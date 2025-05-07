#include "return_codes.h"

#include <stdint.h>
#include <stdio.h>

typedef struct
{
	char format;
	char operation;
	uint8_t maxExp;
	uint8_t lenMant;
	uint8_t maxIndex;
	uint8_t lenExp;
	uint8_t round;
} Constants;

typedef struct
{
	uint8_t sign;
	int16_t exp;
	uint32_t mantissa;
} Float32;

void print(uint8_t sign, int16_t exp, uint32_t mantissa, Constants constant)
{
	mantissa <<= constant.format == 'f' ? 9 : 22;
	mantissa >>= constant.format == 'f' ? 8 : 20;
	printf(sign ? "-" : "");
	if (exp >= constant.maxExp)
		printf("inf");
	else
		constant.format == 'f' ? printf("0x1.%06xp%+i", mantissa, exp) : printf("0x1.%03xp%+i", mantissa, exp);
}

char isNan(int16_t exp, uint32_t mantissa, Constants constant)
{
	if (exp == constant.maxExp && (mantissa != 0 && mantissa != (1 << 23) && mantissa != 1024))
	{
		return 1;
	}
	return 0;
}

char isZeroPrint(uint8_t sign, int16_t exp, uint32_t mantissa, Constants constant)
{
	if (exp == -(constant.maxExp - 1) && (mantissa == 0))
	{
		printf(sign ? "-" : "");
		printf("0x0.000");
		constant.format == 'f' ? printf("000p+0") : printf("p+0");
		return 1;
	}
	return 0;
}

char isZero(Float32 *Number, uint32_t mantissa, Constants constant)
{
	if (Number->exp == -(constant.maxExp - 1) && (mantissa == 0))
	{
		Number->mantissa = 0;
		return 1;
	}
	return 0;
}

char isInf(Float32 Number, Constants constant)
{
	if (Number.exp == constant.maxExp && (Number.mantissa == 0 || Number.mantissa == 1024 || Number.mantissa == (1 << 23)))
		return 1;
	return 0;
}

char roundToZero(int16_t *expRes, Constants constant, uint8_t *signRes, uint32_t *mantissaRes)
{
	if (*expRes <= (-(constant.maxExp - 1) - constant.lenMant))
	{
		*expRes = -(constant.maxExp - 1);
		*mantissaRes = 0;
		if (constant.round == 2 && *signRes == 0 || constant.round == 3 && *signRes == 1)
			*expRes = -(constant.maxExp - 2) - constant.lenMant;
		if (isZeroPrint(*signRes, *expRes, *mantissaRes, constant))
			return 1;
	}
	return 0;
}

void parseTerm(uint32_t number, Float32 *num, Constants constant)
{
	number <<= (31 - constant.lenMant - constant.lenExp);
	num->sign = (number >> 31) & 1;
	num->exp = num->sign ? (number >> (31 - constant.lenExp)) - (1 << constant.lenExp) : number >> (31 - constant.lenExp);
	num->exp -= (((1 << constant.lenExp) - 1) >> 1);
	num->mantissa = (number << (constant.lenExp + 1)) >> (constant.lenExp + 1);
	num->mantissa += 1 << (31 - constant.lenExp);
	num->mantissa >>= (31 - constant.lenMant - constant.lenExp);
}

void normalize(int16_t *exp, uint32_t *mantissa, Constants constant)
{
	*mantissa <<= (23 - constant.lenMant);
	if (*exp != -(((1 << constant.lenExp) - 1) >> 1))
	{
		*mantissa >>= (23 - constant.lenMant);
		return;
	}
	for (int8_t i = 22; i >= 0; i--)
	{
		*mantissa = (*mantissa << 9) >> 8;
		if ((*mantissa & (1 << 23)) != 0)
			break;
		*exp -= 1;
	}
	*mantissa >>= (23 - constant.lenMant);
}

void makeRound(int16_t *expRes, uint64_t *mantissaNew, uint8_t signRes, Constants constant, uint8_t count)
{
	// round
	uint8_t index = *expRes > -(constant.maxExp - 1) ? count : (-(constant.maxExp - 1) - *expRes) + count + 1;
	if (constant.round == 1)
	{
		if ((*mantissaNew & ((1ll << index) - 1)) > (1ll << (index - 1)))
			*mantissaNew += (1ll << (index - 1));
		else if ((*mantissaNew & ((1ll << index) - 1)) == (1ll << (index - 1)) && *mantissaNew & (1ll << index))
			*mantissaNew += (1ll << index);
	}
	else if (constant.round != 0)
	{
		if ((*mantissaNew & ((1ll << index) - 1)) > 0 && signRes == (constant.round - 2))
			*mantissaNew += (1ll << (index));
	}
	index = index > 62 ? 63 : index;
	*mantissaNew >>= index;
	*mantissaNew <<= (index - count);

	if ((1ll << (constant.lenMant + 1)) & *mantissaNew)
	{
		*expRes += 1;
		*mantissaNew >>= 1;
	}
}

uint8_t preprocessingAddSub(uint8_t *signRes, Float32 Number, int16_t *expRes, uint32_t *mantissaForNorm, uint8_t *index, int16_t expFirst, uint32_t *mantissa, Constants constant)
{
	*signRes = Number.sign;
	*index = Number.exp - expFirst > 25 ? 26 : Number.exp - expFirst;
	*index = *index > constant.maxIndex ? constant.maxIndex + 1 : *index;
	*mantissaForNorm = *mantissa & ((1 << *index) - 1);
	*mantissa >>= *index;
	*expRes = Number.exp;
	return *mantissaForNorm > 0;
}

void normalizeAddSub(uint32_t *mantissaRes, uint8_t *index, uint32_t *mantissaForNorm, int16_t *expRes, Constants constant, uint8_t isNeed)
{
	if (*mantissaRes & (1 << (constant.maxIndex - 2)))
	{	 // переполнение при сложении
		*mantissaForNorm += *mantissaRes & 1 ? (1 << *index) : 0;
		*mantissaRes >>= 1;
		*expRes += 1;
		*index += 1;
	}
	else if ((*mantissaRes & (1 << (constant.maxIndex - 3))) == 0 && isNeed)
	{	 // недополнение при вычитании
		uint32_t tmp = *mantissaRes;
		for (int8_t i = constant.maxIndex - 3; i >= 0; i--)
		{
			if (tmp & (1 << i))
			{
				break;
			}
			*mantissaRes <<= 1;
			*expRes -= 1;
			*mantissaRes += *mantissaForNorm & (1 << (*index - 1)) ? 1 : 0;
			*mantissaForNorm -= *mantissaForNorm & (1 << (*index - 1)) ? (1 << (*index - 1)) : 0;
			*index -= 1;
		}
	}
}

void makeAddOrSub(Float32 First, Float32 Second, uint8_t *signRes, int16_t *expRes, uint32_t *mantissaRes, Constants constant)
{
	uint8_t temp = 0;
	uint32_t mantissaForNorm = 0;
	uint8_t index = 0;
	if (First.exp < Second.exp)
		temp = preprocessingAddSub(&*signRes, Second, &*expRes, &mantissaForNorm, &index, First.exp, &First.mantissa, constant);
	else if (First.exp > Second.exp)
		temp = preprocessingAddSub(&*signRes, First, &*expRes, &mantissaForNorm, &index, Second.exp, &Second.mantissa, constant);
	else
	{
		*expRes = First.exp;
		*signRes = First.mantissa >= Second.mantissa ? First.sign : Second.sign;
		index = 0;
	}
	if (First.sign == Second.sign)
		*mantissaRes = First.mantissa + Second.mantissa;
	else
	{
		mantissaForNorm = mantissaForNorm ? (1 << index) - mantissaForNorm : 0;
		if (First.exp == Second.exp)
			*mantissaRes = First.mantissa > Second.mantissa ? First.mantissa - Second.mantissa : Second.mantissa - First.mantissa;
		else
			*mantissaRes = First.exp > Second.exp ? First.mantissa - Second.mantissa - temp : Second.mantissa - First.mantissa - temp;
	}
	// norm
	normalizeAddSub(&*mantissaRes, &index, &mantissaForNorm, &*expRes, constant, 1);
	if (First.exp == Second.exp && First.mantissa == Second.mantissa)
	{
		if (constant.operation == '+' && Second.sign != First.sign || (constant.operation == '-' && Second.sign != First.sign))
			*expRes = -(constant.maxExp - 1);
	}
	// round
	if (constant.round == 1 && (mantissaForNorm > (1 << (index - 1)) || ((mantissaForNorm == (1 << (index - 1))) && *mantissaRes & 1)))
		*mantissaRes += 1;
	else if (constant.round != 0 && (mantissaForNorm > 0 && *signRes == (constant.round - 2)))
		*mantissaRes += 1;
	if (constant.round > 1 && *mantissaRes == 0)
		*signRes = (constant.round - 2);
	else if ((constant.round == 0 || constant.round == 1) && *mantissaRes == 0)
		*signRes = 0;
	// norm after round
	normalizeAddSub(&*mantissaRes, &index, &mantissaForNorm, &*expRes, constant, 0);
}

uint8_t makeNone(Float32 First, Float32 Second, Constants constants)
{
	if (isNan(First.exp, First.mantissa, constants) || isNan(Second.exp, Second.mantissa, constants))
		return 1;
	else if (isZero(&First, First.mantissa, constants) && isZero(&Second, Second.mantissa, constants) && constants.operation == '/')
		return 1;
	else if (isInf(First, constants) && isInf(Second, constants))
	{
		if (constants.operation == '/')
			return 1;
		else if (constants.operation == '+' && First.sign != Second.sign)
			return 1;
		else if (constants.operation == '-' && First.sign == Second.sign)
			return 1;
	}
	else if (isZero(&First, First.mantissa, constants) && isInf(Second, constants) && constants.operation == '*')
		return 1;
	else if (isInf(First, constants) && isZero(&Second, Second.mantissa, constants) && constants.operation == '*')
		return 1;
	return 0;
}

uint8_t makeInf(Float32 First, Float32 Second, Constants constants, uint8_t *signRes)
{
	*signRes = (First.sign + Second.sign) & 1;
	if (isZero(&Second, Second.mantissa, constants) && constants.operation == '/')
		return 1;
	else if (isInf(First, constants))
	{
		if (constants.operation != '*' && constants.operation != '/')
			*signRes = First.sign;
		return 1;
	}
	else if (isInf(Second, constants) && constants.operation != '/')
	{
		if (constants.operation == '-')
			Second.sign = ~Second.sign & 1;
		else if (constants.operation == '*')
			Second.sign = (First.sign + Second.sign) & 1;
		*signRes = Second.sign;
		return 1;
	}
	return 0;
}

uint8_t makeZero(Float32 First, Float32 Second, Constants constants, uint8_t *sign)
{
	if (constants.operation == '*' || constants.operation == '/')
	{
		*sign = (First.sign + Second.sign) & 1;
		if (isZero(&First, First.mantissa, constants) || isZero(&Second, Second.mantissa, constants))
			return 1;
		else if (isInf(Second, constants) && constants.operation == '/')
			return 1;
	}
	else if (isZero(&First, First.mantissa, constants) && isZero(&Second, Second.mantissa, constants))
	{
		*sign = 0;
		if ((constants.operation == '+' && First.sign == 1 && Second.sign == 1) ||
			(constants.operation == '-' && First.sign == 1 && Second.sign == 0))
			*sign = 1;
		else if (constants.round == 3 && (constants.operation == '+' && Second.sign != First.sign) ||
				 (constants.operation == '-' && First.sign == Second.sign))
			*sign = 1;
		return 1;
	}
	return 0;
}

uint32_t makeMul(Float32 First, Float32 Second, uint8_t *signRes, int16_t *expRes, Constants constants)
{
	uint64_t mantissaNew = (uint64_t)First.mantissa * Second.mantissa;
	*signRes = (First.sign + Second.sign) & 1;
	*expRes = Second.exp + First.exp;
	uint8_t count = constants.lenMant;
	if (mantissaNew & (1ll << (2 * constants.lenMant + 1)))
	{
		*expRes += 1;
		count += 1;
	}
	makeRound(&*expRes, &mantissaNew, *signRes, constants, count);
	return mantissaNew;
}

uint32_t makeDiv(Float32 First, Float32 Second, uint8_t *signRes, int16_t *expRes, Constants constants)
{
	uint64_t mantissaNew = 0;
	uint32_t remainder = First.mantissa;
	*signRes = (First.sign + Second.sign) & 1;
	*expRes = First.exp - Second.exp;
	// algorithm del
	for (uint8_t i = 0; i < 2 * constants.lenMant + 8; i++)
	{
		mantissaNew <<= 1;
		mantissaNew += remainder / Second.mantissa;
		remainder -= (mantissaNew & 1) * Second.mantissa;
		remainder <<= 1;
	}
	if ((mantissaNew & (1ll << (2 * constants.lenMant + 7))) == 0)
	{
		*expRes -= 1;
		mantissaNew <<= 1;
	}
	makeRound(&*expRes, &mantissaNew, *signRes, constants, constants.lenMant + 7);
	return mantissaNew;
}

char makeOperation(uint32_t numberF, uint32_t numberS, uint8_t *signRes, int16_t *expRes, uint32_t *mantissaRes, Constants constants)
{
	Float32 First, Second;
	parseTerm(numberF, &First, constants);
	parseTerm(numberS, &Second, constants);

	isZero(&First, First.mantissa - (1 << constants.lenMant), constants);
	isZero(&Second, Second.mantissa - (1 << constants.lenMant), constants);
	if (makeNone(First, Second, constants))
	{
		printf("nan");
		return 0;
	}
	if (makeInf(First, Second, constants, &*signRes))
	{
		printf(*signRes ? "-inf" : "inf");
		return 0;
	}
	if (makeZero(First, Second, constants, &*signRes))
	{
		isZeroPrint(*signRes, -(constants.maxExp - 1), 0, constants);
		return 0;
	}

	normalize(&First.exp, &First.mantissa, constants);
	normalize(&Second.exp, &Second.mantissa, constants);

	if (constants.operation == '*')
		*mantissaRes = makeMul(First, Second, &*signRes, &*expRes, constants);
	if (constants.operation == '+')
		makeAddOrSub(First, Second, &*signRes, &*expRes, &*mantissaRes, constants);
	if (constants.operation == '-')
	{
		Second.sign = Second.sign ? 0 : 1;
		makeAddOrSub(First, Second, &*signRes, &*expRes, &*mantissaRes, constants);
	}
	if (constants.operation == '/')
		*mantissaRes = makeDiv(First, Second, &*signRes, &*expRes, constants);
	if (roundToZero(&*expRes, constants, &*signRes, &*mantissaRes))
		return 0;
	if (*mantissaRes == 0 && *expRes != -(constants.maxExp - 2) - constants.lenMant)
		*expRes = -(constants.maxExp - 1);
	if (isZeroPrint(*signRes, *expRes, *mantissaRes, constants))
		return 0;
	return 1;
}

void setConstants(Constants *constants)
{
	if (constants->format == 'f')
	{
		constants->maxExp = 128;
		constants->lenMant = 23;
		constants->maxIndex = 26;
		constants->lenExp = 8;
	}
	else
	{
		constants->maxExp = 16;
		constants->lenMant = 10;
		constants->maxIndex = 13;
		constants->lenExp = 5;
	}
}

uint8_t checkedFormat(Constants constants)
{
	if (constants.format != 'f' && constants.format != 'h')
	{
		perror("Incorrect format\n");
		return 1;
	}
	return 0;
}

uint8_t checkedRound(Constants constants)
{
	if (constants.round < 0 || constants.round > 4)
	{
		perror("Incorrect round\n");
		return 1;
	}
	return 0;
}

uint8_t checkedOperation(Constants constants)
{
	if (constants.operation != '*' && constants.operation != '/' && constants.operation != '+' && constants.operation != '-')
	{
		perror("Incorrect operation");
		return 1;
	}
	return 0;
}

void specialValueInf(uint8_t sign, int16_t *exp, uint32_t *mantissa, Constants constants)
{
	if (*exp >= constants.maxExp)
	{
		if (constants.round == 0 || (constants.round == 2 && sign == 1) || (constants.round == 3 && sign == 0))
		{
			*exp = constants.maxExp - 1;
			*mantissa = (1 << constants.lenMant) - 1;
		}
	}
}

int main(int argc, char *argv[])
{
	if (argc != 4 && argc != 6)
	{
		perror("Usage: fileName <format> <rounding> <number1> [<operation> <number2>]\n");
		return ERROR_ARGUMENTS_INVALID;
	}

	Constants constants;
	Float32 First;
	uint32_t numberF;

	if (!sscanf(argv[1], "%s ", &constants.format) || checkedFormat(constants))
		return ERROR_ARGUMENTS_INVALID;
	if (!sscanf(argv[2], "%hhu", &constants.round) || checkedRound(constants))
		return ERROR_ARGUMENTS_INVALID;

	sscanf(argv[3], "%x ", &numberF);
	setConstants(&constants);

	if (argc == 4)
	{
		parseTerm(numberF, &First, constants);
		if (isZeroPrint(First.sign, First.exp, First.mantissa - (1 << constants.lenMant), constants))
			return 0;
		if (isNan(First.exp, First.mantissa, constants))
		{
			printf("nan");
			return 0;
		}
		normalize(&First.exp, &First.mantissa, constants);
		print(First.sign, First.exp, First.mantissa, constants);
		return 0;
	}

	uint32_t numberS;
	Float32 Result;
	if (!sscanf(argv[4], "%c", &constants.operation) || checkedOperation(constants))
		return ERROR_ARGUMENTS_INVALID;
	sscanf(argv[5], "%x", &numberS);

	uint8_t signRes;
	int16_t expRes;
	uint32_t mantissaRes;

	if (makeOperation(numberF, numberS, &signRes, &expRes, &mantissaRes, constants))
	{
		specialValueInf(signRes, &expRes, &mantissaRes, constants);
		print(signRes, expRes, mantissaRes, constants);
	}
	return 0;
}
