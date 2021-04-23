module aftermath;

private
{
    import std.algorithm;
    import std.bigint;
    import std.conv;
    import std.math;
    import std.stdio;
    import std.string;
    import std.typecons;

    // template for adding setter/getter
    template addProperty(T, string propertyName, string defaultValue = T.init.to!string)
    {
        const char[] addProperty = format(`
			private %2$s %1$s = %4$s;
	 
			void set%3$s(%2$s %1$s)
			{
				this.%1$s = %1$s;
			}
	 
			%2$s get%3$s()
			{
				return %1$s;
			}
			`, "_" ~ propertyName.toLower, T.stringof, propertyName, defaultValue);
    }

    auto twoComplement(T)(T n, T bits)
    {
        return ((cast(T) 1 << bits) - n) % (cast(T) 1 << bits);
    }

    auto oneComplement(T)(T n, T bits)
    {
        return (cast(T) 1 << bits) - n - cast(T) 1;
    }

    auto countBits(T)(T n)
    {
        T count;
        if (n == 0)
        {
            count++;
        }
        else
        {
            while (n != 0)
            {
                n >>= 1;
                count++;
            }
        }
        return count;
    }

    auto setBit(T)(T n, T i)
    {
        return n | (cast(T) 1 << i);
    }

    auto getBit(T)(T n, T i)
    {
        return (n >> i) & cast(T) 1;
    }

    auto toggleBit(T)(T n, T i)
    {
        return n ^ (cast(T) 1 << i);
    }

    auto unsetBit(T)(T n, T i)
    {
        return (n | (cast(T) 1 << i)) ^ (cast(T) 1 << i);
    }

    auto createMask(T)(T n, T k)
    {
        return ((cast(T) 1 << n) - cast(T) 1) << k;
    }

    auto extractBitField(T)(T x, T n, T k)
    {
        return (x & createMask(n, k)) >> k;
    }

    auto lastSettedBit(T)(T n)
    {
        return countBits(n) - cast(T) 1;
    }

    auto lastUnsettedBit(T)(T n)
    {
        return lastSettedBit(oneComplement(n, countBits(n)));
    }

    auto countTrailingZeroes(T)(T n)
    {
        if (n == 0)
        {
            return 0;
        }
        else
        {
            return countBits(n & (-n)) - cast(T) 1;
        }
    }

    auto removeTrailingZeroes(T)(T n)
    {
        if (n == 0)
        {
            return 0;
        }
        else
        {
            return n >> countTrailingZeroes(n);
        }
    }

    auto ceilLog2(T)(T n)
    {
        T x = lastSettedBit(n);
        return x + cast(T)(n != (cast(T) 1 << x));
    }

    auto floorLog2(T)(T n)
    {
        return countBits(n) - cast(T) 1;
    }

    auto nextPowerOfTwo(T)(T n)
    {
        return cast(T) 1 << ceilLog2(n);
    }

    auto alignValues(T, S)(T a, S b)
    {
        auto lengthA = countBits(a);
        auto lengthB = countBits(b);

        if (lengthA > lengthB)
        {
            b <<= (lengthA - lengthB);
        }
        else
        {
            if (lengthA < lengthB)
            {
                a <<= lengthB - lengthA;
            }
        }

        auto trailingA = countTrailingZeroes(a);
        auto trailingB = countTrailingZeroes(b);

        a >>= min(trailingA, trailingB);
        b >>= min(trailingA, trailingB);

        return tuple(a, b);
    }

    // internals of double
    class DoubleComponents
    {
        mixin(addProperty!(long, "Value"));
        mixin(addProperty!(long, "Sign"));
        mixin(addProperty!(long, "Exponent"));
        mixin(addProperty!(long, "Fraction"));

        this()
        {

        }

        // extract data from double
        auto fromDouble(double number)
        {
            // bitwise conversion to ulong
            _value = *(cast(ulong*)&number);
            // sign extraction
            _sign = _value >> 63;
            // exponent extraction
            _exponent = ((_value & ((1UL << 63) - 1)) >> 52) - 1023;
            // fraction extraction
            _fraction = (1UL << 52) | (_value & ((1UL << 52) - 1));
        }
    }

    // representation of internal posit structure
    class PositComponents
    {
        // 0 or 1 in begin of regime
        mixin(addProperty!(long, "RegimeSign"));
        // sign bit
        mixin(addProperty!(long, "Sign"));
        // regime
        mixin(addProperty!(long, "Regime"));
        // exponent
        mixin(addProperty!(long, "Exponent"));
        // fraction
        mixin(addProperty!(long, "Fraction"));
        // regime length
        mixin(addProperty!(long, "RegimeLength"));
        // exponent length
        mixin(addProperty!(long, "ExponentLength"));
        // fraction length
        mixin(addProperty!(long, "FractionLength"));

        this()
        {

        }

        // extract component from long value (value is bit pattern)
        auto fromLong(long numberOfBits, long exponentSize)(long number)
        {
            long _number = number;
            _sign = getBit(_number, numberOfBits - 1);

            if (_sign == 1)
            {
                _number = twoComplement(_number, numberOfBits);
            }

            _regimesign = getBit(_number, numberOfBits - 2);

            if (_regimesign == 0)
            {
                _regimelength = numberOfBits - lastSettedBit(_number) - 1;
            }
            else
            {
                _regimelength = numberOfBits - lastUnsettedBit(_number) - 1;
            }

            _exponentlength = max(0, min(exponentSize, numberOfBits - 1 - _regimelength));
            _fractionlength = max(0, numberOfBits - 1 - _regimelength - _exponentlength);

            if (_regimesign == 0)
            {
                _regime = -_regimelength + 1;
            }
            else
            {
                _regime = _regimelength - 2;
            }

            _exponent = extractBitField(_number, _exponentlength, _fractionlength) << (
                    exponentSize - _exponentlength);
            _fraction = removeTrailingZeroes(setBit(extractBitField(_number,
                    _fractionlength, 0), _fractionlength));
        }
    }

    // posit container
    template PositContainer(uint size)
    {
        static if (size == 8)
            alias PositContainer = ubyte;
        else static if (size == 16)
            alias PositContainer = ushort;
        else static if (size == 32)
            alias PositContainer = uint;
        else static if (size == 64)
            alias PositContainer = ulong;
        else
            static assert(0);
    }

    class Posit(uint numberOfBits, uint exponentSize)
    {
        private
        {
            // type for internal's of posit
            alias Unum = PositContainer!numberOfBits;
            // internal representation of posit
            mixin(addProperty!(Unum, "Unum"));
            // size of posit in bit
            enum NBITS = numberOfBits;
            // maximal size of exponent in bit
            enum ES = exponentSize;
            // useed
            enum USEED = 2 ^^ (2 ^^ ES);
            // minimal *positive* value (bit pattern)
            enum MINPOS = 1;
            // maximal *positive* value (bit pattern)
            enum MAXPOS = (2 ^^ (NBITS - 1)) - 1;
            // NaR (not a real) pattern
            enum NOT_A_REAL = 2 ^^ (NBITS - 1);
            // zero pattern
            enum ZERO = 0;
            // number of patterns
            enum NPAT = 2 ^^ NBITS;

            PositComponents components = new PositComponents;
        }

        this()
        {

        }

        // construct posit from his elements: (sign, scale, fraction)
        auto construct(T)(T sign, T scale, T fraction)
        {
            Posit!(NBITS, ES) posit = new Posit!(NBITS, ES);

            if (fraction == 0)
            {
                return posit;
            }

            long n = 0;
            long regime = scale >> ES;
            long exponent = scale & createMask(ES, 0);

            long regimeLength;

            if (regime >= 0)
            {
                regimeLength = regime + 2;
            }
            else
            {
                regimeLength = -regime + 1;
            }

            if (regimeLength >= (NBITS + 1))
            {
                if (regime >= 0)
                {
                    posit.fromBits(MAXPOS);
                }
                else
                {
                    posit.fromBits(MINPOS);
                }

                if (sign == 1)
                {
                    auto unum = posit.getUnum;
                    posit.fromBits(twoComplement(_unum.to!long, NBITS).to!Unum);
                }

                return posit;
            }

            if (regime >= 0)
            {
                n |= createMask(regimeLength - 1, NBITS - regimeLength);
            }
            else
            {
                if (NBITS - 1 >= regimeLength)
                {
                    n |= setBit(n, NBITS - 1 - regimeLength);
                }
            }

            long exponentBits = min(ES, NBITS - 1 - regimeLength);
            long fractionBits = NBITS - 1 - regimeLength - exponentBits;

            fraction = removeTrailingZeroes(fraction);
            long fractionLength = countBits(fraction) - 1;
            fraction &= 2 ^^ (countBits(fraction) - 1) - 1;

            long trailingBits = NBITS - 1 - regimeLength;
            long expFrac = removeTrailingZeroes(exponent << (fractionLength) | fraction);

            long expFracBits;

            if (fractionLength == 0)
            {
                expFracBits = ES - countTrailingZeroes(exponent);
            }
            else
            {
                expFracBits = ES + fractionLength;
            }

            if (trailingBits < expFracBits)
            {
                long mask = expFrac & createMask(expFracBits - trailingBits, 0);
                long overflown = expFrac & mask;
                n |= expFrac >> (expFracBits - trailingBits);
                auto overflowMask = (1L << (expFracBits - trailingBits - 1L));

                if (overflown == overflowMask)
                {
                    if (getBit(expFrac, expFracBits - trailingBits) == 1)
                    {
                        n += 1;
                    }
                }
                else
                {
                    if (overflown > overflowMask)
                    {
                        n += 1;
                    }
                    else
                    {
                        // for another way actions don't needed
                    }
                }
            }
            else
            {
                n |= expFrac << (trailingBits - expFracBits);
            }

            if (sign == 0)
            {
                posit.fromBits(n);
            }
            else
            {
                posit.fromBits(twoComplement(n.to!long, NBITS));
            }

            return posit;
        }

        // decoding components of posit
        PositComponents decode() @property
        {
            components.fromLong!(NBITS, ES)(_unum);
            return components;
        }

        // set from bit pattern
        auto fromBits(T)(T bitPattern)
        {
            this.setUnum(bitPattern.to!Unum);
            decode;
        }

        // set from double
        auto fromDouble(double x)
        {
            if (x == 0.0)
            {
                _unum = ZERO;
            }
            else
            {
                if (x.isNaN || x.isInfinity)
                {
                    _unum = NOT_A_REAL;
                }
                else
                {
                    DoubleComponents dc = new DoubleComponents;
                    dc.fromDouble(x);

                    _unum = construct(dc.getSign, dc.getExponent, dc.getFraction).getUnum;
                    decode;
                }
            }
        }

        // set from integer
        auto fromInteger(int x)
        {
            if (x == 0)
            {
                _unum = ZERO;
            }
            else
            {
                auto sign = (x >= 0) ? 0 : 1;
                if (sign == 1)
                {
                    x = abs(x);
                }
                auto exponent = countBits(x) - 1;
                auto fraction = x;
                _unum = construct(sign, exponent, fraction).getUnum;
                decode;
            }
        }

        // is maximal value of posit ?
        bool isMax() @property
        {
            return (_unum == MAXPOS);
        }

        // is minimal value of posit ?
        bool isMin() @property
        {
            return (_unum == MINPOS);
        }

        // is a +/- infinity ?
        bool isNaR() @property
        {
            return (_unum == NOT_A_REAL);
        }

        // is valid posit ?
        bool isValid() @property
        {
            return ((0 <= _unum) && (_unum < NPAT));
        }

        // is a posit zero ?
        bool isZero() @property
        {
            return (_unum == ZERO);
        }

        // addition
        auto opBinary(string op)(Posit!(NBITS, ES) rhs) if (op == "+")
        {
            if (_unum == 0)
            {
                return rhs;
            }

            if (rhs.isZero)
            {
                return this;
            }
            else
            {
                if ((rhs.isNaR) || (_unum == NOT_A_REAL))
                {
                    return rhs;
                }
            }

            PositComponents components2 = new PositComponents;
            decode;
            components2.fromLong!(NBITS, ES)(rhs.getUnum);

            auto fractions = alignValues(components.getFraction, components2.getFraction);
            long fraction1 = fractions[0];
            long fraction2 = fractions[1];
            long scale1 = 2 ^^ ES * components.getRegime + components.getExponent;
            long scale2 = 2 ^^ ES * components2.getRegime + components2.getExponent;
            long scale = max(scale1, scale2);

            long estimatedLength;

            if (scale1 > scale2)
            {
                fraction1 <<= scale1 - scale2;
                estimatedLength = countBits(fraction1);
            }
            else
            {
                fraction2 <<= scale2 - scale1;
                estimatedLength = countBits(fraction2);
            }

            long fraction = ((-1) ^^ components.getSign * fraction1) + (
                    (-1) ^^ components2.getSign * fraction2);
            long sign = (fraction < 0) ? 1 : 0;
            fraction = abs(fraction);

            long resultLength = countBits(fraction);
            scale += resultLength - estimatedLength;
            fraction = removeTrailingZeroes(fraction);

            return construct(sign, scale, fraction);
        }

        // subtraction
        auto opBinary(string op)(Posit!(NBITS, ES) rhs) if (op == "-")
        {
            return (this + (-rhs));
        }

        // conversion to int
        int opCast(T : int)()
        {
            if (_unum == 0)
            {
                return 0;
            }
            else
            {
                if (_unum == NOT_A_REAL)
                {
                    return T.max;
                }
                else
                {
                    return (cast(double) this).to!int;
                }
            }
        }

        // conversion to double
        double opCast(T : double)()
        {
            if (_unum == 0)
            {
                return 0.0;
            }
            else
            {
                if (_unum == NOT_A_REAL)
                {
                    return double.nan;
                }
                else
                {
                    decode;
                    double fraction = components.getFraction;
                    double n = countBits(components.getFraction) - 1;
                    return ((-1.0) ^^ components.getSign * 2.0 ^^ (
                            2.0 ^^ ES * components.getRegime + components.getExponent - n)
                            * fraction);
                }
            }
        }

        // multiplication
        auto opBinary(string op)(Posit!(NBITS, ES) rhs) if (op == "*")
        {
            if (this.isZero || this.isNaR)
            {
                return this;
            }
            else
            {
                if (rhs.isZero || rhs.isNaR)
                {
                    return rhs;
                }
            }

            PositComponents components2 = new PositComponents;
            decode;
            components2.fromLong!(NBITS, ES)(rhs.getUnum);

            long sign = components.getSign ^ components2.getSign;

            long scale = (2 ^^ ES * (
                    components.getRegime + components2.getRegime)
                    + components.getExponent + components2.getExponent);
            long fraction = components.getFraction * components2.getFraction;

            long fa = floorLog2(components.getFraction);
            long fb = floorLog2(components2.getFraction);
            long fc = floorLog2(fraction);

            scale += fc - fa - fb;

            return construct(sign, scale, fraction);
        }

        // division
        auto opBinary(string op)(Posit!(NBITS, ES) rhs) if (op == "/")
        {
            if (this.isZero || this.isNaR)
            {
                return this;
            }
            else
            {
                if (rhs.isZero || rhs.isNaR)
                {
                    return rhs;
                }
            }

            PositComponents components2 = new PositComponents;
            decode;
            components2.fromLong!(NBITS, ES)(rhs.getUnum);

            long fraction1 = components.getFraction;

            if ((fraction1 & (fraction1 - 1)) == 0)
            {
                return this * rhs.reciprocal;
            }
            else
            {
                long sign = components.getSign ^ components2.getSign;
                long scale = (2 ^^ ES * (
                        components.getRegime - components2.getRegime)
                        + components.getExponent - components2.getExponent);
                long fraction2 = components2.getFraction;
                auto fractions = alignValues(fraction1, fraction2);
                import std.bigint;

                auto n = BigInt(fractions[0].to!string);
                fraction2 = fractions[1];
                long fa = floorLog2(n << (NBITS * 4)).to!long;
                long fb = floorLog2(fraction2);
                auto fraction = (n << (NBITS * 4) / fraction2).to!long;
                long fc = floorLog2(fraction);

                scale -= fa - fb - fc;

                return construct(sign, scale, fraction);
            }
        }

        override int opCmp(Object o)
        {
            int result;
            if (typeid(o) == typeid(Posit!(NBITS, ES)))
            {
                auto a = this.toSignedInteger;
                auto b = (cast(Posit!(NBITS, ES)) o).toSignedInteger;

                if (a > b)
                {
                    result = 1;
                }
                else
                {
                    if (a < b)
                    {
                        result = -1;
                    }
                    else
                    {
                        result = 0;
                    }
                }
            }
            return result;
        }

        // unary minus
        auto opUnary(string op)() if (op == "-")
        {
            Posit!(NBITS, ES) posit = new Posit!(NBITS, ES);
            posit.fromBits(twoComplement(_unum.to!ulong, NBITS));
            return posit;
        }

        // reciprocal
        auto reciprocal()
        {
            Posit!(NBITS, ES) posit = new Posit!(NBITS, ES);
            long bits = unsetBit(twoComplement(_unum.to!long, NBITS), NBITS - 1);
            posit.fromBits(bits);

            return posit;
        }

        version (linux)
        {
            // nice binary representation with color
            string toBinaryFormatted()
            {
                // for sign format (sign is string) (red colored)
                enum SIGN_FORMAT = "\u001b[41m\u001b[97m\u001b[1m%s\u001b[0m";
                // for regime format (regime is string) (yellow colored)
                enum REGIME_FORMAT = "\u001b[43m\u001b[97m\u001b[1m%s\u001b[0m";
                // for exponent format (exponent is string) (blue colored)
                enum EXPONENT_FORMAT = "\u001b[44m\u001b[97m\u001b[1m%s\u001b[0m";
                // for fraction format (fraction is string) (black colored)
                enum FRACTION_FORMAT = "\u001b[40m\u001b[97m\u001b[1m%s\u001b[0m";

                // fill the data structure with current data from posit
                decode;
                string formattedData;

                // binary string from number
                auto rawData = ("%0." ~ NBITS.to!string ~ "b").format(_unum);

                // rawData[0] - first digit of binary representation, i.e sign of posit
                formattedData ~= SIGN_FORMAT.format(rawData[0].to!string);
                // position of posits components in unsigned his representation
                auto position = 1 + components.getRegimeLength;
                // regime started at second position
                formattedData ~= REGIME_FORMAT.format(rawData[1 .. position]);

                // if exponent exists
                if (components.getExponentLength != 0)
                {
                    formattedData ~= EXPONENT_FORMAT.format(
                            rawData[position .. position + components.getExponentLength]);
                    position += components.getExponentLength;
                }

                // if fraction exists
                if (components.getFractionLength != 0)
                {
                    formattedData ~= FRACTION_FORMAT.format(rawData[position .. $]);
                }

                return formattedData;
            }
        }

        // to signed integer
        auto toSignedInteger()
        {
            template SignedType(T)
            {
                static if (is(T == ubyte))
                    alias SignedType = byte;
                else static if (is(T == ushort))
                    alias SignedType = short;
                else static if (is(T == uint))
                    alias SignedType = int;
                else static if (is(T == ulong))
                    alias SignedType = long;
                else
                    static assert(0);
            }

            alias SignedUnum = SignedType!Unum;

            SignedUnum unum = cast(SignedUnum) _unum;

            return unum;
        }

        // to unsigned integer
        auto toUnsignedInteger()
        {
            return _unum;
        }

        // string representation
        override string toString()
        {
            enum string positFormat = `Posit{%d, %d}(0x%0.` ~ to!string(NBITS >> 2) ~ `x)[%0.32f]`;

            return positFormat.format(NBITS, ES, _unum, cast(double) this);
        }

        alias components this;
    }
}

alias Posit8 = Posit!(8, 0);
alias Posit16 = Posit!(16, 1);
alias Posit32 = Posit!(32, 2);
alias SoftFloat = Posit!(8, 2);
