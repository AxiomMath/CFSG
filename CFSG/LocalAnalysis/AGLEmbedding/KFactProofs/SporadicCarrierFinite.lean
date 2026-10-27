module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint

instance finite_carrier_J2 : Finite (NativeSporadic.Carrier .J2) :=
  inferInstanceAs (Finite NativeSporadic.J2)

instance finite_carrier_J3 : Finite (NativeSporadic.Carrier .J3) :=
  inferInstanceAs (Finite NativeSporadic.J3)

instance finite_carrier_McL : Finite (NativeSporadic.Carrier .McL) :=
  inferInstanceAs (Finite NativeSporadic.McL)

instance finite_carrier_Co2 : Finite (NativeSporadic.Carrier .Co2) :=
  inferInstanceAs (Finite NativeSporadic.Co2)

instance finite_carrier_Co3 : Finite (NativeSporadic.Carrier .Co3) :=
  inferInstanceAs (Finite NativeSporadic.Co3)

instance finite_carrier_He : Finite (NativeSporadic.Carrier .He) :=
  inferInstanceAs (Finite NativeSporadic.He)

instance finite_carrier_Ru : Finite (NativeSporadic.Carrier .Ru) :=
  inferInstanceAs (Finite NativeSporadic.Ru)

instance finite_carrier_HS : Finite (NativeSporadic.Carrier .HS) :=
  inferInstanceAs (Finite NativeSporadic.HS)

end CFSG.AGLEmbedding
