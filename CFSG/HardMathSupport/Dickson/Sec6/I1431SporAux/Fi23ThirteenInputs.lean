module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23ThirteenNative

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

set_option compiler.extract_closed false

@[expose] def fi23ThirteenOK (O : WOrbit) : Bool :=
  let T₀ := eTab O
  let T₁ := starWordTab O (dTable O) (genTables O (-2)) (fivePathOf O)
  (List.range 5).all fun a => (List.range 5).all fun b =>
    a + b == 0 || (fixList (fiveTab T₀ T₁ a b)).length % 13 != 0

end CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23ThirteenNative
