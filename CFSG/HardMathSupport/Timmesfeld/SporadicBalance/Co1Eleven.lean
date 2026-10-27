module

public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.Co1Block.PermData
public import Certificates.Certificate16954
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Th.GroupTheory

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Eleven

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Fi23.Native

theorem card_centralizer_Co1_eleven
    (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) ≤ 66 ∧
      3 ∣ Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) :=
  Certificates.certificate16954 x hx

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Eleven
