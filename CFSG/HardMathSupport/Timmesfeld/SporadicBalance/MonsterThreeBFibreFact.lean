module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBLocal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Monster.Generated
open _root_.Timmesfeld.M3B (fT fLam fpt unpack nPts fRootV repD)


@[expose] def FibreRoots (k : ℕ) : Prop :=
  ∀ p < nPts, ∀ x : Gmat, IsAct tbSys x (toD (fpt (fT k) (fLam k) (unpack p))) →
    ∃ g ∈ tbL, ∃ v ∈ fRootV k, IsAct tbSys (g⁻¹ * x * g) (toD (repD k v))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

end
