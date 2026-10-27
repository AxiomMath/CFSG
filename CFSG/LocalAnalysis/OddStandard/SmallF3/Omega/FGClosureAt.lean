module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClSplit
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClTwoU43
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureFive
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureSix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGSchurU43
public import CFSG.LieType.Universal.Spin.Forms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal.Spin

theorem fg_closureAt_o5 : Asc82ClosureAt ShapeO5 :=
  asc82ClosureAt_of_omegaStar_all (n := 5) (ε := 1)
    (fun _ _ h => isOmegaStar_of_lieModel_psp h)
    (fun _ _ _ _ _ hQ hdim hs => fg_closureFix_five hQ hdim hs)

theorem fg_closureAt_o6p : Asc82ClosureAt ShapeO6P :=
  asc82ClosureAt_of_omegaStar_all (n := 6) (ε := 1)
    (fun _ _ h => isOmegaStar_of_lieModel_psl h)
    (fun _ _ _ _ _ hQ hdim hs => fg_closureFix_six_plus hQ hdim hs)

theorem fg_closureAt_o6m : Asc82ClosureAt ShapeO6M :=
  asc82ClosureAt_of_omegaStar_all (n := 6) (ε := -1)
    (fun _ _ h => isOmegaStar_of_lieModel_psu h)
    (fun _ _ _ _ _ hQ hdim hs => fg_closureFix_six_minus hQ hdim hs)

theorem fg_closureAt_twoU43 (hGA : CFSG.Open.GriessAllModelsStatement) :
    Asc82ClosureAt IsTwoU43 := by
  let Q : QuadraticForm (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) := quadMinus 3 (ZMod 3) 0 1
  have hirr : ∀ s : ZMod 3, s ^ 2 + 0 * s + 1 ≠ 0 := by decide
  have hQ : Q.Nondegenerate := nondegenerate_quadMinus_of_finite 3 (ZMod 3) hirr
  have hdim : Module.finrank (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) = 6 := by simp
  have hs : quadSign Q = -1 :=
    quadSign_quadMinus (m := 3) (b := 0) (c := 1) (by norm_num) hirr
  exact asc82ClosureAt_twoU43 (fg_asc82SchurU43 hGA) hQ hdim hs
    (fg_closureFix_six_minus hQ hdim hs)

end CFSG.OddStandard.SmallF3.Omega
