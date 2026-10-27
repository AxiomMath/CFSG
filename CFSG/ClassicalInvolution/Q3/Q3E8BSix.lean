module

public import CFSG.ClassicalInvolution.Q3.Q3E8Facts
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


theorem false_of_three_pairs3 (hD8 : TypeE8.D8NoThreeAdjPairs 3 .POmegaPlus 8 1)
    (hY : YData3 .POmegaPlus 8) [Finite (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K]
    {X : Type} [Group X] (φ : (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K →* X)
    (hker : φ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K)
    (R : Fin 3 → Fin 2 → Subgroup (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K)
    (hfund : ∀ i j, R i j ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D)
    (hadj : ∀ i, ModelAdj (Subgroup.center (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K)
      (R i 0) (R i 1))
    (hstd : ∀ i, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W ((R i 0).map φ)
      ((R i 1).map φ))
    (hcomm : ∀ i i', i ≠ i' → ∀ j j', Commutes (R i j) (R i' j')) : False := by
  refine hD8 R hfund (fun i => ⟨hadj i, ?_⟩) hcomm
  exact exists_lin_of_map3 (not_three_dvd_card_center hY.cop) φ hker (hY.pow3 _ (hfund i 0))
    (hY.pow3 _ (hfund i 1)) (hstd i)

theorem false_of_six3 (hD8 : TypeE8.D8NoThreeAdjPairs 3 .POmegaPlus 8 1)
    (hY : YData3 .POmegaPlus 8) [Finite (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K]
    {X : Type} [Group X] (φ : (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K →* X)
    (hker : φ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K)
    {Ra Rb Rc Rd Re Rf : Subgroup (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K}
    (hfa : Ra ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D)
    (hfb : Rb ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D)
    (hfc : Rc ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D)
    (hfd : Rd ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D)
    (hfe : Re ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D)
    (hff : Rf ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D)
    (hab : ModelAdj (Subgroup.center (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K) Ra Rb)
    (hcd : ModelAdj (Subgroup.center (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K) Rc Rd)
    (hef : ModelAdj (Subgroup.center (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K) Re Rf)
    (sab : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (Ra.map φ) (Rb.map φ))
    (scd : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (Rc.map φ) (Rd.map φ))
    (sef : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (Re.map φ) (Rf.map φ))
    (hac : Commutes Ra Rc) (had : Commutes Ra Rd) (hbc : Commutes Rb Rc) (hbd : Commutes Rb Rd)
    (hae : Commutes Ra Re) (haf : Commutes Ra Rf) (hbe : Commutes Rb Re) (hbf : Commutes Rb Rf)
    (hce : Commutes Rc Re) (hcf : Commutes Rc Rf) (hde : Commutes Rd Re) (hdf : Commutes Rd Rf) :
    False := by
  refine false_of_three_pairs3 hD8 hY φ hker ![![Ra, Rb], ![Rc, Rd], ![Re, Rf]] ?_ ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> assumption
  · intro i
    fin_cases i
    · exact hab
    · exact hcd
    · exact hef
  · intro i
    fin_cases i
    · exact sab
    · exact scd
    · exact sef
  · intro i i' hii' j j'
    fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
      first
      | exact absurd rfl hii'
      | assumption
      | exact commutes_symm ‹_›

end CFSG.ClassicalInvolution.Q3.Q3W
