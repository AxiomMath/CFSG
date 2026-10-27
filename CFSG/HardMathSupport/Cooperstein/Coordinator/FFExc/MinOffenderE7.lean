module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinOffender
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinSylow7

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem posU7_eq : posU7 K = posUnip e7Data_valid K := by
  unfold posU7 posUnip
  simp only [one_mul]

theorem e7_56_pair_bound_all (A : Subgroup (e7Data_valid.minGroup K)) (hA : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card (fixedSub (hV := e7Data_valid) (k := K) A) ≤ Nat.card K ^ 45 ∧
      Nat.card A ^ 2 * Nat.card (fixedSub (hV := e7Data_valid) (k := K) A) ≤ Nat.card K ^ 55 := by
  have := finite_minGroup7 K
  exact bound_of_conj e7Data_valid K (posU7 K)
    (fun B hB => e7_conj_into_posU7 K B (isPGroup_of_sq B hB)) 45 55
    (fun B hBU hBne hBel => e7_56_pair_bound K (A := B) (by rwa [← posU7_eq K])
      (comm_of_exp_two hBel) hBne) A hA hel

theorem e7_56_no_offender (A : Subgroup (e7Data_valid.minGroup K)) (hA : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card (fixedSub (hV := e7Data_valid) (k := K) A) < Nat.card K ^ 56 ∧
      4 * (Nat.card A ^ 2 * Nat.card (fixedSub (hV := e7Data_valid) (k := K) A)) <
        Nat.card K ^ 112 := by
  obtain ⟨h1, h2⟩ := e7_56_pair_bound_all K A hA hel
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  exact lt_of_bounds hq h1 h2 (by norm_num) (by norm_num)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
