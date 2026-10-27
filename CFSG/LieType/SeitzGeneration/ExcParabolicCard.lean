module

public import CFSG.Timmesfeld.Orders.ExceptionalWeyl

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders

variable {τ : Tag}

section Sums

variable [Fintype (WeylGroup τ)]

theorem finsum_parabolicWeylGroup_eq (J : Set (Fin τ.rank)) (q : ℕ) :
    ∑ᶠ w : parabolicWeylGroup τ J, q ^ (coxeterSystem τ).length w = parabolicSum τ J q := by
  classical
  rw [finsum_eq_sum_of_fintype, parabolicSum]
  refine (Finset.sum_subtype _ (fun w => ?_) (fun w => q ^ (coxeterSystem τ).length w)).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, parabolic_eq_parabolicWeylGroup]

theorem parabolicSum_pos (J : Set (Fin τ.rank)) {q : ℕ} (hq : 0 < q) :
    0 < parabolicSum τ J q := by
  classical
  unfold parabolicSum
  exact Finset.sum_pos (fun w _ => pow_pos hq _) ⟨1, by simp⟩

end Sums

section Index

variable {K : Type} [Field K] [Finite K] [Fintype (WeylGroup τ)]

theorem parabolicSum_univ_eq_mul_index (J : Set (Fin τ.rank)) :
    parabolicSum τ Set.univ (Nat.card K) = parabolicSum τ J (Nat.card K) *
      (parabolicSubgroup τ K J).relIndex (adjointGroup τ K) := by
  classical
  have hP := (standard_parabolic_cells τ K).2.2.2.2.2.2 J
  have hA := card_adjointGroup (τ := τ) (K := K)
  have hle := parabolicSubgroup_le_adjointGroup τ K J
  have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  have h2 := Subgroup.relIndex_mul_card (H := parabolicSubgroup τ K J) (K := adjointGroup τ K)
  rw [inf_of_le_left hle, hP, hA, finsum_parabolicWeylGroup_eq, finsum_eq_sum_of_fintype] at h2
  have hpos : 0 < Nat.card (torusGroup τ K) * Nat.card K ^
      {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard :=
    Nat.mul_pos Nat.card_pos (pow_pos Nat.card_pos _)
  rw [parabolicSum_univ]
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← h2]
  ring

end Index

end CFSG.LieType.SeitzGeneration
