module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutElems
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsCount

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

variable {L : Type} [Group L]

theorem l33_card_L (hL : LieModel L .PSL 3 3 1) :
    Nat.card L = 5616 := by
  obtain ⟨e⟩ := equiv_of_lieModel hL
  rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]

theorem l33_card_mulAut (hL : LieModel L .PSL 3 3 1) :
    Nat.card (MulAut L) = 11232 := by
  obtain ⟨e⟩ := equiv_of_lieModel hL
  exact card_mulAut e

theorem l33_conj_injective (hL : LieModel L .PSL 3 3 1) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  intro a b hab
  obtain ⟨M, hM⟩ := exists_isL33Model hL
  have h1 : (M.e a : Equiv.Perm (Fin 26)) = (M.e b : Equiv.Perm (Fin 26)) := by
    rw [← hM.ι_conj a, ← hM.ι_conj b, hab]
  exact M.e.injective (Subtype.ext h1)

theorem l33_index_inner (hL : LieModel L .PSL 3 3 1) :
    (MulAut.conj : L →* MulAut L).range.index = 2 := by
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := l33_conj_injective hL
  have hcard : Nat.card (MulAut.conj : L →* MulAut L).range = Nat.card L :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h := Subgroup.card_mul_index ((MulAut.conj : L →* MulAut L).range)
  rw [hcard, l33_card_L hL, l33_card_mulAut hL] at h
  omega

theorem l33_card_involutions
    (hL : LieModel L .PSL 3 3 1) :
    Nat.card {u : L // u ^ 2 = 1 ∧ u ≠ 1} = 117 := by
  obtain ⟨e⟩ := equiv_of_lieModel hL
  have hiff : ∀ u : L, (u ^ 2 = 1 ∧ u ≠ 1) ↔
      (((e u : QP.originalSubgroup) : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧
        ((e u : QP.originalSubgroup) : Equiv.Perm (Fin 26)) ≠ 1) := by
    intro u
    have hsq : ((e u : QP.originalSubgroup) : Equiv.Perm (Fin 26)) ^ 2 = 1 ↔ u ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, OneMemClass.coe_eq_one, ← map_pow, MulEquiv.map_eq_one_iff e]
    have hone : ((e u : QP.originalSubgroup) : Equiv.Perm (Fin 26)) ≠ 1 ↔ u ≠ 1 :=
      not_congr (by rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff e])
    exact hsq.symm.and hone.symm
  have key : Nat.card {u : L // u ^ 2 = 1 ∧ u ≠ 1} =
      Nat.card {g : QP.originalSubgroup // (g : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧
        (g : Equiv.Perm (Fin 26)) ≠ 1} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv hiff)
  rw [key]
  exact card_model_inner_involutions

theorem l33_card_outer_involutions
    (hL : LieModel L .PSL 3 3 1) :
    Nat.card {φ : MulAut L // φ ^ 2 = 1 ∧ ¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹} = 234 := by
  obtain ⟨M, h⟩ := exists_isL33Model hL
  let F : {φ : MulAut L // φ ^ 2 = 1 ∧ ¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹} →
      {g : QA.originalSubgroup // (g : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧
        (g : Equiv.Perm (Fin 26)) ∉ QP.originalSubgroup} := fun φ => by
    refine ⟨⟨M.ι φ.1, h.A_eq ▸ M.ι_mem φ.1⟩, ?_⟩
    change (M.ι φ.1 : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧ M.ι φ.1 ∉ QP.originalSubgroup
    exact ⟨by rw [← map_pow, φ.2.1, map_one],
      fun hmem => φ.2.2 (M.inner_of_mem φ.1 (by rwa [← h.P_eq] at hmem))⟩
  let G : {g : QA.originalSubgroup // (g : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧
        (g : Equiv.Perm (Fin 26)) ∉ QP.originalSubgroup} →
      {φ : MulAut L // φ ^ 2 = 1 ∧ ¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹} := fun g => by
    refine ⟨liftA M (g.1 : Equiv.Perm (Fin 26)) (h.A_eq.symm ▸ g.1.property), ?_, ?_⟩
    · apply M.ι_injective
      rw [map_pow, ι_liftA, g.2.1, map_one]
    · intro hinner
      have hmem : (g.1 : Equiv.Perm (Fin 26)) ∈ M.P :=
        (liftA_inner_iff M h.P_le_A (h.A_eq.symm ▸ g.1.property)).1 hinner
      exact g.2.2 (by rwa [h.P_eq] at hmem)
  let e : {φ : MulAut L // φ ^ 2 = 1 ∧ ¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹} ≃
      {g : QA.originalSubgroup // (g : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧
        (g : Equiv.Perm (Fin 26)) ∉ QP.originalSubgroup} :=
    { toFun := F
      invFun := G
      left_inv := fun φ => Subtype.ext (liftA_ι M φ.1)
      right_inv := fun g => Subtype.ext (Subtype.ext (ι_liftA M (g.1 : Equiv.Perm (Fin 26))
        (h.A_eq.symm ▸ g.1.property))) }
  rw [Nat.card_congr e]
  exact card_model_outer_involutions

end CFSG.OddStandard.SmallF3.L33
