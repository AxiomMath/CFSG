module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Pointwise

private theorem commutator_sup_le_of_commutative_of_le_normalizer {G : Type*} [Group G]
    {T N : Subgroup G} (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : ⁅T ⊔ N, T ⊔ N⁆ ≤ N := by
  have hconj : ∀ s ∈ T, ∀ m ∈ N, s * m * s⁻¹ ∈ N := fun s hs m hm =>
    (Subgroup.mem_normalizer_iff.1 (hTN hs) m).1 hm
  have hmul : ∀ x ∈ T ⊔ N, ∃ t ∈ T, ∃ n ∈ N, x = t * n := by
    intro x hx
    have hx' : x ∈ (T : Set G) * (N : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T N hTN]
      exact hx
    obtain ⟨t, ht, n, hn, rfl⟩ := hx'
    exact ⟨t, ht, n, hn, rfl⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨t, ht, n, hn, rfl⟩ := hmul x hx
  obtain ⟨t', ht', n', hn', rfl⟩ := hmul y hy
  have hn₁ : t'⁻¹ * n * t' ∈ N := by simpa using hconj t'⁻¹ (inv_mem ht') n hn
  have hn₂ : t' * n'⁻¹ * t'⁻¹ ∈ N := hconj t' ht' _ (inv_mem hn')
  have hinv : (t * t')⁻¹ = t⁻¹ * t'⁻¹ := by rw [hT t ht t' ht', mul_inv_rev]
  have key : ⁅t * n, t' * n'⁆ =
      ((t * t') * ((t'⁻¹ * n * t') * n' * n⁻¹) * (t * t')⁻¹) * (t' * n'⁻¹ * t'⁻¹) := by
    rw [commutatorElement_def, hinv]
    group
  rw [key]
  exact mul_mem (hconj _ (mul_mem ht ht') _ (mul_mem (mul_mem hn₁ hn') (inv_mem hn))) hn₂

section Levi

variable {τ : Tag} {K : Type} [Field K]

private theorem torusGroup_mul_comm {g h : ModGL τ K} (hg : g ∈ torusGroup τ K)
    (hh : h ∈ torusGroup τ K) : g * h = h * g := by
  have key : torusGroup τ K ≤ Subgroup.centralizer (torusGroup τ K : Set (ModGL τ K)) := by
    rw [torusGroup, Subgroup.centralizer_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨j, u⟩, rfl⟩
    exact torusElt_mul_comm j i u t
  exact Subgroup.mem_centralizer_iff.1 (key hh) g hg

private theorem subsystemGroup_eq_rootSpan (A : Set (Fin τ.rank)) :
    subsystemGroup τ K A =
      rootSpan τ K {α | ∃ j ∈ A, α = Pi.single j 1 ∨ α = -Pi.single j 1} := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) (iSup₂_le fun α hα => ?_)
  · rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan
        (S := {α | ∃ j ∈ A, α = Pi.single j 1 ∨ α = -Pi.single j 1}) ⟨j, hj, Or.inl rfl⟩ c
    · rw [← pinnedX_neg_single]
      exact pinnedX_mem_rootSpan
        (S := {α | ∃ j ∈ A, α = Pi.single j 1 ∨ α = -Pi.single j 1}) ⟨j, hj, Or.inr rfl⟩ c
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨j, hj, rfl | rfl⟩ := hα
    · rw [pinnedX_single]
      exact Subgroup.subset_closure ⟨j, hj, c, Or.inl rfl⟩
    · rw [pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨j, hj, c, Or.inr rfl⟩

private theorem torusGroup_le_normalizer_subsystemGroup (A : Set (Fin τ.rank)) :
    torusGroup τ K ≤ Subgroup.normalizer (subsystemGroup τ K A : Set (ModGL τ K)) := by
  rw [subsystemGroup_eq_rootSpan]
  refine torusGroup_le_normalizer_rootSpan ?_
  rintro α ⟨j, -, rfl | rfl⟩
  · exact isRoot_single τ j
  · exact isRoot_neg_single τ j

theorem commutator_parabolicLevi_le_subsystemGroup (A : Set (Fin τ.rank)) :
    ⁅parabolicLevi τ K A, parabolicLevi τ K A⁆ ≤ subsystemGroup τ K A :=
  commutator_sup_le_of_commutative_of_le_normalizer
    (torusGroup_le_normalizer_subsystemGroup A) fun _ ha _ hb => torusGroup_mul_comm ha hb

end Levi

end CFSG.LieType.SeitzGeneration.ExcWideThree
