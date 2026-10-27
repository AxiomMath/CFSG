module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFPermEF
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFPermInvolution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPermWitness

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoNormalizerE

open Equiv Subgroup Janko
open scoped Pointwise

theorem mem_normalizer_Ebar {g : alternatingGroup (Fin 9)} (h₁ : g * sbar₁ * g⁻¹ ∈ Ebar)
    (h₂ : g * ebar₂ * g⁻¹ ∈ Ebar) (h₃ : g * ebar₃ * g⁻¹ ∈ Ebar) :
    g ∈ normalizer (Ebar : Set (alternatingGroup (Fin 9))) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [Ebar, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
  rcases hx with rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃

theorem sbar₁_mem_Ebar : sbar₁ ∈ Ebar :=
  JankoPerm.gens_subset_Ebar (by simp)

theorem ebar₂_mem_Ebar : ebar₂ ∈ Ebar :=
  JankoPerm.gens_subset_Ebar (by simp)

theorem ebar₃_mem_Ebar : ebar₃ ∈ Ebar :=
  JankoPerm.gens_subset_Ebar (by simp)

theorem tbar_mem_normalizer_Ebar : tbar ∈ normalizer (Ebar : Set (alternatingGroup (Fin 9))) := by
  refine mem_normalizer_Ebar ?_ ?_ ?_
  · rw [tbar_conj_sbar₁]
    exact inv_mem sbar₁_mem_Ebar
  · rw [show tbar * ebar₂ * tbar⁻¹ = ebar₃ from Subtype.ext (show (tbar : Perm (Fin 9)) * ebar₂ *
      (tbar : Perm (Fin 9))⁻¹ = ebar₃ by decide)]
    exact ebar₃_mem_Ebar
  · rw [show tbar * ebar₃ * tbar⁻¹ = ebar₂ from Subtype.ext (show (tbar : Perm (Fin 9)) * ebar₃ *
      (tbar : Perm (Fin 9))⁻¹ = ebar₂ by decide)]
    exact ebar₂_mem_Ebar

theorem ρbar_conj_sbar₁ : ρbar * sbar₁ * ρbar⁻¹ = ebar₂ :=
  Subtype.ext (show (ρbar : Perm (Fin 9)) * sbar₁ * (ρbar : Perm (Fin 9))⁻¹ = ebar₂ by decide)

theorem ρbar_mem_normalizer_Ebar : ρbar ∈ normalizer (Ebar : Set (alternatingGroup (Fin 9))) := by
  refine mem_normalizer_Ebar ?_ ?_ ?_
  · rw [ρbar_conj_sbar₁]
    exact ebar₂_mem_Ebar
  · rw [show ρbar * ebar₂ * ρbar⁻¹ = ebar₃ from Subtype.ext (show (ρbar : Perm (Fin 9)) * ebar₂ *
      (ρbar : Perm (Fin 9))⁻¹ = ebar₃ by decide)]
    exact ebar₃_mem_Ebar
  · rw [show ρbar * ebar₃ * ρbar⁻¹ = sbar₁ from Subtype.ext (show (ρbar : Perm (Fin 9)) * ebar₃ *
      (ρbar : Perm (Fin 9))⁻¹ = sbar₁ by decide)]
    exact sbar₁_mem_Ebar

theorem Kbar_le_normalizer_Ebar : Kbar ≤ normalizer (Ebar : Set (alternatingGroup (Fin 9))) := by
  rw [Kbar, closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact tbar_mem_normalizer_Ebar
  · exact JankoF.ℓbar_mem_normalizer_Ebar
  · exact ρbar_mem_normalizer_Ebar

theorem tbar_mem_Kbar : tbar ∈ Kbar :=
  subset_closure (by simp)

theorem ℓbar_mem_Kbar : ℓbar ∈ Kbar :=
  subset_closure (by simp)

theorem ρbar_mem_Kbar : ρbar ∈ Kbar :=
  subset_closure (by simp)

theorem Kbar_le_stabilizer : Kbar ≤ (MulAction.stabilizer (Perm (Fin 9))
    ({0, 3, 6} : Finset (Fin 9))).comap (alternatingGroup (Fin 9)).subtype := by
  rw [Kbar, closure_le]
  rintro _ (rfl | rfl | rfl) <;> exact mem_comap.mpr (MulAction.mem_stabilizer_iff.mpr (by decide))

theorem Ebar_inf_Kbar : Ebar ⊓ Kbar = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgE, hgK⟩
  have hS : (g : Perm (Fin 9)) • ({0, 3, 6} : Finset (Fin 9)) = {0, 3, 6} :=
    MulAction.mem_stabilizer_iff.mp (mem_comap.mp (Kbar_le_stabilizer hgK))
  have hmem : ∀ x ∈ ({0, 3, 6} : Finset (Fin 9)),
      (g : Perm (Fin 9)) x ∈ ({0, 3, 6} : Finset (Fin 9)) := by
    intro x hx
    rw [← hS]
    exact Finset.smul_mem_smul_finset hx
  have hE := JankoPerm.apply_mem_of_mem_Ebar hgE
  simp only [Finset.mem_product] at hE
  obtain ⟨h0, h3, h6⟩ := hE
  have key : ∀ a : Fin 9, ∀ b : Fin 9, a ∈ ({0, 3, 6} : Finset (Fin 9)) →
      a ∈ ({b, b + 1, b + 2} : Finset (Fin 9)) → b = 0 ∨ b = 3 ∨ b = 6 → a = b := by decide
  exact mem_bot.mpr (JankoPerm.eq_one_of_mem_Ebar hgE (key _ 0 (hmem 0 (by decide)) h0 (by simp))
    (key _ 3 (hmem 3 (by decide)) h3 (by simp)) (key _ 6 (hmem 6 (by decide)) h6 (by simp)))

theorem orderOf_ρbar : orderOf ρbar = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext (show (ρbar : Perm (Fin 9)) ^ 3 = 1 by decide)) ?_
  intro h
  have h0 : (ρbar : Perm (Fin 9)) 0 = 0 := by rw [h]; rfl
  exact absurd h0 (by decide)

theorem ρbar_conj_sbar₁_ne : ρbar * sbar₁ * ρbar⁻¹ ≠ sbar₁ ∧ ρbar * sbar₁ * ρbar⁻¹ ≠ sbar₁⁻¹ := by
  rw [ρbar_conj_sbar₁]
  constructor
  · intro h
    have h3 := congrArg (fun g : alternatingGroup (Fin 9) => (g : Perm (Fin 9)) 3) h
    exact absurd h3 (by decide)
  · intro h
    have h3 := congrArg (fun g : alternatingGroup (Fin 9) => (g : Perm (Fin 9)) 3) h
    exact absurd h3 (by decide)

theorem tbar_conj_ρbar_ne : tbar * ρbar * tbar⁻¹ ≠ ρbar ∧ tbar * ρbar * tbar⁻¹ ≠ ρbar⁻¹ := by
  have h : ((tbar * ρbar * tbar⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) 1 = 8 :=
    show ((tbar : Perm (Fin 9)) * ρbar * (tbar : Perm (Fin 9))⁻¹) 1 = 8 by decide
  constructor
  · intro h'
    rw [h'] at h
    exact absurd h (by decide)
  · intro h'
    rw [h'] at h
    exact absurd h (show ((ρbar : Perm (Fin 9)))⁻¹ 1 ≠ 8 by decide)

theorem tbar_notMem_Fbar : tbar ∉ Fbar := by
  rw [mem_Fbar_iff]
  decide

theorem mem_closure_ybar_qbar {g : alternatingGroup (Fin 9)}
    (hg : g ∈ closure ({ybar, tbar * ℓbar} : Set (alternatingGroup (Fin 9)))) :
    g = 1 ∨ g = ybar ∨ g = tbar * ℓbar ∨ g = ybar * (tbar * ℓbar) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one] <;> decide
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one, InvMemClass.coe_inv] <;>
      decide

theorem cycleType_ybar_mul_qbar : ((ybar * (tbar * ℓbar) : alternatingGroup (Fin 9)) :
    Perm (Fin 9)).cycleType = {2, 2} := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← multiset_replicate_two_two,
    cycleType_eq_replicate_iff_of_sq_eq_one (by decide)]
  decide

theorem cycleType_of_mem_closure_ybar_qbar {g : alternatingGroup (Fin 9)}
    (hg : g ∈ closure ({ybar, tbar * ℓbar} : Set (alternatingGroup (Fin 9)))) (hg1 : g ≠ 1) :
    (g : Perm (Fin 9)).cycleType = {2, 2} := by
  rcases mem_closure_ybar_qbar hg with rfl | rfl | rfl | rfl
  · exact absurd rfl hg1
  · exact JankoF.cycleType_ybar
  · exact JankoF.cycleType_tbar_mul_ℓbar
  · exact cycleType_ybar_mul_qbar

theorem card_closure_ybar_qbar :
    Nat.card (closure ({ybar, tbar * ℓbar} : Set (alternatingGroup (Fin 9)))) = 4 := by
  have hy : ybar ∈ closure ({ybar, tbar * ℓbar} : Set (alternatingGroup (Fin 9))) :=
    subset_closure (by simp)
  have hq : tbar * ℓbar ∈ closure ({ybar, tbar * ℓbar} : Set (alternatingGroup (Fin 9))) :=
    subset_closure (by simp)
  have h : ((closure ({ybar, tbar * ℓbar} : Set (alternatingGroup (Fin 9))) : Set _)) =
      (({1, ybar, tbar * ℓbar, ybar * (tbar * ℓbar)} : Finset (alternatingGroup (Fin 9))) :
        Set (alternatingGroup (Fin 9))) := by
    ext g
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    refine ⟨mem_closure_ybar_qbar, ?_⟩
    rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact hy
    · exact hq
    · exact mul_mem hy hq
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoNormalizerE
