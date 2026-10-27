module

public import CFSG.CharacterTheory.PermutationCharacterOrbits

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

variable (W I : Type*) [Group W] [MulAction W I] [Fintype I]

@[expose] noncomputable def sumZeroSubmodule : Submodule ℂ (I → ℂ) where
  carrier := {f | ∑ i, f i = 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at hf hg ⊢
    rw [hf, hg, add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hf ⊢
    rw [← Finset.mul_sum, hf, mul_zero]

theorem mem_sumZeroSubmodule (f : I → ℂ) : f ∈ sumZeroSubmodule I ↔ ∑ i, f i = 0 := Iff.rfl

@[expose] noncomputable def sumZeroSubrep : Subrepresentation (permutationRepresentation W I) where
  toSubmodule := sumZeroSubmodule I
  apply_mem_toSubmodule g f hf := by
    rw [mem_sumZeroSubmodule] at hf ⊢
    simp only [permutationRepresentation_apply]
    rw [← hf]
    exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ (fun _ => rfl)

theorem sumZeroSubrep_toSubmodule :
    (sumZeroSubrep W I).toSubmodule = sumZeroSubmodule I := rfl

@[expose] noncomputable def constantSubmodule : Submodule ℂ (I → ℂ) :=
  Submodule.span ℂ {fun _ => 1}

theorem isCompl_sumZero_constant [Nonempty I] :
    IsCompl (sumZeroSubmodule I) (constantSubmodule I) := by
  have hcard : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · rw [Submodule.disjoint_def]
    intro f hf hc
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hc
    rw [mem_sumZeroSubmodule] at hf
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hf
    have hc0 : c = 0 := (mul_eq_zero.mp hf).resolve_left hcard
    rw [hc0, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have havg : (fun _ => (∑ i, f i) / Fintype.card I) ∈ constantSubmodule I := by
      apply Submodule.mem_span_singleton.mpr
      exact ⟨(∑ i, f i) / Fintype.card I, by funext i; simp⟩
    have hrest : f - (fun _ => (∑ i, f i) / Fintype.card I) ∈ sumZeroSubmodule I := by
      rw [mem_sumZeroSubmodule]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
      ring
    have h := Submodule.add_mem_sup hrest havg
    rwa [sub_add_cancel] at h

theorem sumZeroSubrep_character [Nonempty I] (w : W) :
    (sumZeroSubrep W I).toRepresentation.character w = fixedPointCount W I w - 1 := by
  set N : Fin 2 → Submodule ℂ (I → ℂ) := ![sumZeroSubmodule I, constantSubmodule I] with hN
  have hint : DirectSum.IsInternal N := by
    rw [DirectSum.isInternal_submodule_iff_isCompl N (i := 0) (j := 1) (by decide)
      (by ext k; fin_cases k <;> simp)]
    exact isCompl_sumZero_constant I
  have hmaps : ∀ k, Set.MapsTo (permutationRepresentation W I w) (N k) (N k) := by
    intro k
    fin_cases k
    · intro f hf
      exact (sumZeroSubrep W I).apply_mem_toSubmodule w hf
    · intro f hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
      exact Submodule.mem_span_singleton.mpr ⟨c, by funext i; rfl⟩
  have htrace := LinearMap.trace_eq_sum_trace_restrict hint hmaps
  rw [Fin.sum_univ_two] at htrace
  have hconst : LinearMap.trace ℂ (N 1) ((permutationRepresentation W I w).restrict (hmaps 1)) =
      1 := by
    have hid : (permutationRepresentation W I w).restrict (hmaps 1) = LinearMap.id := by
      ext ⟨f, hf⟩ i
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
      rfl
    rw [hid, LinearMap.trace_id]
    have hrank : Module.finrank ℂ (N 1) = 1 := by
      change Module.finrank ℂ (Submodule.span ℂ {fun _ : I => (1 : ℂ)}) = 1
      apply finrank_span_singleton
      intro h
      have := congrFun h (Classical.arbitrary I)
      exact one_ne_zero this
    rw [hrank, Nat.cast_one]
  rw [hconst] at htrace
  have hperm := permutationRepresentation_character (W := W) (I := I) w
  rw [Representation.character] at hperm
  rw [← hperm, htrace]
  change LinearMap.trace ℂ (sumZeroSubmodule I)
      ((permutationRepresentation W I w).restrict ((sumZeroSubrep W I).apply_mem_toSubmodule w)) =
    LinearMap.trace ℂ (N 0) ((permutationRepresentation W I w).restrict (hmaps 0)) + 1 - 1
  rw [add_sub_cancel_right]
  rfl

end CFSG.Wreathed.CentralSL2
