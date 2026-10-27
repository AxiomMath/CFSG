module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.CharacterValuesAlgebraicIntegers
import CFSG.FeitThompson.Representations.RationalAlgebraicIntegerIsInteger

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {G : Type*} [Group G]

theorem isIntegral_apply_of_mem_span_Irr [Finite G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (x : G) : IsIntegral ℤ (f x) := by
  induction hf using Submodule.span_induction with
  | mem χ hχ => obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ; exact FDRep.isIntegral_character V x
  | zero => simpa using isIntegral_zero
  | add g h _ _ hg hh => simpa using hg.add hh
  | smul a g _ hg =>
      have ha : IsIntegral ℤ ((a : ℂ)) := isIntegral_intCast a
      simpa using ha.mul hg

theorem exists_int_apply_one_of_mem_span_Irr {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) : ∃ n : ℤ, f 1 = n := by
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
      exact ⟨(finrank ℂ V.V : ℤ), by simp [FDRep.char_one]⟩
  | zero => exact ⟨0, by simp⟩
  | add g h _ _ hg hh =>
      obtain ⟨m, hm⟩ := hg; obtain ⟨n, hn⟩ := hh
      exact ⟨m + n, by rw [Pi.add_apply, hm, hn]; push_cast; ring⟩
  | smul a g _ hg =>
      obtain ⟨m, hm⟩ := hg
      exact ⟨a * m, by rw [Pi.smul_apply, zsmul_eq_mul, hm]; push_cast; ring⟩

theorem exists_int_sum_subgroup_of_mem_span_Irr (Z : Subgroup G) [Fintype Z] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) :
    ∃ m : ℤ, ∑ z : Z, f z = (Nat.card Z : ℂ) * m := by
  have hcard : ((Nat.card Z : ℂ)) ≠ 0 := by simp
  have _ : Invertible ((Nat.card Z : ℂ)) := invertibleOfNonzero hcard
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
      refine ⟨(finrank ℂ (Representation.invariants (V.ρ.comp Z.subtype)) : ℤ), ?_⟩
      have h := Representation.card_inv_mul_sum_char_eq_finrank
        (V.ρ.comp Z.subtype : Representation ℂ Z V.V)
      have h2 : ∀ z : Z, Representation.character (V.ρ.comp Z.subtype) z
          = FDRep.character V (z : G) := fun z => rfl
      simp only [h2] at h
      push_cast
      rw [← h]
      field_simp
  | zero => exact ⟨0, by simp⟩
  | add g h _ _ hg hh =>
      obtain ⟨m, hm⟩ := hg; obtain ⟨n, hn⟩ := hh
      refine ⟨m + n, ?_⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, hm, hn]
      push_cast
      ring
  | smul a g _ hg =>
      obtain ⟨m, hm⟩ := hg
      refine ⟨a * m, ?_⟩
      simp only [Pi.smul_apply, zsmul_eq_mul, ← Finset.mul_sum, hm]
      push_cast
      ring

theorem exists_int_cfInner_res_one (Z : Subgroup G) [Fintype Z] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) : ∃ m : ℤ, cfInner (fun z : Z => f z) 1 = m := by
  obtain ⟨m, hm⟩ := exists_int_sum_subgroup_of_mem_span_Irr Z hf
  refine ⟨m, ?_⟩
  have hcard : ((Nat.card Z : ℂ)) ≠ 0 := by simp
  rw [cfInner_def]
  simp only [Pi.one_apply, map_one, mul_one, hm]
  field_simp

theorem sum_subgroup_of_eq_on_punctured (Z : Subgroup G) [Fintype Z] {f : G → ℂ} {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → f z = c) :
    ∑ z : Z, f z = f 1 + ((Nat.card Z : ℂ) - 1) * c := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Z))]
  have h1 : ∑ z ∈ (Finset.univ : Finset Z).erase 1, f z
      = ∑ _z ∈ (Finset.univ : Finset Z).erase 1, c := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz1 : z ≠ 1 := (Finset.mem_erase.1 hz).1
    exact hc z z.2 fun h => hz1 (Subtype.ext h)
  rw [h1, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ : Finset Z).erase 1).card = Nat.card Z - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hcard, Nat.cast_sub Nat.card_pos]
  norm_num

theorem exists_int_of_eq_on_punctured_subgroup [Finite G] {Z : Subgroup G} (hZ : Z ≠ ⊥)
    {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G)) {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → f z = c) : ∃ n : ℤ, c = n := by
  have _ : Fintype Z := Fintype.ofFinite _
  obtain ⟨n₁, hn₁⟩ := exists_int_apply_one_of_mem_span_Irr (G := G) hf
  obtain ⟨m, hm⟩ := exists_int_sum_subgroup_of_mem_span_Irr Z hf
  have hsum := sum_subgroup_of_eq_on_punctured Z hc
  have hN : 1 < Nat.card Z := (Subgroup.one_lt_card_iff_ne_bot Z).2 hZ
  have hNne : ((Nat.card Z : ℂ) - 1) ≠ 0 :=
    sub_ne_zero_of_ne (by exact_mod_cast hN.ne')
  have hceq : c = ((Nat.card Z : ℂ) * m - n₁) / ((Nat.card Z : ℂ) - 1) := by
    field_simp
    rw [← hm, hsum, hn₁]
    ring
  have hrat : ∃ q : ℚ, c = (q : ℂ) := by
    refine ⟨((Nat.card Z : ℚ) * m - n₁) / ((Nat.card Z : ℚ) - 1), ?_⟩
    rw [hceq]
    push_cast
    ring
  obtain ⟨z₀, hz₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
  have hcint : IsIntegral ℤ c := by
    rw [← hc z₀ z₀.2 (fun h => hz₀ (Subtype.ext h))]
    exact isIntegral_apply_of_mem_span_Irr hf _
  exact (Complex.isIntegral_int_iff_exists_int_of_exists_rat hrat).1 hcint

end CFSG.FeitThompson
