module

public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace AnchoredLowNormRectangle

open Finset

section Arith

variable {I J : Type*} [Fintype I] [Fintype J]

theorem one_le_sq_of_ne_zero {n : ℤ} (h : n ≠ 0) : 1 ≤ n ^ 2 := by
  have h0 : 0 < n ^ 2 := by positivity
  linarith [Int.add_one_le_iff.mpr h0]

theorem one_le_sum_sq_of_exists_ne_zero {a : I → ℤ} (h : ∃ i, a i ≠ 0) : 1 ≤ ∑ i, a i ^ 2 := by
  obtain ⟨i, hi⟩ := h
  calc (1 : ℤ) ≤ a i ^ 2 := one_le_sq_of_ne_zero hi
    _ ≤ ∑ i, a i ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)

theorem eq_one_of_sum_sq_le {a : I → J → ℤ} {i₀ : I} {j₀ : J} (h00 : a i₀ j₀ = 1)
    (hexch : ∀ i j, a i j = a i j₀ + a i₀ j - a i₀ j₀)
    (hbound : ∑ i, ∑ j, a i j ^ 2 ≤ (Fintype.card I : ℤ) + 1)
    (hq : (Fintype.card I : ℤ) + 1 < Fintype.card J) (i : I) : a i j₀ = 1 := by
  by_contra hne
  have hcol : ∀ j : J, 1 ≤ ∑ i' : I, a i' j ^ 2 := by
    intro j
    refine one_le_sum_sq_of_exists_ne_zero ?_
    by_cases h : a i₀ j = 0
    · exact ⟨i, by rw [hexch i j, h, h00]; intro hz; exact hne (by linarith)⟩
    · exact ⟨i₀, h⟩
  have hge : (Fintype.card J : ℤ) ≤ ∑ i : I, ∑ j : J, a i j ^ 2 := by
    rw [Finset.sum_comm]
    calc (Fintype.card J : ℤ) = ∑ _j : J, (1 : ℤ) := by simp
      _ ≤ ∑ j : J, ∑ i : I, a i j ^ 2 := Finset.sum_le_sum fun j _ => hcol j
  linarith

theorem eq_zero_of_ne_of_sum_sq_le {a : I → J → ℤ} {i₀ : I} {j₀ : J} (h00 : a i₀ j₀ = 1)
    (hexch : ∀ i j, a i j = a i j₀ + a i₀ j - a i₀ j₀)
    (hbound : ∑ i, ∑ j, a i j ^ 2 ≤ (Fintype.card I : ℤ) + 1)
    (hq : (Fintype.card I : ℤ) + 1 < Fintype.card J) (hm : 2 ≤ Fintype.card I)
    {i : I} {j : J} (hj : j ≠ j₀) : a i j = 0 := by
  classical
  have hrow : ∀ i, a i j₀ = 1 := fun i => eq_one_of_sum_sq_le h00 hexch hbound hq i
  have hconst : ∀ i j, a i j = a i₀ j := fun i j => by rw [hexch i j, hrow i, h00]; ring
  set S := ∑ j : J, a i₀ j ^ 2 with hS
  have hsum : ∑ i : I, ∑ j : J, a i j ^ 2 = (Fintype.card I : ℤ) * S := by
    have h1 : ∀ i : I, ∑ j : J, a i j ^ 2 = S := fun i =>
      Finset.sum_congr rfl fun j _ => by rw [hconst i j]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (2 : ℤ) ≤ (Fintype.card I : ℤ) := by exact_mod_cast hm
  have hle : (Fintype.card I : ℤ) * S ≤ (Fintype.card I : ℤ) + 1 := by rw [← hsum]; exact hbound
  have hSle : S ≤ 1 := by nlinarith
  have h2 : a i₀ j ^ 2 + a i₀ j₀ ^ 2 ≤ S := by
    have h3 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({j, j₀} : Finset J))
      fun x _ _ => sq_nonneg (a i₀ x)
    rwa [Finset.sum_pair hj] at h3
  have hzero : a i₀ j ^ 2 = 0 := by rw [h00] at h2; nlinarith [sq_nonneg (a i₀ j)]
  rw [hconst i j]
  exact pow_eq_zero_iff two_ne_zero |>.mp hzero

end Arith

variable {G : Type*} [Group G] [Fintype G] {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] {η : I → J → G → ℂ} {f : G → ℂ} {a : I → J → ℤ}
  {i₀ : I} {j₀ : J}

omit [Fintype I] [Fintype J] [Group G] in
theorem cfInner_eq_ite (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2) (i i' : I)
    (j j' : J) : cfInner (η i j) (η i' j') = if i = i' ∧ j = j' then 1 else 0 := by
  simpa [Prod.ext_iff] using hη.cfInner_eq_ite (i, j) (i', j')

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem exists_int_coeff (hηmem : ∀ i j, η i j ∈ Submodule.span ℤ (Irr G))
    (hf : f ∈ Submodule.span ℤ (Irr G)) :
    ∃ a : I → J → ℤ, ∀ i j, cfInner f (η i j) = (a i j : ℂ) := by
  choose a ha using fun (i : I) (j : J) => exists_int_cfInner_of_mem_span_Irr hf (hηmem i j)
  exact ⟨a, ha⟩

omit [Group G] in
theorem sum_sq_le (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2)
    (ha : ∀ i j, cfInner f (η i j) = (a i j : ℂ))
    (hf : cfInner f f = (Fintype.card I : ℂ) + 1) :
    ∑ i, ∑ j, a i j ^ 2 ≤ (Fintype.card I : ℤ) + 1 := by
  have hb := sum_norm_sq_cfInner_le hη f
  rw [hf, Fintype.sum_prod_type] at hb
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hb
  have h : ((∑ i, ∑ j, a i j ^ 2 : ℤ) : ℝ) ≤ (Fintype.card I : ℝ) + 1 := by
    refine le_trans (le_of_eq ?_) hb
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ha i j]
    simp [sq_abs]
  exact_mod_cast h

omit [Group G] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem exchange_int (ha : ∀ i j, cfInner f (η i j) = (a i j : ℂ))
    (hexch : ∀ i j, cfInner f (η i j) + cfInner f (η i₀ j₀)
      = cfInner f (η i j₀) + cfInner f (η i₀ j)) (i : I) (j : J) :
    a i j = a i j₀ + a i₀ j - a i₀ j₀ := by
  have h := hexch i j
  rw [ha, ha, ha, ha] at h
  have h1 : ((a i j + a i₀ j₀ : ℤ) : ℂ) = ((a i j₀ + a i₀ j : ℤ) : ℂ) := by push_cast; exact h
  have h2 : a i j + a i₀ j₀ = a i j₀ + a i₀ j := by exact_mod_cast h1
  omega

theorem cfInner_eq_one (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2)
    (hηmem : ∀ i j, η i j ∈ Submodule.span ℤ (Irr G)) (hf : f ∈ Submodule.span ℤ (Irr G))
    (hq : (Fintype.card I : ℤ) + 1 < Fintype.card J)
    (hnorm : cfInner f f = (Fintype.card I : ℂ) + 1) (h00 : cfInner f (η i₀ j₀) = 1)
    (hexch : ∀ i j, cfInner f (η i j) + cfInner f (η i₀ j₀)
      = cfInner f (η i j₀) + cfInner f (η i₀ j)) (i : I) :
    cfInner f (η i j₀) = 1 := by
  obtain ⟨a, ha⟩ := exists_int_coeff hηmem hf
  have h00' : a i₀ j₀ = 1 := by
    have h := h00; rw [ha] at h; exact_mod_cast h
  rw [ha, eq_one_of_sum_sq_le h00' (exchange_int ha hexch) (sum_sq_le hη ha hnorm) hq i]
  norm_num

theorem cfInner_eq_zero (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2)
    (hηmem : ∀ i j, η i j ∈ Submodule.span ℤ (Irr G)) (hf : f ∈ Submodule.span ℤ (Irr G))
    (hm : 2 ≤ Fintype.card I) (hq : (Fintype.card I : ℤ) + 1 < Fintype.card J)
    (hnorm : cfInner f f = (Fintype.card I : ℂ) + 1) (h00 : cfInner f (η i₀ j₀) = 1)
    (hexch : ∀ i j, cfInner f (η i j) + cfInner f (η i₀ j₀)
      = cfInner f (η i j₀) + cfInner f (η i₀ j)) (i : I) {j : J} (hj : j ≠ j₀) :
    cfInner f (η i j) = 0 := by
  obtain ⟨a, ha⟩ := exists_int_coeff hηmem hf
  have h00' : a i₀ j₀ = 1 := by
    have h := h00; rw [ha] at h; exact_mod_cast h
  rw [ha, eq_zero_of_ne_of_sum_sq_le h00' (exchange_int ha hexch) (sum_sq_le hη ha hnorm) hq hm hj]
  norm_num

omit [Fintype J] [Group G] in
theorem cfInner_sum_col_self (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2) (j₀ : J) :
    cfInner (∑ i, η i j₀) (∑ i, η i j₀) = (Fintype.card I : ℂ) := by
  rw [cfInner_sum_left]
  have h : ∀ i : I, cfInner (η i j₀) (∑ i' : I, η i' j₀) = 1 := by
    intro i
    rw [cfInner_sum_right, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [cfInner_eq_ite hη]
    · intro b _ hb
      simp [cfInner_eq_ite hη, Ne.symm hb]
  simp [h]

omit [Fintype J] [DecidableEq I] [DecidableEq J] [Group G] in
theorem cfInner_sum_col_right (hrow : ∀ i, cfInner f (η i j₀) = 1) :
    cfInner f (∑ i, η i j₀) = (Fintype.card I : ℂ) := by
  rw [cfInner_sum_right]
  simp [hrow]

omit [Fintype J] [DecidableEq I] [DecidableEq J] [Group G] in
theorem cfInner_sum_col_left (hrow : ∀ i, cfInner f (η i j₀) = 1) :
    cfInner (∑ i, η i j₀) f = (Fintype.card I : ℂ) := by
  rw [← conj_cfInner, cfInner_sum_col_right hrow]
  simp

omit [Fintype G] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem mem_span_Irr_residue (hηmem : ∀ i j, η i j ∈ Submodule.span ℤ (Irr G))
    (hf : f ∈ Submodule.span ℤ (Irr G)) (j₀ : J) :
    (∑ i, η i j₀) - f ∈ Submodule.span ℤ (Irr G) :=
  Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => hηmem i j₀) hf

omit [Fintype J] [Group G] in
theorem cfInner_self_residue (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2)
    (hrow : ∀ i, cfInner f (η i j₀) = 1) (hnorm : cfInner f f = (Fintype.card I : ℂ) + 1) :
    cfInner ((∑ i, η i j₀) - f) ((∑ i, η i j₀) - f) = 1 := by
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_sum_col_self hη,
    cfInner_sum_col_right hrow, cfInner_sum_col_left hrow, hnorm]
  ring

omit [Fintype J] [Group G] in
theorem isOrthogonal_residue (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2)
    (hrow : ∀ i, cfInner f (η i j₀) = 1)
    (hzero : ∀ i, ∀ j ≠ j₀, cfInner f (η i j) = 0) (i : I) (j : J) :
    IsOrthogonal ((∑ i, η i j₀) - f) (η i j) := by
  rw [isOrthogonal_iff, cfInner_sub_left, cfInner_sum_left]
  by_cases hj : j = j₀
  · subst hj
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i), hrow i]
    · simp [cfInner_eq_ite hη]
    · intro b _ hb
      simp [cfInner_eq_ite hη, hb]
  · rw [hzero i j hj]
    simp [cfInner_eq_ite hη, Ne.symm hj]

omit [Fintype G] [Fintype J] [DecidableEq I] [DecidableEq J] [Group G] in
theorem eq_sum_col_sub_residue (f : G → ℂ) (η : I → J → G → ℂ) (j₀ : J) :
    f = (∑ i, η i j₀) - ((∑ i, η i j₀) - f) := by
  rw [sub_sub_cancel]

theorem exists_virtualChar_norm_one (hη : IsOrthonormalFamily fun p : I × J => η p.1 p.2)
    (hηmem : ∀ i j, η i j ∈ Submodule.span ℤ (Irr G)) (hf : f ∈ Submodule.span ℤ (Irr G))
    (hm : 2 ≤ Fintype.card I) (hq : (Fintype.card I : ℤ) + 1 < Fintype.card J)
    (hnorm : cfInner f f = (Fintype.card I : ℂ) + 1) (h00 : cfInner f (η i₀ j₀) = 1)
    (hexch : ∀ i j, cfInner f (η i j) + cfInner f (η i₀ j₀)
      = cfInner f (η i j₀) + cfInner f (η i₀ j)) :
    (∀ i, cfInner f (η i j₀) = 1) ∧ (∀ i, ∀ j ≠ j₀, cfInner f (η i j) = 0) ∧
      ∃ χ ∈ Submodule.span ℤ (Irr G), cfInner χ χ = 1 ∧ (∀ i j, IsOrthogonal χ (η i j)) ∧
        f = (∑ i, η i j₀) - χ := by
  have hrow : ∀ i, cfInner f (η i j₀) = 1 :=
    fun i => cfInner_eq_one hη hηmem hf hq hnorm h00 hexch i
  have hzero : ∀ i, ∀ j ≠ j₀, cfInner f (η i j) = 0 :=
    fun i j hj => cfInner_eq_zero hη hηmem hf hm hq hnorm h00 hexch i hj
  exact ⟨hrow, hzero, (∑ i, η i j₀) - f, mem_span_Irr_residue hηmem hf j₀,
    cfInner_self_residue hη hrow hnorm, isOrthogonal_residue hη hrow hzero,
    eq_sum_col_sub_residue f η j₀⟩

end AnchoredLowNormRectangle

end CFSG.FeitThompson
