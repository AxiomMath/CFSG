module

public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormOnePivot

variable {G : Type*} [Group G] [Fintype G]

theorem int_eq_of_sub_eq_one_of_sq_add_sq_le_one {r s : ℤ} (hrs : r - s = 1)
    (hle : r ^ 2 + s ^ 2 ≤ 1) : (r = 1 ∧ s = 0) ∨ (r = 0 ∧ s = -1) := by
  have hr : r = s + 1 := by omega
  subst hr
  have h1 : s ≤ 0 := by nlinarith
  have h2 : -1 ≤ s := by nlinarith
  omega

theorem eq_sum_smul_of_cfInner_self_eq_sum_mul_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : ι → G → ℂ} (he : IsOrthonormalFamily e) {x : G → ℂ} {c : ι → ℂ}
    (hc : ∀ i, cfInner x (e i) = c i)
    (hnorm : cfInner x x = ∑ i, c i * (starRingEnd ℂ) (c i)) :
    x = ∑ i, c i • e i := by
  have hη : ∀ k l, CauchySchwarzProjection.classFunInner (e k) (e l) = if k = l then 1 else 0 :=
    fun k l => by rw [← cfInner_eq_classFunInner]; exact he.cfInner_eq_ite k l
  have hc' : ∀ k, CauchySchwarzProjection.classFunInner x (e k) = c k := fun k => by
    rw [← cfInner_eq_classFunInner]; exact hc k
  have h := CauchySchwarzProjection.classFunInner_self_eq_add_of_inner_eq hη x c hc'
  rw [← cfInner_eq_classFunInner, ← cfInner_eq_classFunInner, hnorm] at h
  have hz : cfInner (x - ∑ k, c k • e k) (x - ∑ k, c k • e k) = 0 := by linear_combination -h
  have : Nonempty G := ⟨1⟩
  exact sub_eq_zero.1 (cfInner_self_eq_zero.1 hz)

theorem eq_pivot_or_card_eq_two_and_eq_neg
    {ι : Type*} [Finite ι] [DecidableEq ι] {e : ι → G → ℂ} {i₀ : ι}
    (hcard : 2 ≤ Nat.card ι) (hmem : ∀ i, e i ∈ Submodule.span ℤ (Irr G))
    (he : IsOrthonormalFamily e) {x : G → ℂ} (hx : x ∈ Submodule.span ℤ (Irr G))
    (hxx : cfInner x x = 1) (hpivot : ∀ i, i ≠ i₀ → cfInner x (e i₀ - e i) = 1) :
    x = e i₀ ∨ (Nat.card ι = 2 ∧ ∃ i, i ≠ i₀ ∧ x = -e i) := by
  have : Fintype ι := Fintype.ofFinite ι
  choose a ha using fun i => exists_int_cfInner_of_mem_span_Irr hx (hmem i)
  have hsub : ∀ i, i ≠ i₀ → a i₀ - a i = 1 := by
    intro i hi
    have h := hpivot i hi
    rw [cfInner_sub_right, ha, ha] at h
    exact_mod_cast h
  have hbound : (∑ i, a i ^ 2 : ℤ) ≤ 1 := by
    have hb := sum_norm_sq_cfInner_le he x
    rw [hxx] at hb
    simp only [Complex.one_re] at hb
    have hrw : ∀ i ∈ (Finset.univ : Finset ι), ‖cfInner x (e i)‖ ^ 2 = ((a i ^ 2 : ℤ) : ℝ) := by
      intro i _
      rw [ha i, Complex.norm_intCast]
      push_cast
      rw [sq_abs]
    rw [Finset.sum_congr rfl hrw] at hb
    exact_mod_cast hb
  have hpair : ∀ i j, i ≠ j → a i ^ 2 + a j ^ 2 ≤ 1 := by
    intro i j hij
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset ι))
      (fun k _ _ => sq_nonneg (a k))
    rw [Finset.sum_pair hij] at h
    linarith
  have hproj : (∑ i, a i ^ 2 : ℤ) = 1 → x = ∑ i, (a i : ℂ) • e i := by
    intro hs
    refine eq_sum_smul_of_cfInner_self_eq_sum_mul_conj he ha ?_
    have hconj : ∑ i, (a i : ℂ) * (starRingEnd ℂ) (a i : ℂ) = ((∑ i, a i ^ 2 : ℤ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by simp [sq]
    rw [hconj, hs, hxx]
    norm_num
  have : Nontrivial ι := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨i₁, hi₁⟩ := exists_ne i₀
  rcases int_eq_of_sub_eq_one_of_sq_add_sq_le_one (hsub i₁ hi₁) (hpair i₀ i₁ (Ne.symm hi₁)) with
    ⟨h0, h1⟩ | ⟨h0, h1⟩
  ·
    left
    have hzero : ∀ i, i ≠ i₀ → a i = 0 := fun i hi => by have := hsub i hi; omega
    have hs : (∑ i, a i ^ 2 : ℤ) = 1 := by
      rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _)
        (fun j _ hj => by rw [hzero j hj]; ring), h0]
      ring
    rw [hproj hs, Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _)
      (fun j _ hj => by rw [hzero j hj]; simp), h0]
    simp
  ·
    right
    have hneg : ∀ i, i ≠ i₀ → a i = -1 := fun i hi => by have := hsub i hi; omega
    have huniq : ∀ i, i ≠ i₀ → i = i₁ := by
      intro i hi
      by_contra hne
      have h := hpair i i₁ hne
      rw [hneg i hi, hneg i₁ hi₁] at h
      norm_num at h
    have huniv : (Finset.univ : Finset ι) = {i₀, i₁} := by
      refine ((Finset.subset_univ _).antisymm fun i _ => ?_).symm
      rcases eq_or_ne i i₀ with rfl | hi
      · simp
      · simp [huniq i hi]
    have hcard2 : Nat.card ι = 2 := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv,
        Finset.card_insert_of_notMem (by simpa using Ne.symm hi₁)]
      simp
    refine ⟨hcard2, i₁, hi₁, ?_⟩
    have hs : (∑ i, a i ^ 2 : ℤ) = 1 := by
      rw [huniv, Finset.sum_pair (Ne.symm hi₁), h0, h1]
      ring
    rw [hproj hs, huniv, Finset.sum_pair (Ne.symm hi₁), h0, h1]
    simp

theorem eq_zero_or_eq_neg_one_of_cfInner_sub_eq_one {n : ℕ} {e : Fin (n + 2) → G → ℂ}
    (hmem : ∀ i, e i ∈ Submodule.span ℤ (Irr G)) (he : IsOrthonormalFamily e)
    {x : G → ℂ} (hx : x ∈ Submodule.span ℤ (Irr G)) (hxx : cfInner x x = 1)
    (hpivot : ∀ i, i ≠ 0 → cfInner x (e 0 - e i) = 1) :
    x = e 0 ∨ (n + 2 = 2 ∧ x = -e 1) := by
  rcases eq_pivot_or_card_eq_two_and_eq_neg (by simp) hmem he hx hxx hpivot with
    h | ⟨hcard, i, hi, hxi⟩
  · exact Or.inl h
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    refine Or.inr ⟨hcard, ?_⟩
    have hi1 : i = 1 := by
      have hlt : i.val < n + 2 := i.isLt
      have h0 : i.val ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
      have h1 : (1 : Fin (n + 2)).val = 1 := by simp
      exact Fin.ext (by omega)
    exact hi1 ▸ hxi

omit [Group G] in
theorem cfInner_neg_swap_eq_ite {e : Fin 2 → G → ℂ} (he : IsOrthonormalFamily e) (i j : Fin 2) :
    cfInner (![-e 1, -e 0] i) (![-e 1, -e 0] j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cfInner_neg_left, cfInner_neg_right, he.cfInner_eq_ite]

end NormOnePivot

end CFSG.FeitThompson
