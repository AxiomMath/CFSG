module

public import CFSG.FeitThompson.Representations.ClassFunctionCauchySchwarzProjection
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate CauchySchwarzProjection

variable {G : Type*} [Fintype G]

theorem CauchySchwarzProjection.classFunInner_eq_cfInner (f h : G → ℂ) :
    classFunInner f h = cfInner f h := by
  rw [classFunInner_apply, cfInner_def, Nat.card_eq_fintype_card]

theorem int_self_eq_sq_iff {a : ℤ} : a = a ^ 2 ↔ a = 0 ∨ a = 1 := by
  refine ⟨fun h => ?_, fun h => by rcases h with h | h <;> rw [h] <;> ring⟩
  have h2 : a * (a - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (by omega)

theorem int_neg_le_sq (b : ℤ) : -b ≤ b ^ 2 := by nlinarith [sq_nonneg (b + 1)]

theorem int_neg_eq_sq_iff {b : ℤ} : -b = b ^ 2 ↔ b = 0 ∨ b = -1 := by
  refine ⟨fun h => ?_, fun h => by rcases h with h | h <;> rw [h] <;> ring⟩
  have h2 : b * (b + 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (by omega)

theorem exists_subsets_eq_sum_sub_sum_of_norm_eq_card_add_card
    {G : Type*} [Group G] [Fintype G] {n m : ℕ} (_hn : 1 ≤ n) (_hm : 1 ≤ m)
    {R T : Finset (G → ℂ)} (hRT : Disjoint R T)
    (hRmem : ∀ r ∈ R, r ∈ Submodule.span ℤ (Irr G))
    (hTmem : ∀ t ∈ T, t ∈ Submodule.span ℤ (Irr G))
    (hON : IsOrthonormalFamily fun u : {v // v ∈ R ∪ T} => (u : G → ℂ))
    (_hRcard : R.card = 2 * n) (_hTcard : T.card = 2 * m)
    {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    (hfnorm : cfInner f f = (n : ℂ) + (m : ℂ))
    (hfR : cfInner f (∑ r ∈ R, r) = (n : ℂ))
    (hfT : cfInner f (∑ t ∈ T, t) = -(m : ℂ)) :
    ∃ R₀ ⊆ R, ∃ T₀ ⊆ T, R₀.card = n ∧ T₀.card = m ∧
      f = ∑ r ∈ R₀, r - ∑ t ∈ T₀, t := by
  classical
  set E := R ∪ T with hEdef
  have hmem : ∀ u ∈ E, u ∈ Submodule.span ℤ (Irr G) := by
    intro u hu
    rcases Finset.mem_union.1 hu with h | h
    · exact hRmem u h
    · exact hTmem u h
  have hint : ∀ u ∈ E, ∃ z : ℤ, cfInner f u = (z : ℂ) := fun u hu =>
    exists_int_cfInner_of_mem_span_Irr hf (hmem u hu)
  choose! A hA using hint
  have hη : ∀ k l : {v // v ∈ E}, classFunInner (k : G → ℂ) (l : G → ℂ)
      = if k = l then 1 else 0 := fun k l => by
    rw [classFunInner_eq_cfInner]
    by_cases h : k = l
    · rw [if_pos h, h]; exact hON.cfInner_self l
    · rw [if_neg h]; exact isOrthogonal_iff.1 (hON.isOrthogonal h)
  set c : {v // v ∈ E} → ℂ := fun k => ((A (k : G → ℂ) : ℤ) : ℂ) with hcdef
  have hc : ∀ k : {v // v ∈ E}, classFunInner f (k : G → ℂ) = c k := fun k => by
    rw [classFunInner_eq_cfInner, hA _ k.2]
  have hpyth := classFunInner_self_eq_add_of_inner_eq hη f c hc
  set X : G → ℂ := ∑ u ∈ E, (A u : ℂ) • u with hXdef
  have hXeq : (∑ k : {v // v ∈ E}, c k • (k : G → ℂ)) = X :=
    Finset.sum_coe_sort E fun u => (A u : ℂ) • u
  set S : ℤ := ∑ u ∈ E, A u ^ 2 with hSdef
  have hsumsq : (∑ k : {v // v ∈ E}, c k * conj (c k)) = (S : ℂ) := by
    rw [hSdef]
    push_cast
    rw [← Finset.sum_coe_sort E fun u => ((A u : ℂ)) ^ 2]
    exact Finset.sum_congr rfl fun k _ => by simp [hcdef, map_intCast]; ring
  rw [hsumsq, hXeq, classFunInner_eq_cfInner, hfnorm] at hpyth
  have hre : ((n : ℝ) + m) = (S : ℝ) + (classFunInner (f - X) (f - X)).re := by
    simpa using congrArg Complex.re hpyth
  have hresid := classFunInner_self_re_nonneg (f - X)
  have hSle : S ≤ (n : ℤ) + m := by
    have : (S : ℝ) ≤ (n : ℝ) + m := by linarith
    exact_mod_cast this
  have hAR : ∑ r ∈ R, A r = (n : ℤ) := by
    have h1 : cfInner f (∑ r ∈ R, r) = ((∑ r ∈ R, A r : ℤ) : ℂ) := by
      rw [cfInner_sum_right]
      push_cast
      exact Finset.sum_congr rfl fun r hr => hA r (Finset.mem_union_left _ hr)
    rw [hfR] at h1
    exact_mod_cast h1.symm
  have hAT : ∑ t ∈ T, A t = -(m : ℤ) := by
    have h1 : cfInner f (∑ t ∈ T, t) = ((∑ t ∈ T, A t : ℤ) : ℂ) := by
      rw [cfInner_sum_right]
      push_cast
      exact Finset.sum_congr rfl fun t ht => hA t (Finset.mem_union_right _ ht)
    rw [hfT] at h1
    exact_mod_cast h1.symm
  have hRle : ∀ r ∈ R, A r ≤ A r ^ 2 := fun r _ => Int.le_self_sq _
  have hTle : ∀ t ∈ T, -(A t) ≤ A t ^ 2 := fun t _ => int_neg_le_sq _
  have hsplit : S = (∑ r ∈ R, A r ^ 2) + ∑ t ∈ T, A t ^ 2 := by
    rw [hSdef, hEdef, Finset.sum_union hRT]
  have hQR : ∑ r ∈ R, A r ≤ ∑ r ∈ R, A r ^ 2 := Finset.sum_le_sum hRle
  have hQT : ∑ t ∈ T, (-(A t)) ≤ ∑ t ∈ T, A t ^ 2 := Finset.sum_le_sum hTle
  have hQT' : (m : ℤ) ≤ ∑ t ∈ T, A t ^ 2 := by
    rw [Finset.sum_neg_distrib, hAT] at hQT
    simpa using hQT
  have hSeq : S = (n : ℤ) + m := by omega
  have hReq : ∀ r ∈ R, A r = A r ^ 2 :=
    (Finset.sum_eq_sum_iff_of_le hRle).1 (by omega)
  have hTeq : ∀ t ∈ T, -(A t) = A t ^ 2 := by
    refine (Finset.sum_eq_sum_iff_of_le hTle).1 ?_
    rw [Finset.sum_neg_distrib, hAT]
    omega
  have hfX : f = X := by
    have h0 : (classFunInner (f - X) (f - X)).re = 0 := by
      rw [hSeq] at hre; push_cast at hre; linarith
    have h1 := classFunInner_self_re_eq_zero.1 h0
    rwa [sub_eq_zero] at h1
  have hR01 : ∀ r ∈ R, A r = 0 ∨ A r = 1 := fun r hr => int_self_eq_sq_iff.1 (hReq r hr)
  have hT01 : ∀ t ∈ T, A t = 0 ∨ A t = -1 := fun t ht => int_neg_eq_sq_iff.1 (hTeq t ht)
  have hcardR : (R.filter fun r => A r = 1).card = n := by
    have h1 : ∑ r ∈ R, A r = ∑ r ∈ R.filter fun r => A r = 1, A r := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro r hr hnr
      rcases hR01 r hr with h | h
      · exact h
      · exact absurd (Finset.mem_filter.2 ⟨hr, h⟩) hnr
    have h2 : ∑ r ∈ R.filter fun r => A r = 1, A r
        = ((R.filter fun r => A r = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl fun r hr => (Finset.mem_filter.1 hr).2, Finset.sum_const]
      simp
    have h3 : (((R.filter fun r => A r = 1).card : ℤ)) = (n : ℤ) := by rw [← h2, ← h1, hAR]
    exact_mod_cast h3
  have hcardT : (T.filter fun t => A t = -1).card = m := by
    have h1 : ∑ t ∈ T, A t = ∑ t ∈ T.filter fun t => A t = -1, A t := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro t ht hnt
      rcases hT01 t ht with h | h
      · exact h
      · exact absurd (Finset.mem_filter.2 ⟨ht, h⟩) hnt
    have h2 : ∑ t ∈ T.filter fun t => A t = -1, A t
        = -((T.filter fun t => A t = -1).card : ℤ) := by
      rw [Finset.sum_congr rfl fun t ht => (Finset.mem_filter.1 ht).2, Finset.sum_const]
      simp
    have h3 : (((T.filter fun t => A t = -1).card : ℤ)) = (m : ℤ) := by
      have h4 := h1.symm.trans hAT
      rw [h2] at h4
      omega
    exact_mod_cast h3
  have hsumR : ∑ r ∈ R, (A r : ℂ) • r = ∑ r ∈ R.filter fun r => A r = 1, r := by
    have e1 : ∑ r ∈ R.filter fun r => A r = 1, (A r : ℂ) • r
        = ∑ r ∈ R.filter fun r => A r = 1, r :=
      Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.1 hr).2]; simp
    have e2 : ∑ r ∈ R.filter fun r => ¬ (A r = 1), (A r : ℂ) • r = 0 :=
      Finset.sum_eq_zero fun r hr => by
        obtain ⟨hr1, hr2⟩ := Finset.mem_filter.1 hr
        rcases hR01 r hr1 with h | h
        · rw [h]; simp
        · exact absurd h hr2
    rw [← Finset.sum_filter_add_sum_filter_not R fun r => A r = 1, e1, e2, add_zero]
  have hsumT : ∑ t ∈ T, (A t : ℂ) • t = -∑ t ∈ T.filter fun t => A t = -1, t := by
    have e1 : ∑ t ∈ T.filter fun t => A t = -1, (A t : ℂ) • t
        = ∑ t ∈ T.filter fun t => A t = -1, -t :=
      Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.1 ht).2]; simp
    have e2 : ∑ t ∈ T.filter fun t => ¬ (A t = -1), (A t : ℂ) • t = 0 :=
      Finset.sum_eq_zero fun t ht => by
        obtain ⟨ht1, ht2⟩ := Finset.mem_filter.1 ht
        rcases hT01 t ht1 with h | h
        · rw [h]; simp
        · exact absurd h ht2
    rw [← Finset.sum_filter_add_sum_filter_not T fun t => A t = -1, e1, e2, add_zero,
      Finset.sum_neg_distrib]
  refine ⟨R.filter fun r => A r = 1, Finset.filter_subset _ _,
    T.filter fun t => A t = -1, Finset.filter_subset _ _, hcardR, hcardT, ?_⟩
  rw [hfX, hXdef, hEdef, Finset.sum_union hRT, hsumR, hsumT, sub_eq_add_neg]

end CFSG.FeitThompson
