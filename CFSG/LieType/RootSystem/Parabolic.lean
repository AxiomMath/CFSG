module

public import CFSG.LieType.RootSystem.Form
public import TauCeti.GroupTheory.Coxeter.Parabolic

public section

namespace CFSG.LieType.RootSystem

open CoxeterSystem

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem one_le_sum_of_nonneg {v : I → ℤ} (h0 : 0 ≤ v) (hne : v ≠ 0) : 1 ≤ ∑ k, v k := by
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have h1 : v m ≤ ∑ k, v k := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ m)
  have h2 : 0 ≤ v m := h0 m
  omega

theorem eq_single_of_sum_eq_one {v : I → ℤ} (h0 : 0 ≤ v) (h1 : ∑ k, v k = 1) :
    ∃ m, v = Pi.single m 1 := by
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at h1
  have hsum := Finset.add_sum_erase Finset.univ v (Finset.mem_univ m)
  have hrest : ∀ k ∈ Finset.univ.erase m, v k ≤ ∑ k ∈ Finset.univ.erase m, v k :=
    fun k hk => Finset.single_le_sum (fun k _ => h0 k) hk
  have hrest0 : 0 ≤ ∑ k ∈ Finset.univ.erase m, v k := Finset.sum_nonneg fun k _ => h0 k
  have hm0 : 0 ≤ v m := h0 m
  have hm1 : v m = 1 := by omega
  refine ⟨m, funext fun k => ?_⟩
  by_cases hk : k = m
  · subst hk
    simp [hm1]
  · have h3 := hrest k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    have h4 : 0 ≤ v k := h0 k
    rw [Pi.single_apply, ite_eq_right hk]
    omega

theorem sum_smul_single (v : I → ℤ) : ∑ m, v m • Pi.single m (1 : ℤ) = v := by
  conv_rhs => rw [← Finset.univ_sum_single v]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

omit [DecidableEq I] in
private theorem sum_sum_smul {ι : Type*} [Fintype ι] (c : ι → ℤ) (f : ι → I → ℤ) :
    ∑ k, (∑ m, c m • f m) k = ∑ m, c m * ∑ k, f m k := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem ne_zero_of_mem_roots (D : Set I) {γ : I → ℤ} (hγ : γ ∈ roots hA D) : γ ≠ 0 := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, -, rfl⟩
  · exact weylAction_single_ne_zero hA w i
  · rw [two_nsmul]
    intro h
    apply weylAction_single_ne_zero hA w i
    funext k
    have := congrFun h k
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [Pi.zero_apply]
    omega

theorem weylAction_mem_roots {D : Set I} (w : (coxeterMatrix hA).Group) {γ : I → ℤ}
    (hγ : γ ∈ roots hA D) : weylAction hA w γ ∈ roots hA D := by
  rcases hγ with ⟨w', i, rfl⟩ | ⟨w', i, hi, rfl⟩
  · exact Or.inl ⟨w * w', i, by rw [weylAction_mul_apply]⟩
  · exact Or.inr ⟨w * w', i, hi, by rw [map_nsmul, weylAction_mul_apply]⟩

omit [DecidableEq I] in
include hA in
theorem exists_pos_coroot {δ : I → ℤ} (h0 : 0 ≤ δ) (hne : δ ≠ 0) :
    ∃ k, 0 < δ k ∧ 0 < coroot A k δ := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hx : toRat δ = 0 := hA.eq_zero_of_forall_mul_sum_apply_mul_nonpos fun k => by
    have hk : δ k * coroot A k δ ≤ 0 := by
      have h0k : 0 ≤ δ k := h0 k
      rcases h0k.lt_or_eq with h | h
      · exact mul_nonpos_of_nonneg_of_nonpos h.le (hcon k h)
      · rw [← h, zero_mul]
    rw [coroot_apply] at hk
    simp only [toRat_apply]
    exact_mod_cast hk
  exact toRat_injective (by rw [hx, map_zero])

theorem eq_single_of_forall_not_isLeftDescent (J : Set I) (u : (coxeterMatrix hA).Group) (i : I)
    (hJ : ∀ j ∈ J, ¬ (coxeterMatrix hA).toCoxeterSystem.IsLeftDescent u j)
    (hsupp : ∀ k ∉ J, weylAction hA u (Pi.single i 1) k = 0) :
    ∃ m ∈ J, weylAction hA u (Pi.single i 1) = Pi.single m 1 := by
  have hpos : ∀ m ∈ J, 0 ≤ weylAction hA u⁻¹ (Pi.single m 1) := fun m hm =>
    nonneg_of_not_isRightDescent hA _ _ fun h =>
      hJ m hm ((coxeterMatrix hA).toCoxeterSystem.isRightDescent_inv_iff.mp h)
  have hback : ∑ m, weylAction hA u (Pi.single i 1) m • weylAction hA u⁻¹ (Pi.single m 1) =
      Pi.single i 1 := by
    conv_rhs => rw [← weylAction_inv_apply_apply hA u (Pi.single i 1),
      ← sum_smul_single (weylAction hA u (Pi.single i 1))]
    rw [map_sum]
    simp only [map_zsmul]
  rcases weylAction_single_nonneg_or_nonpos hA u i with h0 | h0
  ·
    have hht := congrArg (fun v : I → ℤ => ∑ k, v k) hback
    simp only [sum_sum_smul] at hht
    have h1 : ∑ k, (Pi.single i 1 : I → ℤ) k = 1 := by simp
    have hle : ∑ k, weylAction hA u (Pi.single i 1) k ≤ 1 := by
      refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hht.trans h1).le
      by_cases hm : m ∈ J
      · exact le_mul_of_one_le_right (h0 m)
          (one_le_sum_of_nonneg (hpos m hm) (weylAction_single_ne_zero hA _ _))
      · simp [hsupp m hm]
    have hge := one_le_sum_of_nonneg h0 (weylAction_single_ne_zero hA u i)
    obtain ⟨m, hm⟩ := eq_single_of_sum_eq_one h0 (le_antisymm hle hge)
    refine ⟨m, by_contra fun hmJ => ?_, hm⟩
    have := hsupp m hmJ
    rw [hm] at this
    simp at this
  ·
    exfalso
    have hle : (Pi.single i 1 : I → ℤ) ≤ 0 := by
      rw [← hback]
      refine Finset.sum_nonpos fun m _ => ?_
      by_cases hm : m ∈ J
      · exact smul_nonpos_of_nonpos_of_nonneg (h0 m) (hpos m hm)
      · simp [hsupp m hm]
    have := hle i
    simp at this

private theorem exists_parabolic_of_nonneg (J : Set I) (n : ℕ) :
    ∀ (w : (coxeterMatrix hA).Group) (i : I),
      ∑ k, weylAction hA w (Pi.single i 1) k = n → 0 ≤ weylAction hA w (Pi.single i 1) →
      (∀ k ∉ J, weylAction hA w (Pi.single i 1) k = 0) →
      ∃ z ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic J, ∃ m ∈ J,
        weylAction hA z (weylAction hA w (Pi.single i 1)) = Pi.single m 1 := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w i hn h0 hsupp
    have hne := weylAction_single_ne_zero hA w i
    obtain ⟨k, hk, hc⟩ := exists_pos_coroot hA h0 hne
    have hkJ : k ∈ J := by
      by_contra h
      have := hsupp k h
      omega
    have hge := one_le_sum_of_nonneg h0 hne
    by_cases h1 : n ≤ 1
    · obtain ⟨m, hm⟩ := eq_single_of_sum_eq_one h0 (by omega)
      refine ⟨1, one_mem _, m, by_contra fun hmJ => ?_, by rw [map_one, Module.End.one_apply, hm]⟩
      have := hsupp m hmJ
      rw [hm] at this
      simp at this
    have hδ' : weylAction hA (cs.simple k * w) (Pi.single i 1) =
        weylAction hA w (Pi.single i 1) - coroot A k (weylAction hA w (Pi.single i 1)) •
          Pi.single k 1 := by
      rw [weylAction_mul_apply, weylAction_simple, reflection_apply_coroot]
    have hht : ∑ l, weylAction hA (cs.simple k * w) (Pi.single i 1) l =
        ∑ l, weylAction hA w (Pi.single i 1) l - coroot A k (weylAction hA w (Pi.single i 1)) := by
      rw [hδ']
      simp [Finset.sum_sub_distrib, Pi.single_apply]
    have h0' : 0 ≤ weylAction hA (cs.simple k * w) (Pi.single i 1) := by
      rcases weylAction_single_nonneg_or_nonpos hA (cs.simple k * w) i with h | h
      · exact h
      exfalso
      have hsupp' : ∀ l, l ≠ k → weylAction hA w (Pi.single i 1) l = 0 := fun l hl => by
        have h2 := h l
        rw [hδ'] at h2
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hl, ite_false, smul_zero,
          sub_zero, Pi.zero_apply] at h2
        exact le_antisymm h2 (h0 l)
      have hδeq : weylAction hA w (Pi.single i 1) =
          weylAction hA w (Pi.single i 1) k • Pi.single k 1 := by
        ext l
        by_cases hl : l = k
        · subst hl
          simp
        · simp [hl, hsupp' l hl]
      have hsum1 : ∑ l, weylAction hA w (Pi.single i 1) l = weylAction hA w (Pi.single i 1) k := by
        conv_lhs => rw [hδeq]
        simp [Pi.single_apply]
      have hinv := weylAction_inv_apply_apply hA w (Pi.single i 1)
      rw [hδeq, map_zsmul] at hinv
      have hi := congrFun hinv i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at hi
      have := Int.eq_one_of_mul_eq_one_right hk.le hi
      omega
    have hsupp' : ∀ l ∉ J, weylAction hA (cs.simple k * w) (Pi.single i 1) l = 0 := fun l hl => by
      have hlk : l ≠ k := fun h => hl (h ▸ hkJ)
      rw [hδ']
      simp [hlk, hsupp l hl]
    obtain ⟨n', hn'⟩ := Int.eq_ofNat_of_zero_le (Finset.sum_nonneg fun l _ => h0' l)
    obtain ⟨z, hz, m, hm, hzm⟩ := ih n' (by omega) (cs.simple k * w) i hn' h0' hsupp'
    refine ⟨z * cs.simple k, mul_mem hz (cs.simple_mem_parabolic hkJ), m, hm, ?_⟩
    rw [weylAction_mul_apply, ← weylAction_mul_apply hA (cs.simple k), hzm]

theorem exists_parabolic_of_support (J : Set I) (w : (coxeterMatrix hA).Group) (i : I)
    (hsupp : ∀ k ∉ J, weylAction hA w (Pi.single i 1) k = 0) :
    ∃ z ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic J, ∃ m ∈ J,
      weylAction hA z (weylAction hA w (Pi.single i 1)) = Pi.single m 1 := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  rcases weylAction_single_nonneg_or_nonpos hA w i with h0 | h0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Finset.sum_nonneg fun l _ => h0 l)
    exact exists_parabolic_of_nonneg hA J n w i hn h0 hsupp
  have hneg : weylAction hA (w * cs.simple i) (Pi.single i 1) =
      -weylAction hA w (Pi.single i 1) := by
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg]
  have h0' : 0 ≤ weylAction hA (w * cs.simple i) (Pi.single i 1) := by
    rw [hneg]
    exact neg_nonneg.mpr h0
  have hsupp' : ∀ k ∉ J, weylAction hA (w * cs.simple i) (Pi.single i 1) k = 0 := by
    intro k hk
    rw [hneg, Pi.neg_apply, hsupp k hk, neg_zero]
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Finset.sum_nonneg fun l _ => h0' l)
  obtain ⟨z, hz, m, hm, hzm⟩ := exists_parabolic_of_nonneg hA J n _ i hn h0' hsupp'
  refine ⟨cs.simple m * z, mul_mem (cs.simple_mem_parabolic hm) hz, m, hm, ?_⟩
  rw [hneg, map_neg] at hzm
  rw [weylAction_mul_apply, ← neg_neg (weylAction hA z _), hzm, map_neg,
    weylAction_simple_single, neg_neg]

end CFSG.LieType.RootSystem
