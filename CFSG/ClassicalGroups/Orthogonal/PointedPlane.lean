module

public import CFSG.ClassicalGroups.Orthogonal.Transitive

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem exists_eichler_apply_fixed_mark
    {r v w : V} (hr : Q r = 1) (hv : Q v = 1) (hw : Q w = 1)
    (hrv : polar Q r v = 1) (hrw : polar Q r w = 1)
    (hβ : polar Q v w = 0 ∨ polar Q v w = 1) :
    ∃ u : V, Q u = 0 ∧ polar Q u r = 0 ∧
      eichler Q u r r = r ∧ eichler Q u r v = w + (polar Q v w) • r := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set b := polar Q v w with hb
  set u := v + w + b • r with hu
  have hβ' : b = 0 ∨ b = 1 := by simpa [hb] using hβ
  have hβ2 : b ^ 2 = b := by
    rcases hβ' with h | h <;> rw [h] <;> ring
  have hvv : polar Q v v = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hrr : polar Q r r = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hv2 : v + v = 0 := by rw [← two_smul K v, h2, zero_smul]
  have hneg_u : -u = u := by
    rw [neg_eq_iff_add_eq_zero, ← two_smul K u, h2, zero_smul]
  have huQ : Q u = 0 := by
    rw [hu, QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, hv, hw, hr,
      polar_add_left, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q v r, polar_comm Q w r, hrv, hrw]
    rw [hβ2]
    linear_combination (1 + 2 * b) * h2
  have hu_r : polar Q u r = 0 := by
    rw [hu, polar_add_left, polar_add_left, polar_smul_left_eq, hrr,
      polar_comm Q v r, polar_comm Q w r, hrv, hrw, mul_zero, add_zero]
    linear_combination h2
  have hvu : polar Q v u = 0 := by
    rw [hu, polar_add_right, polar_add_right, polar_smul_right_eq, hvv,
      polar_comm Q v r, hrv]
    linear_combination b * h2
  have hvr : polar Q v r = 1 := (polar_comm Q v r).trans hrv
  have hfix : eichler Q u r r = r :=
    eichler_apply_of_polar_eq_zero (u := u) (w := r) (x := r)
      ((polar_comm Q r u).trans hu_r) hrr
  have hmove : eichler Q u r v = w + b • r := by
    rw [eichler_apply huQ hu_r v]
    simp only [hvu, hvr, hr, zero_smul, smul_zero, add_zero, mul_zero, one_mul, one_smul]
    rw [sub_eq_add_neg, hneg_u]
    calc
      v + u = v + (v + w + b • r) := by rw [hu]
      _ = (v + v) + (w + b • r) := by abel
      _ = w + b • r := by rw [hv2, zero_add]
  exact ⟨u, huQ, hu_r, hfix, hmove⟩

theorem exists_mem_elementaryGroup_apply_pair_or_add
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    {P P' : HypPair Q} (hP : P.Orth P')
    {r v r' w : V}
    (hr : Q r = 1) (hv : Q v = 1)
    (hr' : Q r' = 1) (hw : Q w = 1)
    (hrv : polar Q r v = 1) (hrw : polar Q r' w = 1) :
    ∃ g ∈ elementaryGroup Q, g r = r' ∧ (g v = w ∨ g v = w + r') := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero Q] at hr
    exact zero_ne_one hr
  have hr'0 : r' ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero Q] at hr'
    exact zero_ne_one hr'
  obtain ⟨a, ha, har⟩ :=
    exists_mem_elementaryGroup_apply_eq hQ hP hr0 hr'0 (hr.trans hr'.symm)
  set v₁ := a v with hv₁
  have hQv₁ : Q v₁ = 1 := by
    rw [hv₁, map_of_mem (elementaryGroup_le_orthogonalGroup Q ha) v, hv]
  have hrv₁ : polar Q r' v₁ = 1 := by
    rw [hv₁, ← har, polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q ha) r v, hrv]
  have hβ : polar Q v₁ w = 0 ∨ polar Q v₁ w = 1 := by
    by_cases h0 : polar Q v₁ w = 0
    · exact Or.inl h0
    · right
      obtain ⟨y, _hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
      have hy1 : y = 1 := (huniq 1 one_ne_zero).symm
      exact (huniq (polar Q v₁ w) h0).trans hy1
  obtain ⟨u, huQ, hu_r', hfix, hmove⟩ :=
    exists_eichler_apply_fixed_mark (r := r') (v := v₁) (w := w)
      hr' hQv₁ hw hrv₁ hrw hβ
  refine ⟨eichler Q u r' * a, mul_mem (eichler_mem_elementaryGroup Q u r') ha, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, har, hfix]
  · rw [LinearEquiv.mul_apply, ← hv₁]
    rcases hβ with h0 | h1
    · left
      rw [hmove, h0, zero_smul, add_zero]
    · right
      rw [hmove, h1, one_smul]

theorem exists_mem_elementaryGroup_apply_span_pair
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    {P P' : HypPair Q} (hP : P.Orth P')
    {r v r' w : V}
    (hr : Q r = 1) (hv : Q v = 1)
    (hr' : Q r' = 1) (hw : Q w = 1)
    (hrv : polar Q r v = 1) (hrw : polar Q r' w = 1) :
    ∃ g ∈ elementaryGroup Q, g r = r' ∧
      (Submodule.span K {r, v}).map (g : V →ₗ[K] V) = Submodule.span K {r', w} := by
  obtain ⟨g, hg, hgr, hgv⟩ :=
    exists_mem_elementaryGroup_apply_pair_or_add hK hQ hP hr hv hr' hw hrv hrw
  have hgr' : (g : V →ₗ[K] V) r = r' := hgr
  have hgv' : (g : V →ₗ[K] V) v = w ∨ (g : V →ₗ[K] V) v = w + r' := hgv
  refine ⟨g, hg, hgr, ?_⟩
  rw [Submodule.map_span, Set.image_pair, hgr']
  rcases hgv' with h | h
  · simpa [h]
  · rw [h]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · refine Submodule.mem_span_pair.mpr ⟨1, 1, ?_⟩
        rw [one_smul, one_smul]
        abel
    · rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · refine Submodule.mem_span_pair.mpr ⟨-1, 1, ?_⟩
        rw [neg_one_smul, one_smul]
        abel

end CFSG.ClassicalGroups.Orthogonal
