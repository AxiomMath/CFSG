module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Const

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Closure

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem mem_of_two_term {G K : Type*} [Group G] [Field K] (H : Subgroup G) (X Y : K → G)
    (hX : ∀ a b, X (a + b) = X a * X b) (hY : ∀ a b, Y (a + b) = Y a * Y b)
    (hXY : ∀ a b, Commute (X a) (Y b)) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {C₁ C₂ : K}
    (hC₁ : C₁ * C₁ = 1) (hC₂ : C₂ * C₂ = 1)
    (h : ∀ c d : K, X (C₁ * c * d) * Y (C₂ * c * d ^ 2) ∈ H) :
    (∀ e, X e ∈ H) ∧ ∀ f, Y f ∈ H := by
  have hC₁0 : C₁ ≠ 0 := fun h0 => by simp [h0] at hC₁
  have ht1' : t - 1 ≠ 0 := sub_ne_zero.2 ht1
  have hY0 : Y 0 = 1 := by
    have h0 := hY 0 0
    rw [add_zero] at h0
    exact mul_eq_left.1 h0.symm
  have hXmem : ∀ e, X e ∈ H := by
    intro e
    obtain ⟨c₁, hc₁⟩ : ∃ c₁ : K, c₁ = e * t / (C₁ * (t - 1)) := ⟨_, rfl⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K, c₂ = -c₁ / t ^ 2 := ⟨_, rfl⟩
    have e1 : C₁ * c₁ * 1 + C₁ * c₂ * t = e := by
      rw [hc₂, hc₁]
      field_simp
      ring
    have e2 : C₂ * c₁ * 1 ^ 2 + C₂ * c₂ * t ^ 2 = 0 := by
      rw [hc₂]
      field_simp
      ring
    have h12 := H.mul_mem (h c₁ 1) (h c₂ t)
    have key : X (C₁ * c₁ * 1) * Y (C₂ * c₁ * 1 ^ 2) * (X (C₁ * c₂ * t) * Y (C₂ * c₂ * t ^ 2)) =
        X e := by
      calc X (C₁ * c₁ * 1) * Y (C₂ * c₁ * 1 ^ 2) * (X (C₁ * c₂ * t) * Y (C₂ * c₂ * t ^ 2))
          = X (C₁ * c₁ * 1) * (Y (C₂ * c₁ * 1 ^ 2) * X (C₁ * c₂ * t)) * Y (C₂ * c₂ * t ^ 2) := by
            simp only [mul_assoc]
        _ = X (C₁ * c₁ * 1) * (X (C₁ * c₂ * t) * Y (C₂ * c₁ * 1 ^ 2)) * Y (C₂ * c₂ * t ^ 2) := by
            rw [← (hXY (C₁ * c₂ * t) (C₂ * c₁ * 1 ^ 2)).eq]
        _ = X (C₁ * c₁ * 1 + C₁ * c₂ * t) * Y (C₂ * c₁ * 1 ^ 2 + C₂ * c₂ * t ^ 2) := by
            rw [hX, hY]
            simp only [mul_assoc]
        _ = X e := by rw [e1, e2, hY0, mul_one]
    rwa [key] at h12
  refine ⟨hXmem, fun f => ?_⟩
  have hf : C₂ * (C₂ * f) * 1 ^ 2 = f := by rw [← mul_assoc, hC₂]; simp
  have hx := hXmem (C₁ * (C₂ * f) * 1)
  have hy := H.mul_mem (H.inv_mem hx) (h (C₂ * f) 1)
  rw [hf, inv_mul_cancel_left] at hy
  exact hy


theorem pinnedX_mem_rootSubgroup_F4 {K : Type} [Field K] (α : Fin Tag.F4.rank → ℤ) (c : K) :
    pinnedX Tag.F4 K α c ∈ rootSubgroup Tag.F4 K α := by
  unfold rootSubgroup
  exact Subgroup.subset_closure ⟨c, rfl⟩

theorem commute_pinnedX_of_commPairs_nil {K : Type} [Field K] {v w : Fin Tag.F4.rank → ℤ}
    (hv : IsRoot .F4 v) (hw : IsRoot .F4 w) (hne : v ≠ w) (hne' : v ≠ -w)
    (h : commPairs .F4 v w = []) (c d : K) :
    Commute (pinnedX .F4 K v c) (pinnedX .F4 K w d) := by
  obtain ⟨C, -, hF⟩ := exists_pinnedX_commFormula_F4_exact hv hw hne hne'
  have h1 := hF K c d
  rw [h, List.map_nil, List.prod_nil, ← pinnedX_neg Tag.F4 K v c,
    ← pinnedX_neg Tag.F4 K w d] at h1
  exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact h1)

theorem rootSubgroup_add_le_single {K : Type} [Field K] (H : Subgroup (ModGL Tag.F4 K))
    {v w : Fin Tag.F4.rank → ℤ} (hv : IsRoot .F4 v) (hw : IsRoot .F4 w) (hne : v ≠ w)
    (hP : commPairs .F4 v w = [(1, 1)]) (hnr : ¬ IsRoot .F4 (w - v))
    (hA : rootSubgroup .F4 K v ≤ H) (hB : rootSubgroup .F4 K w ≤ H) :
    rootSubgroup .F4 K (v + w) ≤ H := by
  have hm : (1, 1) ∈ commPairs .F4 v w := by rw [hP]; simp
  have hvw : IsRoot .F4 (v + w) := by simpa using (mem_commPairs.1 hm).2
  have hne' : v ≠ -w := fun h => hvw.ne_zero (by rw [h, neg_add_cancel])
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hv hw hne hne'
  have hC1 : |C (1, 1)| = 1 := by rw [hC _ hm]; simp [hnr]
  have hsq : ((C (1, 1) : ℤ) : K) * ((C (1, 1) : ℤ) : K) = 1 := by
    rcases (abs_eq zero_le_one).1 hC1 with h | h <;> rw [h] <;> simp
  have hpin : ∀ e : K, pinnedX .F4 K (v + w) e ∈ H := by
    intro e
    have h1 := hF K 1 (((C (1, 1) : ℤ) : K) * e)
    rw [hP] at h1
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_nsmul,
      pow_one, one_pow] at h1
    rw [← mul_assoc, hsq, one_mul, ← pinnedX_neg Tag.F4 K v 1,
      ← pinnedX_neg Tag.F4 K w (((C (1, 1) : ℤ) : K) * e)] at h1
    have hx := hA (pinnedX_mem_rootSubgroup_F4 v 1)
    have hy := hB (pinnedX_mem_rootSubgroup_F4 w (((C (1, 1) : ℤ) : K) * e))
    rw [← h1]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  unfold rootSubgroup
  rw [Subgroup.closure_le]
  rintro _ ⟨e, rfl⟩
  exact hpin e

theorem rootSubgroup_add_le_double {K : Type} [Field K] {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (H : Subgroup (ModGL Tag.F4 K)) {v w : Fin Tag.F4.rank → ℤ} (hv : IsRoot .F4 v)
    (hw : IsRoot .F4 w) (hne : v ≠ w) (hP : commPairs .F4 v w = [(1, 1), (1, 2)])
    (hnr : ¬ IsRoot .F4 (w - v)) (hne₂ : v + w ≠ v + 2 • w) (hne₃ : v + w ≠ -(v + 2 • w))
    (hP₂ : commPairs .F4 (v + w) (v + 2 • w) = [])
    (hA : rootSubgroup .F4 K v ≤ H) (hB : rootSubgroup .F4 K w ≤ H) :
    rootSubgroup .F4 K (v + w) ≤ H ∧ rootSubgroup .F4 K (v + 2 • w) ≤ H := by
  have hm₁ : (1, 1) ∈ commPairs .F4 v w := by rw [hP]; simp
  have hm₂ : (1, 2) ∈ commPairs .F4 v w := by rw [hP]; simp
  have hvw : IsRoot .F4 (v + w) := by simpa using (mem_commPairs.1 hm₁).2
  have hvw₂ : IsRoot .F4 (v + 2 • w) := by simpa using (mem_commPairs.1 hm₂).2
  have hne' : v ≠ -w := fun h => hvw.ne_zero (by rw [h, neg_add_cancel])
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hv hw hne hne'
  have hC₁ : |C (1, 1)| = 1 := by rw [hC _ hm₁]; simp [hnr]
  have hC₂ : |C (1, 2)| = 1 := by rw [hC _ hm₂]; simp
  have hsq : ∀ z : ℤ, |z| = 1 → (z : K) * (z : K) = 1 := fun z hz => by
    rcases (abs_eq zero_le_one).1 hz with h | h <;> rw [h] <;> simp
  obtain ⟨hX, hY⟩ := mem_of_two_term H (pinnedX .F4 K (v + w)) (pinnedX .F4 K (v + 2 • w))
    (pinnedX_add Tag.F4 K (v + w)) (pinnedX_add Tag.F4 K (v + 2 • w))
    (fun a b => commute_pinnedX_of_commPairs_nil hvw hvw₂ hne₂ hne₃ hP₂ a b) ht0 ht1
    (hsq _ hC₁) (hsq _ hC₂) fun c d => by
    have h1 := hF K c d
    rw [hP] at h1
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_nsmul,
      pow_one] at h1
    rw [← pinnedX_neg Tag.F4 K v c, ← pinnedX_neg Tag.F4 K w d] at h1
    have hx := hA (pinnedX_mem_rootSubgroup_F4 v c)
    have hy := hB (pinnedX_mem_rootSubgroup_F4 w d)
    rw [← h1]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  constructor <;> (unfold rootSubgroup; rw [Subgroup.closure_le]; rintro _ ⟨e, rfl⟩)
  · exact hX e
  · exact hY e

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Closure
