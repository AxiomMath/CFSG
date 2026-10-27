module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

attribute [local simp] HypPair.Q_e HypPair.Q_f HypPair.polar_ef HypPair.polar_fe
  HypPair.polar_ee HypPair.polar_ff

theorem polar_eichler_apply {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (x z : V) :
    polar Q (eichler Q u w x) z = polar Q x z + polar Q x u * polar Q w z -
      (polar Q x w + Q w * polar Q x u) * polar Q u z := by
  rw [eichler_apply hu hw, polar_sub_left, polar_add_left, polar_smul_left_eq,
    polar_smul_left_eq]

theorem exists_mem_elementaryGroup_polar_ne_zero (hQ : (polarBilin Q).Nondegenerate)
    {P P' : HypPair Q} (h : P.Orth P') {x : V} (hx : x ≠ 0) :
    ∃ g ∈ elementaryGroup Q, polar Q (g x) P.e ≠ 0 := by
  have h' := h.symm
  by_cases h1 : polar Q x P.e = 0
  swap
  · exact ⟨1, Subgroup.one_mem _, by simpa using h1⟩
  have case_f' : ∀ y : V, polar Q y P.e = 0 → polar Q y P'.f ≠ 0 →
      ∃ g ∈ elementaryGroup Q, polar Q (g y) P.e ≠ 0 := by
    intro y hye hyf'
    refine ⟨eichler Q P'.f P.f, eichler_mem_elementaryGroup Q _ _, ?_⟩
    rw [polar_eichler_apply P'.Q_f h'.ff, hye, h'.fe]
    simpa using hyf'
  by_cases h2 : polar Q x P'.e = 0
  swap
  · refine ⟨eichler Q P'.e P.f, eichler_mem_elementaryGroup Q _ _, ?_⟩
    rw [polar_eichler_apply P'.Q_e h'.ef, h1, h'.ee]
    simpa using h2
  by_cases h3 : polar Q x P'.f = 0
  swap
  · exact case_f' x h1 h3
  by_cases h4 : polar Q x P.f = 0
  swap
  · have hw : polar Q P.f (P'.e + P'.f) = 0 := by rw [polar_add_right, h.fe, h.ff, add_zero]
    refine ⟨eichler Q P.f (P'.e + P'.f), eichler_mem_elementaryGroup Q _ _, ?_⟩
    rw [polar_eichler_apply P.Q_f hw, h1, polar_add_right Q x, h2, h3, polar_add_left,
      h'.ee, h'.fe, QuadraticMap.map_add Q, P'.Q_e, P'.Q_f, P'.polar_ef]
    simpa using h4
  obtain ⟨v, hv⟩ := exists_polar_ne_zero hQ hx
  set v' := v - polar Q v P'.e • P'.f with hv'
  have he'v' : polar Q P'.e v' = 0 := by
    rw [hv', polar_sub_right, polar_smul_right_eq, P'.polar_ef, mul_one, polar_comm, sub_self]
  have hxv' : polar Q x v' = polar Q x v := by
    rw [hv', polar_sub_right, polar_smul_right_eq, h3, mul_zero, sub_zero]
  set x₁ := eichler Q P'.e v' x with hx₁
  have hx₁e : polar Q x₁ P.e = 0 := by
    rw [hx₁, polar_eichler_apply P'.Q_e he'v', h1, h2, h'.ee]
    ring
  have hx₁f' : polar Q x₁ P'.f ≠ 0 := by
    rw [hx₁, polar_eichler_apply P'.Q_e he'v', h3, h2, hxv', P'.polar_ef]
    simpa using hv
  obtain ⟨g, hg, hgx⟩ := case_f' x₁ hx₁e hx₁f'
  exact ⟨g * eichler Q P'.e v', mul_mem hg (eichler_mem_elementaryGroup Q _ _), hgx⟩

theorem exists_mem_elementaryGroup_apply_eq_of_polar_ne_zero {P P' : HypPair Q} (h : P.Orth P')
    {x y : V} (hxy : Q x = Q y) (hx : polar Q P.e x ≠ 0) (hy : polar Q P'.e y ≠ 0) :
    ∃ g ∈ elementaryGroup Q, g x = y := by
  have h' := h.symm
  set s := polar Q P.e x
  set c := polar Q P'.e y
  set z := (Q x / s) • P.e + s • P.f + c • P'.f with hz
  have hQz : Q z = Q x := by
    rw [hz, QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq,
      map_smul_eq_sq, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_left_eq, polar_smul_right_eq, P.Q_e, P.Q_f, P'.Q_f,
      P.polar_ef, h.ef, h.ff]
    field_simp
    ring
  have hez : polar Q P.e z = s := by
    rw [hz, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_smul_right_eq, P.polar_ee, P.polar_ef, h.ef]
    ring
  have he'z : polar Q P'.e z = c := by
    rw [hz, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_smul_right_eq, h'.ee, h'.ef, P'.polar_ef]
    ring
  refine ⟨eichler Q P'.e (c⁻¹ • (y - z)) * eichler Q P.e (s⁻¹ • (z - x)),
    mul_mem (eichler_mem_elementaryGroup Q _ _) (eichler_mem_elementaryGroup Q _ _), ?_⟩
  rw [LinearEquiv.mul_apply, eichler_apply_eq_of_polar_eq P.Q_e hQz.symm rfl hez hx,
    eichler_apply_eq_of_polar_eq P'.Q_e (hQz.trans hxy) he'z rfl hy]

theorem exists_mem_elementaryGroup_apply_eq (hQ : (polarBilin Q).Nondegenerate)
    {P P' : HypPair Q} (h : P.Orth P') {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Q x = Q y) :
    ∃ g ∈ elementaryGroup Q, g x = y := by
  obtain ⟨a, ha, hax⟩ := exists_mem_elementaryGroup_polar_ne_zero hQ h hx
  obtain ⟨b, hb, hby⟩ := exists_mem_elementaryGroup_polar_ne_zero hQ h.symm hy
  have hQ' : Q (a x) = Q (b y) := by
    rw [map_of_mem (elementaryGroup_le_orthogonalGroup Q ha),
      map_of_mem (elementaryGroup_le_orthogonalGroup Q hb), hxy]
  obtain ⟨c, hc, hcxy⟩ := exists_mem_elementaryGroup_apply_eq_of_polar_ne_zero h hQ'
    (by rwa [polar_comm]) (by rwa [polar_comm])
  refine ⟨b⁻¹ * c * a, mul_mem (mul_mem (inv_mem hb) hc) ha, ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hcxy, LinearEquiv.inv_apply_apply']

end CFSG.ClassicalGroups.Orthogonal
