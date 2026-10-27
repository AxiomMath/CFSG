module

public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

@[expose] def eichlerLin (u w : V) : V →ₗ[K] V where
  toFun x := x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u
  map_add' x y := by
    simp only [polar_add_left, add_smul, mul_add]
    abel
  map_smul' c x := by
    simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply]
    module

theorem eichlerLin_apply (u w x : V) :
    eichlerLin Q u w x = x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u :=
  rfl

theorem eichlerLin_zero_right (u x : V) : eichlerLin Q u 0 x = x := by
  simp [eichlerLin_apply]

variable {Q} in
theorem eichlerLin_comp {u v w : V} (hu : Q u = 0) (hv : polar Q u v = 0)
    (hw : polar Q u w = 0) (x : V) :
    eichlerLin Q u v (eichlerLin Q u w x) = eichlerLin Q u (v + w) x := by
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have hwu : polar Q w u = 0 := by rw [polar_comm, hw]
  simp only [eichlerLin_apply, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul,
    hwu, huu, hv, mul_zero, sub_zero, add_zero]
  rw [QuadraticMap.map_add Q v w, polar_add_right, polar_comm Q w v]
  module

variable {Q} in
theorem map_eichlerLin {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (x : V) :
    Q (eichlerLin Q u w x) = Q x := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, hw]
  rw [eichlerLin_apply, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q,
    QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, hu]
  simp only [polar_add_left, polar_smul_left, polar_smul_right, smul_eq_mul, hwu]
  ring

noncomputable def eichler (u w : V) : V ≃ₗ[K] V :=
  open scoped Classical in
  if h : Q u = 0 ∧ polar Q u w = 0 then
    LinearEquiv.ofLinearMap (eichlerLin Q u w) (eichlerLin Q u (-w))
      (LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, eichlerLin_comp h.1 h.2 (by rw [polar_neg_right, h.2, neg_zero]),
          add_neg_cancel, eichlerLin_zero_right, LinearMap.id_apply])
      (LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, eichlerLin_comp h.1 (by rw [polar_neg_right, h.2, neg_zero]) h.2,
          neg_add_cancel, eichlerLin_zero_right, LinearMap.id_apply])
  else 1

variable {Q}

theorem eichler_apply {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (x : V) :
    eichler Q u w x = x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u := by
  rw [eichler, dite_eq_left ⟨hu, hw⟩]
  rfl

theorem eichler_of_not {u w : V} (h : ¬(Q u = 0 ∧ polar Q u w = 0)) : eichler Q u w = 1 := by
  rw [eichler, dite_eq_right h]

theorem eichler_of_map_ne_zero {u : V} (hu : Q u ≠ 0) (w : V) : eichler Q u w = 1 :=
  eichler_of_not fun h => hu h.1

theorem eichler_of_polar_ne_zero {u w : V} (hw : polar Q u w ≠ 0) : eichler Q u w = 1 :=
  eichler_of_not fun h => hw h.2

variable (Q) in
theorem eichler_zero_right (u : V) : eichler Q u 0 = 1 := by
  by_cases hu : Q u = 0
  · exact LinearEquiv.ext fun x => by
      rw [eichler_apply hu (polar_zero_right Q u)]
      simp
  · exact eichler_of_map_ne_zero hu 0

variable (Q) in
theorem eichler_zero_left (w : V) : eichler Q 0 w = 1 :=
  LinearEquiv.ext fun x => by
    rw [eichler_apply (QuadraticMap.map_zero Q) (polar_zero_left Q w)]
    simp

variable (Q) in
theorem eichler_mem_orthogonalGroup (u w : V) :
    eichler Q u w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    rw [eichler_apply h.1 h.2]
    exact map_eichlerLin h.1 h.2 x
  · rw [eichler_of_not h]
    exact Subgroup.one_mem _

theorem eichler_mul {u v w : V} (hv : polar Q u v = 0) (hw : polar Q u w = 0) :
    eichler Q u v * eichler Q u w = eichler Q u (v + w) := by
  by_cases hu : Q u = 0
  · have hvw : polar Q u (v + w) = 0 := by rw [polar_add_right, hv, hw, add_zero]
    exact LinearEquiv.ext fun x => by
      rw [LinearEquiv.mul_apply, eichler_apply hu hv, eichler_apply hu hw, eichler_apply hu hvw]
      exact eichlerLin_comp hu hv hw x
  · rw [eichler_of_map_ne_zero hu, eichler_of_map_ne_zero hu, eichler_of_map_ne_zero hu, mul_one]

theorem eichler_inv {u w : V} (hw : polar Q u w = 0) :
    (eichler Q u w)⁻¹ = eichler Q u (-w) := by
  rw [inv_eq_iff_mul_eq_one, eichler_mul hw (by rw [polar_neg_right, hw, neg_zero]),
    add_neg_cancel, eichler_zero_right]

theorem eichler_apply_self (u w : V) : eichler Q u w u = u := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply h.1 h.2, polar_self_eq_zero h.1, h.2]
    simp
  · rw [eichler_of_not h]
    rfl

theorem eichler_apply_smul_self (u w : V) (c : K) : eichler Q u w (c • u) = c • u := by
  rw [map_smul, eichler_apply_self]

theorem eichler_apply_of_polar_eq_zero {u w x : V} (hxu : polar Q x u = 0)
    (hxw : polar Q x w = 0) : eichler Q u w x = x := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply h.1 h.2, hxu, hxw]
    simp
  · rw [eichler_of_not h]
    rfl

theorem eichler_apply_eq_add (u w x : V) :
    ∃ a b : K, eichler Q u w x = x + a • w + b • u := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · refine ⟨polar Q x u, -(polar Q x w + Q w * polar Q x u), ?_⟩
    rw [eichler_apply h.1 h.2, neg_smul, sub_eq_add_neg]
  · exact ⟨0, 0, by rw [eichler_of_not h]; simp⟩

theorem eichler_conj {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (u w : V) : g * eichler Q u w * g⁻¹ = eichler Q (g u) (g w) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hgu : Q (g u) = 0 := by rw [map_of_mem hg, h.1]
    have hgw : polar Q (g u) (g w) = 0 := by rw [polar_map_of_mem hg, h.2]
    refine LinearEquiv.ext fun x => ?_
    have hx : ∀ y, polar Q (g⁻¹ x) y = polar Q x (g y) := fun y => by
      rw [← polar_map_of_mem hg, LinearEquiv.apply_inv_apply']
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_apply h.1 h.2, eichler_apply hgu hgw,
      map_sub, map_add, map_smul, map_smul, LinearEquiv.apply_inv_apply', hx, hx, map_of_mem hg]
  · have h' : ¬(Q (g u) = 0 ∧ polar Q (g u) (g w) = 0) := by
      rwa [map_of_mem hg, polar_map_of_mem hg]
    rw [eichler_of_not h, eichler_of_not h', mul_one, mul_inv_cancel]

theorem eichler_add_smul_self {u : V} (hu : Q u = 0) (w : V) (c : K) :
    eichler Q u (w + c • u) = eichler Q u w := by
  have hpol : polar Q u (w + c • u) = polar Q u w := by
    rw [polar_add_right, polar_smul_right_eq, polar_self_eq_zero hu, mul_zero, add_zero]
  by_cases hw : polar Q u w = 0
  · refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply hu (hpol.trans hw), eichler_apply hu hw]
    have hQ : Q (w + c • u) = Q w := by
      rw [QuadraticMap.map_add Q, map_smul_eq_sq, hu, polar_smul_right_eq, polar_comm, hw]
      ring
    rw [hQ, polar_add_right, polar_smul_right_eq]
    module
  · rw [eichler_of_polar_ne_zero hw, eichler_of_polar_ne_zero (by rwa [hpol])]

theorem eichler_smul_left (c : K) (u w : V) : eichler Q (c • u) w = eichler Q u (c • w) := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, zero_smul, eichler_zero_left, eichler_zero_right]
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h1 : Q (c • u) = 0 := by rw [map_smul_eq_sq, h.1, mul_zero]
    have h2 : polar Q (c • u) w = 0 := by rw [polar_smul_left_eq, h.2, mul_zero]
    have h3 : polar Q u (c • w) = 0 := by rw [polar_smul_right_eq, h.2, mul_zero]
    refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply h1 h2, eichler_apply h.1 h3, polar_smul_right_eq, polar_smul_right_eq,
      map_smul_eq_sq]
    module
  · have h' : ¬(Q (c • u) = 0 ∧ polar Q (c • u) w = 0) := by
      rwa [map_smul_eq_sq, polar_smul_left_eq, mul_eq_zero, mul_eq_zero,
        or_iff_right (pow_ne_zero 2 hc), or_iff_right hc]
    have h'' : ¬(Q u = 0 ∧ polar Q u (c • w) = 0) := by
      rwa [polar_smul_right_eq, mul_eq_zero, or_iff_right hc]
    rw [eichler_of_not h', eichler_of_not h'']

theorem eichler_apply_eq_of_polar_eq {u x y : V} (hu : Q u = 0) (hxy : Q x = Q y) {t : K}
    (hx : polar Q u x = t) (hy : polar Q u y = t) (ht : t ≠ 0) :
    eichler Q u (t⁻¹ • (y - x)) x = y := by
  have hw : polar Q u (t⁻¹ • (y - x)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hx, hy, sub_self, mul_zero]
  rw [eichler_apply hu hw, polar_comm Q x u, hx, polar_smul_right_eq, polar_sub_right,
    map_smul_eq_sq, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hQ : Q (y - x) = 2 * Q x - polar Q x y := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, ← hxy,
      polar_comm]
    ring
  rw [hQ, polar_self_eq_two_mul]
  have : t⁻¹ * (polar Q x y - 2 * Q x) + t⁻¹ ^ 2 * (2 * Q x - polar Q x y) * t = 0 := by
    field_simp
    ring
  rw [this, zero_smul, sub_zero]
  abel

variable (Q) in
@[expose] def elementaryGroup : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g | ∃ u w, Q u = 0 ∧ polar Q u w = 0 ∧ eichler Q u w = g}

variable (Q) in
theorem eichler_mem_elementaryGroup (u w : V) : eichler Q u w ∈ elementaryGroup Q := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · exact Subgroup.subset_closure ⟨u, w, h.1, h.2, rfl⟩
  · rw [eichler_of_not h]
    exact Subgroup.one_mem _

variable (Q) in
theorem elementaryGroup_le_orthogonalGroup :
    elementaryGroup Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨u, w, -, -, rfl⟩
  exact eichler_mem_orthogonalGroup Q u w

theorem elementaryGroup_le_of_eichler_mem {H : Subgroup (V ≃ₗ[K] V)}
    (hH : ∀ u w, Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ H) : elementaryGroup Q ≤ H := by
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, rfl⟩
  exact hH u w hu hw

theorem conj_mem_elementaryGroup {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x : V ≃ₗ[K] V}
    (hx : x ∈ elementaryGroup Q) : g * x * g⁻¹ ∈ elementaryGroup Q := by
  have hle : elementaryGroup Q ≤ (elementaryGroup Q).comap (MulAut.conj g).toMonoidHom := by
    apply elementaryGroup_le_of_eichler_mem
    intro u w _ _
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, eichler_conj hg]
    exact eichler_mem_elementaryGroup Q _ _
  exact hle hx

variable (Q) in
theorem elementaryGroup_subgroupOf_normal :
    ((elementaryGroup Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (elementaryGroup_le_orthogonalGroup Q)]
  intro h k hh hk
  exact conj_mem_elementaryGroup hk hh

variable (Q) in
def rootGroup (u : V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∃ w, polar Q u w = 0 ∧ eichler Q u w = g}
  one_mem' := ⟨0, polar_zero_right Q u, eichler_zero_right Q u⟩
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, by rw [polar_add_right, hv, hw, add_zero], (eichler_mul hv hw).symm⟩
  inv_mem' := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨-w, by rw [polar_neg_right, hw, neg_zero], (eichler_inv hw).symm⟩

theorem mem_rootGroup {u : V} {g : V ≃ₗ[K] V} :
    g ∈ rootGroup Q u ↔ ∃ w, polar Q u w = 0 ∧ eichler Q u w = g :=
  Iff.rfl

theorem eichler_mem_rootGroup {u w : V} (hw : polar Q u w = 0) : eichler Q u w ∈ rootGroup Q u :=
  ⟨w, hw, rfl⟩

variable (Q) in
theorem rootGroup_le_elementaryGroup (u : V) : rootGroup Q u ≤ elementaryGroup Q := by
  rintro _ ⟨w, -, rfl⟩
  exact eichler_mem_elementaryGroup Q u w

theorem rootGroup_commute {u : V} {a b : V ≃ₗ[K] V} (ha : a ∈ rootGroup Q u)
    (hb : b ∈ rootGroup Q u) : a * b = b * a := by
  obtain ⟨v, hv, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hb
  rw [eichler_mul hv hw, eichler_mul hw hv, add_comm]

theorem conj_mem_rootGroup {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u : V} {x : V ≃ₗ[K] V} (hx : x ∈ rootGroup Q u) : g * x * g⁻¹ ∈ rootGroup Q (g u) := by
  obtain ⟨w, hw, rfl⟩ := hx
  rw [eichler_conj hg]
  exact ⟨g w, by rw [polar_map_of_mem hg, hw], rfl⟩

theorem conj_mem_rootGroup_of_apply_eq_smul {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u : V} {c : K} (hgu : g u = c • u)
    {x : V ≃ₗ[K] V} (hx : x ∈ rootGroup Q u) : g * x * g⁻¹ ∈ rootGroup Q u := by
  obtain ⟨w, hw, rfl⟩ := hx
  rw [eichler_conj hg, hgu, eichler_smul_left]
  refine ⟨c • g w, ?_, rfl⟩
  rw [polar_smul_right_eq, ← polar_smul_left_eq, ← hgu, polar_map_of_mem hg, hw]

end CFSG.ClassicalGroups.Orthogonal
