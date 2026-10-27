module

public import CFSG.LieType.BorelTits.OrthogonalForm

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

namespace QuadForm

variable (Φ : QuadForm K V)

theorem polar_smul_left (c : K) (u v : V) : Φ.polar.β (c • u) v = c * Φ.polar.β u v := by
  rw [Φ.polar.smul_left, Φ.polar_σ, RingEquiv.refl_apply]

theorem Q_eq_zero_of_polar_self (h2 : (2 : K) ≠ 0) {v : V} (hv : Φ.polar.β v v = 0) :
    Φ.Q v = 0 := by
  rw [Φ.polar_self] at hv
  exact (mul_eq_zero.mp hv).resolve_left h2

theorem exists_mem_Q_ne_zero {W : Submodule K V} (hW : ¬Φ.polar.IsTotallyIsotropic W) :
    ∃ w ∈ W, Φ.Q w ≠ 0 := by
  obtain ⟨u, hu, hu'⟩ := IsConcreteLE.not_le_iff_exists.mp hW
  obtain ⟨v, hv, hvu⟩ : ∃ v ∈ W, Φ.polar.β v u ≠ 0 := by
    by_contra! h
    exact hu' h
  by_cases hQu : Φ.Q u = 0
  · by_cases hQv : Φ.Q v = 0
    · refine ⟨v + u, add_mem hv hu, ?_⟩
      rwa [Φ.Q_add, hQu, hQv, zero_add, zero_add]
    · exact ⟨v, hv, hQv⟩
  · exact ⟨u, hu, hQu⟩

theorem exists_polar_eq_zero_Q_ne_zero [FiniteDimensional K V] (hd : 3 ≤ Module.finrank K V)
    (x : V) : ∃ w, Φ.polar.β x w = 0 ∧ Φ.Q w ≠ 0 := by
  obtain ⟨w, hw, hQw⟩ := Φ.exists_mem_Q_ne_zero (W := Φ.polar.perp (K ∙ x)) fun h => by
    have h1 : Φ.polar.perp (K ∙ x) ≤ K ∙ x := by
      have := h
      rwa [ReflForm.IsTotallyIsotropic, Φ.polar.perp_perp] at this
    have h2 := Submodule.finrank_mono h1
    have h3 := Φ.polar.finrank_perp (K ∙ x)
    have h4 : Module.finrank K (K ∙ x) ≤ 1 := (finrank_span_le_card ({x} : Set V)).trans (by simp)
    omega
  exact ⟨w, Φ.polar.mem_perp_span_singleton.mp hw, hQw⟩

@[expose] def eichler (x y : V) : V →ₗ[K] V where
  toFun v := v + Φ.polar.β x v • (y - Φ.Q y • x) - Φ.polar.β y v • x
  map_add' u v := by
    simp only [Φ.polar.add_right, add_smul]
    abel
  map_smul' c v := by
    simp only [Φ.polar.smul_right, mul_smul, RingHom.id_apply, smul_add, smul_sub]

theorem eichler_apply (x y v : V) :
    Φ.eichler x y v = v + Φ.polar.β x v • (y - Φ.Q y • x) - Φ.polar.β y v • x :=
  rfl

theorem Q_eichler {x y : V} (hx : Φ.Q x = 0) (hxy : Φ.polar.β x y = 0) (v : V) :
    Φ.Q (Φ.eichler x y v) = Φ.Q v := by
  have hyx : Φ.polar.β y x = 0 := by rw [Φ.polar_symm, hxy]
  have h : Φ.eichler x y v = v + (Φ.polar.β x v • y +
      (-(Φ.polar.β x v * Φ.Q y) - Φ.polar.β y v) • x) := by
    rw [eichler_apply]
    module
  rw [h, Φ.Q_add, Φ.Q_add, Φ.Q_smul, Φ.Q_smul, hx]
  simp only [Φ.polar.add_right, Φ.polar.smul_right, Φ.polar_smul_left, hyx]
  rw [Φ.polar_symm v y, Φ.polar_symm v x]
  ring

theorem eichler_zero_right (x v : V) : Φ.eichler x 0 v = v := by
  rw [eichler_apply, Φ.Q_zero, zero_smul, sub_zero, smul_zero, add_zero, Φ.polar.β_zero_left,
    zero_smul, sub_zero]

theorem eichler_eichler {x y₁ y₂ : V} (hx : Φ.Q x = 0) (hxy₁ : Φ.polar.β x y₁ = 0)
    (hxy₂ : Φ.polar.β x y₂ = 0) (v : V) :
    Φ.eichler x y₁ (Φ.eichler x y₂ v) = Φ.eichler x (y₁ + y₂) v := by
  have hxx : Φ.polar.β x x = 0 := by rw [Φ.polar_self, hx, mul_zero]
  have hy₁x : Φ.polar.β y₁ x = 0 := by rw [Φ.polar_symm, hxy₁]
  have h1 : Φ.polar.β x (Φ.eichler x y₂ v) = Φ.polar.β x v := by
    rw [eichler_apply, Φ.polar.β_sub_right, Φ.polar.add_right, Φ.polar.smul_right,
      Φ.polar.smul_right, Φ.polar.β_sub_right, Φ.polar.smul_right, hxx, hxy₂]
    ring
  have h2 : Φ.polar.β y₁ (Φ.eichler x y₂ v) =
      Φ.polar.β y₁ v + Φ.polar.β x v * Φ.polar.β y₁ y₂ := by
    rw [eichler_apply, Φ.polar.β_sub_right, Φ.polar.add_right, Φ.polar.smul_right,
      Φ.polar.smul_right, Φ.polar.β_sub_right, Φ.polar.smul_right, hy₁x]
    ring
  rw [Φ.eichler_apply x y₁ (Φ.eichler x y₂ v), h1, h2, Φ.eichler_apply x y₂ v,
    Φ.eichler_apply x (y₁ + y₂) v, Φ.Q_add, Φ.polar.add_left]
  module

theorem apply_eichler_apply {g g' : V →ₗ[K] V} (hgg' : ∀ v, g (g' v) = v)
    (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (x y v : V) :
    g (Φ.eichler x y (g' v)) = Φ.eichler (g x) (g y) v := by
  have hβ : ∀ u, Φ.polar.β u (g' v) = Φ.polar.β (g u) v := fun u => by
    rw [← Φ.polar_map_of_Q hg u (g' v), hgg']
  rw [eichler_apply, eichler_apply, map_sub, map_add, map_smul, map_smul, map_sub, map_smul, hgg',
    hβ, hβ, hg]

@[expose] noncomputable def reflect (w : V) : V →ₗ[K] V where
  toFun v := v - (Φ.polar.β w v / Φ.Q w) • w
  map_add' u v := by
    simp only [Φ.polar.add_right, add_div, add_smul]
    abel
  map_smul' c v := by
    simp only [Φ.polar.smul_right, mul_div_assoc, mul_smul, RingHom.id_apply, smul_sub]

theorem reflect_apply (w v : V) : Φ.reflect w v = v - (Φ.polar.β w v / Φ.Q w) • w :=
  rfl

theorem reflect_apply_of_polar_eq_zero {w v : V} (h : Φ.polar.β w v = 0) : Φ.reflect w v = v := by
  rw [reflect_apply, h, zero_div, zero_smul, sub_zero]

theorem reflect_smul_self {w : V} (hw : Φ.Q w ≠ 0) (c : K) : Φ.reflect w (c • w) = -(c • w) := by
  rw [reflect_apply, Φ.polar.smul_right, Φ.polar_self,
    show c * (2 * Φ.Q w) / Φ.Q w = 2 * c by field_simp]
  module

theorem Q_reflect (w v : V) : Φ.Q (Φ.reflect w v) = Φ.Q v := by
  by_cases hw : Φ.Q w = 0
  · rw [reflect_apply, hw, div_zero, zero_smul, sub_zero]
  · rw [reflect_apply, sub_eq_add_neg, ← neg_smul, Φ.Q_add, Φ.Q_smul, Φ.polar.smul_right,
      Φ.polar_symm v w]
    field_simp
    ring

theorem reflect_reflect {w : V} (hw : Φ.Q w ≠ 0) (v : V) : Φ.reflect w (Φ.reflect w v) = v := by
  have h : Φ.polar.β w (Φ.reflect w v) = -Φ.polar.β w v := by
    rw [reflect_apply, Φ.polar.β_sub_right, Φ.polar.smul_right, Φ.polar_self]
    field_simp
    ring
  rw [Φ.reflect_apply w (Φ.reflect w v), h, neg_div, neg_smul, sub_neg_eq_add, reflect_apply,
    sub_add_cancel]

theorem det_reflect [FiniteDimensional K V] {w : V} (hw : Φ.Q w ≠ 0) :
    LinearMap.det (Φ.reflect w) = -1 := by
  set W := Φ.polar.perp (K ∙ w)
  have hfix : ∀ v ∈ W, Φ.reflect w v = v := fun v hv =>
    Φ.reflect_apply_of_polar_eq_zero (Φ.polar.mem_perp_span_singleton.mp hv)
  have hW : W ≤ W.comap (Φ.reflect w) := fun v hv => by
    rw [Submodule.mem_comap, hfix v hv]
    exact hv
  have hres : (Φ.reflect w).restrict hW = LinearMap.id :=
    LinearMap.ext fun v => Subtype.ext (hfix v v.2)
  have hquot : W.mapQ W (Φ.reflect w) hW = (-1 : K) • LinearMap.id := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    rw [Φ.polar.mem_perp_span_singleton, Φ.polar.β_sub_right, reflect_apply, Φ.polar.β_sub_right,
      Φ.polar.smul_right, Φ.polar.smul_right, Φ.polar_self]
    field_simp
    ring
  have hw0 : w ≠ 0 := fun h => hw (h ▸ Φ.Q_zero)
  have hfin : Module.finrank K (V ⧸ W) = 1 := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank K W + Module.finrank K (K ∙ w) = Module.finrank K V :=
      Φ.polar.finrank_perp (K ∙ w)
    rw [finrank_span_singleton hw0] at h2
    omega
  rw [LinearMap.det_eq_det_mul_det W _ hW, hres, hquot, LinearMap.det_id, LinearMap.det_smul,
    LinearMap.det_id, hfin]
  ring

end QuadForm

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K' : Type} [Field K']

theorem exists_mem_orthGroup_mulVec (Q : (ι → K') → K') (f g : (ι → K') →ₗ[K'] (ι → K'))
    (hfg : ∀ v, f (g v) = v) (hgf : ∀ v, g (f v) = v) (hQ : ∀ v, Q (f v) = Q v) :
    ∃ A ∈ orthGroup Q, (∀ v, (A : Matrix ι ι K') *ᵥ v = f v) ∧
      ∀ v, ((A⁻¹ : GL ι K') : Matrix ι ι K') *ᵥ v = g v := by
  have h1 : LinearMap.toMatrix' f * LinearMap.toMatrix' g = 1 := by
    rw [← LinearMap.toMatrix'_comp, show f ∘ₗ g = LinearMap.id from LinearMap.ext hfg,
      LinearMap.toMatrix'_id]
  have h2 : LinearMap.toMatrix' g * LinearMap.toMatrix' f = 1 := by
    rw [← LinearMap.toMatrix'_comp, show g ∘ₗ f = LinearMap.id from LinearMap.ext hgf,
      LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, h1, h2⟩,
    Subgroup.subset_closure fun v => ?_, fun v => LinearMap.toMatrix'_mulVec f v,
    fun v => LinearMap.toMatrix'_mulVec g v⟩
  change Q (LinearMap.toMatrix' f *ᵥ v) = Q v
  rw [LinearMap.toMatrix'_mulVec, hQ]

theorem det_eq_one_of_mem_statedOmega (Q : (ι → K') → K') {A : GL ι K'}
    (hA : A ∈ StatedOmega Q) : (A : Matrix ι ι K').det = 1 := by
  have hle : StatedOmega Q ≤ (Matrix.GeneralLinearGroup.det : GL ι K' →* K'ˣ).ker :=
    Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
  have h := hle hA
  rw [MonoidHom.mem_ker] at h
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

variable (Φ : QuadForm K' (ι → K')) (h2 : (2 : K') ≠ 0)

include h2 in
theorem exists_mem_statedOmega_eichler_smul {x w : ι → K'} (hx : Φ.Q x = 0)
    (hxw : Φ.polar.β x w = 0) (hw : Φ.Q w ≠ 0) (ν : K') :
    ∃ A ∈ StatedOmega Φ.Q, ∀ v, (A : Matrix ι ι K') *ᵥ v = Φ.eichler x (ν • w) v := by
  have hwx : Φ.polar.β w x = 0 := by rw [Φ.polar_symm, hxw]
  have hxs : ∀ c : K', Φ.polar.β x (c • w) = 0 := fun c => by
    rw [Φ.polar.smul_right, hxw, mul_zero]
  have hinv : ∀ c : K', ∀ v, Φ.eichler x (c • w) (Φ.eichler x ((-c) • w) v) = v := fun c v => by
    rw [Φ.eichler_eichler hx (hxs c) (hxs (-c)), ← add_smul, add_neg_cancel, zero_smul,
      Φ.eichler_zero_right]
  obtain ⟨c, hc⟩ : ∃ c : K', -c + -c = ν := ⟨-ν / 2, by field_simp; ring⟩
  obtain ⟨R, hR, hRv, hRinv⟩ := exists_mem_orthGroup_mulVec Φ.Q (Φ.reflect w) (Φ.reflect w)
    (Φ.reflect_reflect hw) (Φ.reflect_reflect hw) (Φ.Q_reflect w)
  obtain ⟨G, hG, hGv, hGinv⟩ := exists_mem_orthGroup_mulVec Φ.Q (Φ.eichler x (c • w))
    (Φ.eichler x ((-c) • w)) (hinv c) (fun v => by simpa only [neg_neg] using hinv (-c) v)
    (Φ.Q_eichler hx (hxs c))
  refine ⟨⁅R, G⁆, Subgroup.commutator_mem_commutator hR hG, fun v => ?_⟩
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
    ← mulVec_mulVec, ← mulVec_mulVec, hGinv, hRinv, hGv, hRv,
    Φ.apply_eichler_apply (Φ.reflect_reflect hw) (Φ.Q_reflect w),
    Φ.reflect_apply_of_polar_eq_zero hwx, Φ.reflect_smul_self hw, ← neg_smul,
    Φ.eichler_eichler hx (hxs _) (hxs _), ← add_smul, hc]

include h2 in
theorem exists_mem_statedOmega_eichler_of_perp {x w₀ : ι → K'} (hx : Φ.Q x = 0)
    (hxw₀ : Φ.polar.β x w₀ = 0) (hw₀ : Φ.Q w₀ ≠ 0) {y : ι → K'} (hxy : Φ.polar.β x y = 0) :
    ∃ A ∈ StatedOmega Φ.Q, ∀ v, (A : Matrix ι ι K') *ᵥ v = Φ.eichler x y v := by
  by_cases hy : Φ.Q y = 0
  ·
    obtain ⟨t, ht⟩ : ∃ t : K', Φ.Q (y + t • w₀) ≠ 0 := by
      by_contra! h
      have h1 := h 1
      have h1' := h (-1)
      rw [Φ.Q_add, Φ.Q_smul, Φ.polar.smul_right, hy] at h1 h1'
      exact hw₀ ((mul_eq_zero.mp (by linear_combination h1 + h1' :
        (2 : K') * Φ.Q w₀ = 0)).resolve_left h2)
    have hxt : Φ.polar.β x (y + t • w₀) = 0 := by
      rw [Φ.polar.add_right, Φ.polar.smul_right, hxy, hxw₀, mul_zero, add_zero]
    have hxt' : Φ.polar.β x ((-t) • w₀) = 0 := by rw [Φ.polar.smul_right, hxw₀, mul_zero]
    obtain ⟨A₁, hA₁, hA₁v⟩ := exists_mem_statedOmega_eichler_smul Φ h2 hx hxt ht 1
    obtain ⟨A₂, hA₂, hA₂v⟩ := exists_mem_statedOmega_eichler_smul Φ h2 hx hxw₀ hw₀ (-t)
    refine ⟨A₁ * A₂, mul_mem hA₁ hA₂, fun v => ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, hA₂v, hA₁v,
      Φ.eichler_eichler hx (by rwa [one_smul]) hxt',
      show (1 : K') • (y + t • w₀) + (-t) • w₀ = y by module]
  · obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler_smul Φ h2 hx hxy hy 1
    exact ⟨A, hA, fun v => by rw [hAv, one_smul]⟩

include h2 in
theorem exists_mem_statedOmega_eichler (hι : 3 ≤ Fintype.card ι) {x y : ι → K'}
    (hx : Φ.Q x = 0) (hxy : Φ.polar.β x y = 0) :
    ∃ A ∈ StatedOmega Φ.Q, ∀ v, (A : Matrix ι ι K') *ᵥ v = Φ.eichler x y v := by
  obtain ⟨w₀, hxw₀, hw₀⟩ :=
    Φ.exists_polar_eq_zero_Q_ne_zero (by rwa [Module.finrank_fintype_fun_eq_card]) x
  exact exists_mem_statedOmega_eichler_of_perp Φ h2 hx hxw₀ hw₀ hxy

theorem exists_mem_statedOmega_eichler_smul' {x w : ι → K'} (hx : Φ.Q x = 0)
    (hxw : Φ.polar.β x w = 0) (hw : Φ.Q w ≠ 0) (ν : K') :
    ∃ A ∈ StatedOmega Φ.Q, ∀ v, (A : Matrix ι ι K') *ᵥ v = Φ.eichler x (ν • w) v := by
  have hwx : Φ.polar.β w x = 0 := by rw [Φ.polar_symm, hxw]
  obtain ⟨u, hxu, hwu⟩ : ∃ u, Φ.polar.β x u = 0 ∧ Φ.polar.β w u ≠ 0 := by
    by_contra! h
    have hmem : w ∈ Φ.polar.perp (Φ.polar.perp (K' ∙ x)) := fun u hu => by
      rw [Φ.polar_symm]
      exact h u (Φ.polar.mem_perp_span_singleton.mp hu)
    rw [Φ.polar.perp_perp] at hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    exact hw (by rw [Φ.Q_smul, hx, mul_zero])
  obtain ⟨y, hy⟩ : ∃ y, y = (-(ν * Φ.Q w) / Φ.polar.β w u) • u := ⟨_, rfl⟩
  have hxy : Φ.polar.β x y = 0 := by rw [hy, Φ.polar.smul_right, hxu, mul_zero]
  have hxy' : Φ.polar.β x (-y) = 0 := by
    rw [← neg_one_smul K' y, Φ.polar.smul_right, hxy, mul_zero]
  have hwy : Φ.polar.β w y = -(ν * Φ.Q w) := by
    rw [hy, Φ.polar.smul_right]
    field_simp
  have hry : Φ.reflect w y = y + ν • w := by
    rw [Φ.reflect_apply, hwy, show -(ν * Φ.Q w) / Φ.Q w = -ν by field_simp, neg_smul,
      sub_neg_eq_add]
  have hxry : Φ.polar.β x (Φ.reflect w y) = 0 := by
    rw [hry, Φ.polar.add_right, hxy, Φ.polar.smul_right, hxw, mul_zero, add_zero]
  have hinv : ∀ z : ι → K', Φ.polar.β x z = 0 → ∀ v,
      Φ.eichler x z (Φ.eichler x (-z) v) = v := fun z hz v => by
    have hz' : Φ.polar.β x (-z) = 0 := by
      rw [← neg_one_smul K' z, Φ.polar.smul_right, hz, mul_zero]
    rw [Φ.eichler_eichler hx hz hz', add_neg_cancel, Φ.eichler_zero_right]
  obtain ⟨R, hR, hRv, hRinv⟩ := exists_mem_orthGroup_mulVec Φ.Q (Φ.reflect w) (Φ.reflect w)
    (Φ.reflect_reflect hw) (Φ.reflect_reflect hw) (Φ.Q_reflect w)
  obtain ⟨G, hG, hGv, hGinv⟩ := exists_mem_orthGroup_mulVec Φ.Q (Φ.eichler x y)
    (Φ.eichler x (-y)) (hinv y hxy) (fun v => by simpa only [neg_neg] using hinv (-y) hxy' v)
    (Φ.Q_eichler hx hxy)
  refine ⟨⁅R, G⁆, Subgroup.commutator_mem_commutator hR hG, fun v => ?_⟩
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
    ← mulVec_mulVec, ← mulVec_mulVec, hGinv, hRinv, hGv, hRv,
    Φ.apply_eichler_apply (Φ.reflect_reflect hw) (Φ.Q_reflect w),
    Φ.reflect_apply_of_polar_eq_zero hwx, Φ.eichler_eichler hx hxry hxy', hry, add_neg_cancel_comm]

theorem exists_mem_statedOmega_eichler' (hι : 5 ≤ Fintype.card ι) {x y : ι → K'}
    (hx : Φ.Q x = 0) (hxy : Φ.polar.β x y = 0) :
    ∃ A ∈ StatedOmega Φ.Q, ∀ v, (A : Matrix ι ι K') *ᵥ v = Φ.eichler x y v := by
  by_cases hy : Φ.Q y = 0
  ·
    have hT : ¬Φ.polar.IsTotallyIsotropic (Φ.polar.perp (K' ∙ x ⊔ K' ∙ y)) := fun hT => by
      have h1 := Φ.polar.finrank_perp (Φ.polar.perp (K' ∙ x ⊔ K' ∙ y))
      have h2 := Φ.polar.finrank_perp (K' ∙ x ⊔ K' ∙ y)
      have h3 := Submodule.finrank_mono hT
      have h4 := Submodule.finrank_sup_add_finrank_inf_eq (K' ∙ x) (K' ∙ y)
      have h5 : Module.finrank K' (K' ∙ x) ≤ 1 :=
        (finrank_span_le_card ({x} : Set (ι → K'))).trans (by simp)
      have h6 : Module.finrank K' (K' ∙ y) ≤ 1 :=
        (finrank_span_le_card ({y} : Set (ι → K'))).trans (by simp)
      rw [Module.finrank_fintype_fun_eq_card] at h1 h2
      omega
    obtain ⟨w, hwT, hw⟩ := Φ.exists_mem_Q_ne_zero hT
    rw [Φ.polar.perp_sup] at hwT
    have hxw : Φ.polar.β x w = 0 := Φ.polar.mem_perp_span_singleton.mp hwT.1
    have hyw : Φ.polar.β y w = 0 := Φ.polar.mem_perp_span_singleton.mp hwT.2
    have hQyw : Φ.Q (y + w) ≠ 0 := by rwa [Φ.Q_add, hy, hyw, zero_add, add_zero]
    have hxyw : Φ.polar.β x (y + w) = 0 := by rw [Φ.polar.add_right, hxy, hxw, add_zero]
    obtain ⟨A₁, hA₁, hA₁v⟩ := exists_mem_statedOmega_eichler_smul' Φ hx hxyw hQyw 1
    obtain ⟨A₂, hA₂, hA₂v⟩ := exists_mem_statedOmega_eichler_smul' Φ hx hxw hw (-1)
    refine ⟨A₁ * A₂, mul_mem hA₁ hA₂, fun v => ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, hA₂v, hA₁v,
      Φ.eichler_eichler hx (by rwa [one_smul]) (by rw [Φ.polar.smul_right, hxw, mul_zero]),
      show (1 : K') • (y + w) + (-1 : K') • w = y by module]
  · obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler_smul' Φ hx hxy hy 1
    exact ⟨A, hA, fun v => by rw [hAv, one_smul]⟩

end Matrix

end CFSG.LieType.BorelTits
