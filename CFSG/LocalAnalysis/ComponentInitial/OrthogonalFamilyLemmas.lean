module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem quadratic_hyperbolic_partner (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    {u : V} (hu : Q u = 0) (hu0 : u ≠ 0) : ∃ f : V, Q f = 0 ∧ polar Q u f = 1 := by
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hu hu0
  exact ⟨P.f, P.Q_f, P.polar_ef⟩

section Diagonal

variable (Q : QuadraticForm K V)

theorem eichler_smul_apply {u v : V} (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 0)
    (c : K) (z : V) :
    eichler Q u (c • v) z = z + (c * polar Q z u) • v - (c * polar Q z v) • u := by
  have hw : polar Q u (c • v) = 0 := by rw [polar_smul_right_eq, huv, mul_zero]
  rw [eichler_apply hu hw, polar_smul_right_eq, map_smul_eq_sq, hv]
  module

@[expose] noncomputable def orthHypRootX (P₁ P₂ : HypPair Q) (a : K) : V ≃ₗ[K] V :=
  eichler Q P₁.e (-a • P₂.f)

@[expose] noncomputable def orthHypRootY (P₁ P₂ : HypPair Q) (a : K) : V ≃ₗ[K] V :=
  eichler Q P₂.e (-a • P₁.f)

@[expose] noncomputable def orthHypWeyl (P₁ P₂ : HypPair Q) (t : K) : V ≃ₗ[K] V :=
  orthHypRootX Q P₁ P₂ t * orthHypRootY Q P₁ P₂ (-t⁻¹) * orthHypRootX Q P₁ P₂ t

variable {Q} {P₁ P₂ : HypPair Q}

structure OrthPolarValues (P₁ P₂ : HypPair Q) : Prop where
  e₁e₁ : polar Q P₁.e P₁.e = 0
  e₁f₁ : polar Q P₁.e P₁.f = 1
  f₁e₁ : polar Q P₁.f P₁.e = 1
  f₁f₁ : polar Q P₁.f P₁.f = 0
  e₂e₂ : polar Q P₂.e P₂.e = 0
  e₂f₂ : polar Q P₂.e P₂.f = 1
  f₂e₂ : polar Q P₂.f P₂.e = 1
  f₂f₂ : polar Q P₂.f P₂.f = 0
  e₁e₂ : polar Q P₁.e P₂.e = 0
  e₁f₂ : polar Q P₁.e P₂.f = 0
  f₁e₂ : polar Q P₁.f P₂.e = 0
  f₁f₂ : polar Q P₁.f P₂.f = 0
  e₂e₁ : polar Q P₂.e P₁.e = 0
  e₂f₁ : polar Q P₂.e P₁.f = 0
  f₂e₁ : polar Q P₂.f P₁.e = 0
  f₂f₁ : polar Q P₂.f P₁.f = 0

theorem orthPolarValues (h : P₁.Orth P₂) : OrthPolarValues P₁ P₂ where
  e₁e₁ := P₁.polar_ee
  e₁f₁ := P₁.polar_ef
  f₁e₁ := P₁.polar_fe
  f₁f₁ := P₁.polar_ff
  e₂e₂ := P₂.polar_ee
  e₂f₂ := P₂.polar_ef
  f₂e₂ := P₂.polar_fe
  f₂f₂ := P₂.polar_ff
  e₁e₂ := h.ee
  e₁f₂ := h.ef
  f₁e₂ := h.fe
  f₁f₂ := h.ff
  e₂e₁ := by rw [polar_comm, h.ee]
  e₂f₁ := by rw [polar_comm, h.fe]
  f₂e₁ := by rw [polar_comm, h.ef]
  f₂f₁ := by rw [polar_comm, h.ff]

theorem orthHypRootX_apply (h : P₁.Orth P₂) (a : K) (z : V) :
    orthHypRootX Q P₁ P₂ a z = z + (-a * polar Q z P₁.e) • P₂.f - (-a * polar Q z P₂.f) • P₁.e :=
  eichler_smul_apply Q P₁.Q_e P₂.Q_f h.ef (-a) z

theorem orthHypRootY_apply (h : P₁.Orth P₂) (a : K) (z : V) :
    orthHypRootY Q P₁ P₂ a z = z + (-a * polar Q z P₂.e) • P₁.f - (-a * polar Q z P₁.f) • P₂.e :=
  eichler_smul_apply Q P₂.Q_e P₁.Q_f (by rw [polar_comm, h.fe]) (-a) z

theorem orthHypRootX_basis (h : P₁.Orth P₂) (a : K) :
    orthHypRootX Q P₁ P₂ a P₁.e = P₁.e ∧ orthHypRootX Q P₁ P₂ a P₂.e = P₂.e + a • P₁.e ∧
      orthHypRootX Q P₁ P₂ a P₁.f = P₁.f - a • P₂.f ∧ orthHypRootX Q P₁ P₂ a P₂.f = P₂.f := by
  have hv := orthPolarValues h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [orthHypRootX_apply h]
     simp only [hv.e₁e₁, hv.e₁f₂, hv.e₂e₁, hv.e₂f₂, hv.f₁e₁, hv.f₁f₂, hv.f₂e₁, hv.f₂f₂]
     module)

theorem orthHypRootY_basis (h : P₁.Orth P₂) (a : K) :
    orthHypRootY Q P₁ P₂ a P₁.e = P₁.e + a • P₂.e ∧ orthHypRootY Q P₁ P₂ a P₂.e = P₂.e ∧
      orthHypRootY Q P₁ P₂ a P₁.f = P₁.f ∧ orthHypRootY Q P₁ P₂ a P₂.f = P₂.f - a • P₁.f := by
  have hv := orthPolarValues h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [orthHypRootY_apply h]
     simp only [hv.e₁e₂, hv.e₁f₁, hv.e₂e₂, hv.e₂f₁, hv.f₁e₂, hv.f₁f₁, hv.f₂e₂, hv.f₂f₁]
     module)

theorem orthHypWeyl_basis (h : P₁.Orth P₂) {t : K} (ht : t ≠ 0) :
    orthHypWeyl Q P₁ P₂ t P₁.e = -t⁻¹ • P₂.e ∧ orthHypWeyl Q P₁ P₂ t P₂.e = t • P₁.e ∧
      orthHypWeyl Q P₁ P₂ t P₁.f = -t • P₂.f ∧ orthHypWeyl Q P₁ P₂ t P₂.f = t⁻¹ • P₁.f := by
  obtain ⟨xe₁, xe₂, xf₁, xf₂⟩ := orthHypRootX_basis h t
  obtain ⟨ye₁, ye₂, yf₁, yf₂⟩ := orthHypRootY_basis h (-t⁻¹)
  simp only [orthHypWeyl, LinearEquiv.mul_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [xe₁, ye₁, map_add, map_smul, xe₁, xe₂]
    match_scalars <;> field_simp
    ring
  · rw [xe₂, map_add, map_smul, ye₂, ye₁, map_add, map_smul, map_add, map_smul, xe₂, xe₁]
    match_scalars <;> field_simp <;> ring
  · rw [xf₁, map_sub, map_smul, yf₁, yf₂, map_sub, map_smul, map_sub, map_smul, xf₁, xf₂]
    match_scalars <;> field_simp <;> ring
  · rw [xf₂, yf₂, map_sub, map_smul, xf₂, xf₁]
    match_scalars <;> field_simp
    ring

theorem orthogonal_elementary_diagonal (h : P₁.Orth P₂) {t : K} (ht : t ≠ 0) :
    (∀ a, orthHypRootX Q P₁ P₂ a ∈ orthElementaryGroup Q) ∧
    (∀ a, orthHypRootY Q P₁ P₂ a ∈ orthElementaryGroup Q) ∧
    orthHypWeyl Q P₁ P₂ t ∈ orthElementaryGroup Q ∧
    orthHypWeyl Q P₁ P₂ t P₁.e = -t⁻¹ • P₂.e ∧ orthHypWeyl Q P₁ P₂ t P₂.e = t • P₁.e ∧
    orthHypWeyl Q P₁ P₂ t P₁.f = -t • P₂.f ∧ orthHypWeyl Q P₁ P₂ t P₂.f = t⁻¹ • P₁.f ∧
    (∀ z, polar Q z P₁.e = 0 → polar Q z P₁.f = 0 → polar Q z P₂.e = 0 → polar Q z P₂.f = 0 →
      orthHypWeyl Q P₁ P₂ t z = z) ∧
    (orthHypWeyl Q P₁ P₂ t * orthHypWeyl Q P₁ P₂ (-1)) P₁.e = t • P₁.e ∧
    (orthHypWeyl Q P₁ P₂ t * orthHypWeyl Q P₁ P₂ (-1)) P₂.e = t⁻¹ • P₂.e ∧
    (orthHypWeyl Q P₁ P₂ t * orthHypWeyl Q P₁ P₂ (-1)) P₁.f = t⁻¹ • P₁.f ∧
    (orthHypWeyl Q P₁ P₂ t * orthHypWeyl Q P₁ P₂ (-1)) P₂.f = t • P₂.f ∧
    ∀ z, polar Q z P₁.e = 0 → polar Q z P₁.f = 0 → polar Q z P₂.e = 0 → polar Q z P₂.f = 0 →
      (orthHypWeyl Q P₁ P₂ t * orthHypWeyl Q P₁ P₂ (-1)) z = z := by
  have hX : ∀ a, orthHypRootX Q P₁ P₂ a ∈ orthElementaryGroup Q := fun a =>
    eichler_mem_elementaryGroup Q _ _
  have hY : ∀ a, orthHypRootY Q P₁ P₂ a ∈ orthElementaryGroup Q := fun a =>
    eichler_mem_elementaryGroup Q _ _
  have hfixX : ∀ (a : K) (z : V), polar Q z P₁.e = 0 → polar Q z P₂.f = 0 →
      orthHypRootX Q P₁ P₂ a z = z := fun a z h1 h2 => by
    rw [orthHypRootX_apply h, h1, h2]
    simp
  have hfixY : ∀ (a : K) (z : V), polar Q z P₂.e = 0 → polar Q z P₁.f = 0 →
      orthHypRootY Q P₁ P₂ a z = z := fun a z h1 h2 => by
    rw [orthHypRootY_apply h, h1, h2]
    simp
  have hfixW : ∀ s z, polar Q z P₁.e = 0 → polar Q z P₁.f = 0 → polar Q z P₂.e = 0 →
      polar Q z P₂.f = 0 → orthHypWeyl Q P₁ P₂ s z = z := by
    intro s z h1 h2 h3 h4
    simp only [orthHypWeyl, LinearEquiv.mul_apply]
    rw [hfixX s z h1 h4, hfixY _ z h3 h2, hfixX s z h1 h4]
  obtain ⟨we₁, we₂, wf₁, wf₂⟩ := orthHypWeyl_basis h ht
  obtain ⟨ve₁, ve₂, vf₁, vf₂⟩ := orthHypWeyl_basis h (neg_ne_zero.2 one_ne_zero : (-1 : K) ≠ 0)
  have hmem : orthHypWeyl Q P₁ P₂ t ∈ orthElementaryGroup Q :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hX t) (hY _)) (hX t)
  refine ⟨hX, hY, hmem, we₁, we₂, wf₁, wf₂, hfixW t, ?_, ?_, ?_, ?_, fun z h1 h2 h3 h4 => ?_⟩
  · rw [LinearEquiv.mul_apply, ve₁, map_smul, we₂]
    match_scalars
    simp
  · rw [LinearEquiv.mul_apply, ve₂, map_smul, we₁]
    match_scalars
    simp
  · rw [LinearEquiv.mul_apply, vf₁, map_smul, wf₂]
    match_scalars
    simp
  · rw [LinearEquiv.mul_apply, vf₂, map_smul, wf₁]
    match_scalars
    simp
  · rw [LinearEquiv.mul_apply, hfixW (-1) z h1 h2 h3 h4, hfixW t z h1 h2 h3 h4]

end Diagonal

section SingularDescent

variable [FiniteDimensional K V]

theorem quadratic_singular_subspace_descent (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hef : polar Q e f = 1) (T : Submodule K V) (hT : ∀ x ∈ T, Q x = 0) {r : ℕ}
    (hTr : finrank K T = r) :
    ∃ T' : Submodule K V, (∀ x ∈ T', polar Q x e = 0 ∧ polar Q x f = 0) ∧
      (∀ x ∈ T', Q x = 0) ∧ r - 1 ≤ finrank K T' ∧ T' ≤ T ⊔ Submodule.span K {e} := by
  classical
  have hee : polar Q e e = 0 := polar_self_eq_zero he
  let φ : V →ₗ[K] K :=
    { toFun := fun x => polar Q x e
      map_add' := fun x y => polar_add_left Q x y e
      map_smul' := fun c x => by simp [polar_smul_left] }
  let π : V →ₗ[K] V :=
    { toFun := fun x => x - polar Q x f • e
      map_add' := fun x y => by
        simp only [polar_add_left, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply, smul_sub, mul_smul] }
  have hπ : ∀ x, π x = x - polar Q x f • e := fun _ => rfl
  have hφ : ∀ x, φ x = polar Q x e := fun _ => rfl
  let U : Submodule K V := T ⊓ LinearMap.ker φ
  have hmemU : ∀ y, y ∈ U ↔ y ∈ T ∧ polar Q y e = 0 := fun y => by
    rw [Submodule.mem_inf, LinearMap.mem_ker, hφ]
  refine ⟨U.map π, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hye := ((hmemU y).1 hy).2
    rw [hπ]
    constructor
    · rw [polar_sub_left, polar_smul_left_eq, hye, hee, mul_zero, sub_zero]
    · rw [polar_sub_left, polar_smul_left_eq, hef, mul_one, sub_self]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyT, hye⟩ := (hmemU y).1 hy
    rw [hπ, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, map_smul_eq_sq, he,
      polar_smul_right_eq, hye, hT y hyT]
    ring
  ·
    let ψ := π.domRestrict U
    have hrange : LinearMap.range ψ = U.map π := LinearMap.range_domRestrict U π
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hrange] at hrn
    have hker : ∀ y : U, ψ y = 0 → (y : V) = polar Q y f • e := fun y hy => by
      rw [LinearMap.domRestrict_apply, hπ] at hy
      exact sub_eq_zero.1 hy
    have hU : r - 1 ≤ finrank K U := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq T (LinearMap.ker φ)
      have h2 := Submodule.finrank_le (T ⊔ LinearMap.ker φ)
      have h3 := LinearMap.finrank_range_add_finrank_ker φ
      have h4 : finrank K (LinearMap.range φ) ≤ 1 := by
        have := Submodule.finrank_le (LinearMap.range φ)
        rwa [Module.finrank_self] at this
      change r - 1 ≤ finrank K ↥(T ⊓ LinearMap.ker φ)
      omega
    by_cases heT : e ∈ T
    ·
      have hUT : U = T := by
        refine le_antisymm inf_le_left fun y hy => (hmemU y).2 ⟨hy, ?_⟩
        have h := QuadraticMap.map_add Q y e
        rw [hT _ (T.add_mem hy heT), hT y hy, he] at h
        linear_combination -h
      have hk : finrank K (LinearMap.ker ψ) ≤ 1 := by
        let χ : LinearMap.ker ψ →ₗ[K] K :=
          { toFun := fun y => polar Q ((y : U) : V) f
            map_add' := fun y z => polar_add_left Q _ _ f
            map_smul' := fun c y => by simp [polar_smul_left] }
        have hχ : Function.Injective χ := by
          rw [← LinearMap.ker_eq_bot, eq_bot_iff]
          intro y hy
          rw [LinearMap.mem_ker] at hy
          have h := hker y (LinearMap.mem_ker.1 y.2)
          change polar Q ((y : U) : V) f = 0 at hy
          rw [hy, zero_smul] at h
          rw [Submodule.mem_bot]
          exact Subtype.ext (Subtype.ext h)
        have := LinearMap.finrank_le_finrank_of_injective hχ
        rwa [Module.finrank_self] at this
      have hUr : finrank K U = r := by rw [hUT, hTr]
      omega
    ·
      have hk : LinearMap.ker ψ = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        rw [Submodule.mem_bot]
        have h := hker y (LinearMap.mem_ker.1 hy)
        by_cases hc : polar Q (y : V) f = 0
        · rw [hc, zero_smul] at h
          exact Subtype.ext h
        · exfalso
          apply heT
          obtain ⟨c, hc'⟩ : ∃ c, polar Q (y : V) f = c := ⟨_, rfl⟩
          rw [hc'] at h hc
          have he' : c⁻¹ • (y : V) = e := by
            rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
          rw [← he']
          exact T.smul_mem _ ((hmemU y).1 y.2).1
      rw [hk, finrank_bot] at hrn
      omega
  · rintro _ ⟨y, hy, rfl⟩
    rw [hπ]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ((hmemU y).1 hy).1)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))

end SingularDescent

section ComplementEmbedding

variable {U W : Submodule K V}

@[expose] noncomputable def orthExtend (hUW : IsCompl U W) : (U ≃ₗ[K] U) →* (V ≃ₗ[K] V) where
  toFun g := ((Submodule.prodEquivOfIsCompl U W hUW).symm.trans
    (g.prodCongr (LinearEquiv.refl K W))).trans (Submodule.prodEquivOfIsCompl U W hUW)
  map_one' := LinearEquiv.ext fun x => by
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
    change Submodule.prodEquivOfIsCompl U W hUW
      ((Submodule.prodEquivOfIsCompl U W hUW).symm x) = x
    exact LinearEquiv.apply_symm_apply _ x
  map_mul' g h := LinearEquiv.ext fun x => by
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.mul_apply]

theorem orthExtend_apply (hUW : IsCompl U W) (g : U ≃ₗ[K] U) (u : U) (w : W) :
    orthExtend hUW g ((u : V) + w) = (g u : V) + w := by
  have hx : (u : V) + w = Submodule.prodEquivOfIsCompl U W hUW (u, w) := rfl
  change Submodule.prodEquivOfIsCompl U W hUW ((g.prodCongr (LinearEquiv.refl K W))
    ((Submodule.prodEquivOfIsCompl U W hUW).symm ((u : V) + w))) = _
  rw [hx, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_add_of_isCompl (hUW : IsCompl U W) (x : V) : ∃ (u : U) (w : W), x = u + w :=
  ⟨((Submodule.prodEquivOfIsCompl U W hUW).symm x).1,
    ((Submodule.prodEquivOfIsCompl U W hUW).symm x).2,
    ((Submodule.prodEquivOfIsCompl U W hUW).apply_symm_apply x).symm⟩

theorem orthogonal_complement_elementary_embedding (Q : QuadraticForm K V) (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, polar Q u w = 0) :
    Function.Injective (orthExtend hUW) ∧
    (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype),
      orthExtend hUW g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
    (∀ g ∈ orthElementaryGroup (Q.comp U.subtype), orthExtend hUW g ∈ orthElementaryGroup Q) ∧
    ∀ u v : U, orthExtend hUW (eichler (Q.comp U.subtype) u v) = eichler Q u v := by
  have hpolar : ∀ x y : U, polar (Q.comp U.subtype) x y = polar Q x y := fun x y => by
    simp [polar]
  have hcomp : ∀ x : U, Q.comp U.subtype x = Q x := fun _ => rfl
  have heich : ∀ u v : U, orthExtend hUW (eichler (Q.comp U.subtype) u v) = eichler Q u v := by
    intro u v
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨u', w, rfl⟩ := exists_add_of_isCompl hUW x
    rw [orthExtend_apply, map_add]
    have hw : eichler Q (u : V) (v : V) w = w := eichler_apply_of_polar_eq_zero
      (by rw [polar_comm]; exact horth u u.2 w w.2) (by rw [polar_comm]; exact horth v v.2 w w.2)
    rw [hw]
    congr 1
    by_cases h : Q (u : V) = 0 ∧ polar Q (u : V) (v : V) = 0
    · have h' : Q.comp U.subtype u = 0 ∧ polar (Q.comp U.subtype) u v = 0 := by
        rw [hcomp, hpolar]
        exact h
      rw [eichler_apply h'.1 h'.2, eichler_apply h.1 h.2]
      simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, hpolar, hcomp]
    · have h' : ¬(Q.comp U.subtype u = 0 ∧ polar (Q.comp U.subtype) u v = 0) := by
        rw [hcomp, hpolar]
        exact h
      rw [eichler_of_not h', eichler_of_not h]
      rfl
  refine ⟨fun g h hgh => LinearEquiv.ext fun u => Subtype.ext ?_, fun g hg => ?_,
    fun g hg => ?_, heich⟩
  · have h1 := orthExtend_apply hUW g u 0
    have h2 := orthExtend_apply hUW h u 0
    rw [hgh, h2] at h1
    simpa using h1.symm
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
    intro x
    obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hUW x
    rw [orthExtend_apply, QuadraticMap.map_add Q, QuadraticMap.map_add Q,
      horth _ (g u).2 _ w.2, horth _ u.2 _ w.2]
    have := hg u
    rw [hcomp, hcomp] at this
    rw [this]
  · have hle : orthElementaryGroup (Q.comp U.subtype) ≤
        (orthElementaryGroup Q).comap (orthExtend hUW) := by
      rw [orthElementaryGroup, elementaryGroup, Subgroup.closure_le]
      rintro _ ⟨u, v, -, -, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, heich]
      exact eichler_mem_elementaryGroup Q _ _
    exact hle hg

end ComplementEmbedding

end CFSG.LocalAnalysis.ComponentInitial
