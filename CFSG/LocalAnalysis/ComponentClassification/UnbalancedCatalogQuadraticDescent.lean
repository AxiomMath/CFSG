module

public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module TensorProduct

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Fixed

variable (σ : K ≃+* K)

@[expose] def descentField : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)

variable {σ}

theorem mem_descentField {a : K} : a ∈ descentField σ ↔ σ a = a := by
  rw [descentField, RingHom.mem_eqLocusField]
  rfl

theorem coe_descentField_fixed (a : descentField σ) : σ (a : K) = a :=
  mem_descentField.1 a.2

variable (T : V →ₛₗ[(σ : K →+* K)] V)

@[expose] def fixSpace : Submodule (descentField σ) V where
  carrier := {v | T v = v}
  add_mem' {v w} hv hw := by
    change T (v + w) = v + w
    rw [map_add, show T v = v from hv, show T w = w from hw]
  zero_mem' := map_zero T
  smul_mem' c v hv := by
    change T ((c : K) • v) = (c : K) • v
    rw [map_smulₛₗ, show T v = v from hv, RingEquiv.coe_toRingHom, coe_descentField_fixed]

variable {T}

theorem mem_fixSpace {v : V} : v ∈ fixSpace T ↔ T v = v :=
  Iff.rfl

variable (hσσ : ∀ a, σ (σ a) = a) (hTT : ∀ v, T (T v) = v) {c : K} (hc : σ c ≠ c)

include hσσ hc in
theorem mem_descentField_decomp (a : K) :
    (c - σ c)⁻¹ * (a - σ a) ∈ descentField σ ∧
      a - c * ((c - σ c)⁻¹ * (a - σ a)) ∈ descentField σ := by
  have hc0 : c - σ c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hbc0 : σ c - c ≠ 0 := sub_ne_zero.mpr hc
  constructor
  · rw [mem_descentField, map_mul, map_inv₀, map_sub, map_sub, hσσ, hσσ, ← neg_sub c,
      ← neg_sub a, inv_neg, neg_mul_neg]
  · rw [mem_descentField, map_sub, map_mul, map_mul, map_inv₀, map_sub, map_sub, hσσ, hσσ]
    field_simp
    ring

include hσσ hTT in
theorem inv_smul_sub_mem_fixSpace (v : V) : (c - σ c)⁻¹ • (v - T v) ∈ fixSpace T := by
  rw [mem_fixSpace, map_smulₛₗ, map_sub, hTT, RingEquiv.coe_toRingHom, map_inv₀, map_sub, hσσ,
    ← neg_sub c, inv_neg, neg_smul, ← smul_neg, neg_sub]

include hσσ hTT hc in
theorem sub_smul_inv_smul_mem_fixSpace (v : V) :
    v - c • ((c - σ c)⁻¹ • (v - T v)) ∈ fixSpace T := by
  have hw := inv_smul_sub_mem_fixSpace hσσ hTT (c := c) v
  rw [mem_fixSpace] at hw ⊢
  rw [map_sub, map_smulₛₗ, hw, RingEquiv.coe_toRingHom]
  have hc0 : c - σ c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have key : (c - σ c) • ((c - σ c)⁻¹ • (v - T v)) = v - T v := by
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [sub_smul, sub_eq_iff_eq_add] at key
  rw [sub_eq_sub_iff_add_eq_add, key]
  abel

include hσσ hTT hc in
theorem span_fixSpace : Submodule.span K (fixSpace T : Set V) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : v = (v - c • ((c - σ c)⁻¹ • (v - T v))) + c • ((c - σ c)⁻¹ • (v - T v)) :=
    (sub_add_cancel _ _).symm
  rw [hv]
  exact add_mem (Submodule.subset_span (sub_smul_inv_smul_mem_fixSpace hσσ hTT hc v))
    (Submodule.smul_mem _ _ (Submodule.subset_span (inv_smul_sub_mem_fixSpace hσσ hTT v)))

include hc in
theorem eq_zero_of_add_smul_eq_zero {w₀ w₁ : V} (h₀ : w₀ ∈ fixSpace T) (h₁ : w₁ ∈ fixSpace T)
    (hw : w₀ + c • w₁ = 0) : w₀ = 0 ∧ w₁ = 0 := by
  have h2 : w₀ + σ c • w₁ = 0 := by
    have h3 := congrArg T hw
    rwa [map_add, map_smulₛₗ, map_zero, mem_fixSpace.mp h₀, mem_fixSpace.mp h₁] at h3
  have h3 : (c - σ c) • w₁ = 0 := by
    rw [sub_smul, show c • w₁ - σ c • w₁ = (w₀ + c • w₁) - (w₀ + σ c • w₁) by abel, hw, h2,
      sub_zero]
  have hw₁ : w₁ = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  refine ⟨?_, hw₁⟩
  rw [hw₁, smul_zero, add_zero] at hw
  exact hw

include hσσ hc in
theorem linearIndependent_fixSpace {ι : Type*} (b : Basis ι (descentField σ) (fixSpace T)) :
    LinearIndependent K (fun i => (b i : V)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  obtain ⟨y, hy⟩ : ∃ y : ι → descentField σ,
      ∀ j, (y j : K) = (c - σ c)⁻¹ * (g j - σ (g j)) :=
    ⟨fun j => ⟨_, (mem_descentField_decomp hσσ hc (g j)).1⟩, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ι → descentField σ, ∀ j, (x j : K) = g j - c * (y j : K) :=
    ⟨fun j => ⟨_, (mem_descentField_decomp hσσ hc (g j)).2⟩, fun j => by rw [hy]⟩
  have hgj : ∀ j, g j = (x j : K) + c * (y j : K) := fun j => by
    rw [hx]
    ring
  have hg' : ((∑ j ∈ s, x j • b j : fixSpace T) : V) +
      c • ((∑ j ∈ s, y j • b j : fixSpace T) : V) = 0 := by
    rw [← hg, Submodule.coe_sum, Submodule.coe_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Submodule.coe_smul, Subfield.smul_def, Subfield.smul_def, smul_smul,
      ← add_smul, ← hgj]
  obtain ⟨h1, h3⟩ := eq_zero_of_add_smul_eq_zero hc (Submodule.coe_mem _) (Submodule.coe_mem _) hg'
  have hx0 := (linearIndependent_iff'.mp b.linearIndependent) s x
    (by rw [← Submodule.coe_eq_zero]; exact h1) i hi
  have hy0 := (linearIndependent_iff'.mp b.linearIndependent) s y
    (by rw [← Submodule.coe_eq_zero]; exact h3) i hi
  rw [hgj i, hx0, hy0, ZeroMemClass.coe_zero, mul_zero, add_zero]

include hσσ hTT hc in
theorem span_basis_fixSpace {ι : Type*} (b : Basis ι (descentField σ) (fixSpace T)) :
    ⊤ ≤ Submodule.span K (Set.range fun i => (b i : V)) := by
  rw [← span_fixSpace hσσ hTT hc, Submodule.span_le]
  intro w hw
  exact Submodule.span_induction (p := fun x _ => ((x : fixSpace T) : V) ∈
      Submodule.span K (Set.range fun i => (b i : V)))
    (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      exact Submodule.subset_span ⟨j, rfl⟩)
    (Submodule.zero_mem _)
    (fun x y _ _ hx hy => by
      rw [Submodule.coe_add]
      exact add_mem hx hy)
    (fun a x _ hx => by
      rw [Submodule.coe_smul, Subfield.smul_def]
      exact Submodule.smul_mem _ _ hx)
    (b.mem_span ⟨w, hw⟩)

@[expose] noncomputable def fixSpaceBasis {ι : Type*}
    (b : Basis ι (descentField σ) (fixSpace T)) : Basis ι K V :=
  Basis.mk (linearIndependent_fixSpace hσσ hc b) (span_basis_fixSpace hσσ hTT hc b)

theorem fixSpaceBasis_apply {ι : Type*} (b : Basis ι (descentField σ) (fixSpace T)) (i : ι) :
    fixSpaceBasis hσσ hTT hc b i = b i :=
  Basis.mk_apply _ _ i

theorem finite_fixSpace [Finite K] [FiniteDimensional K V] :
    Module.Finite (descentField σ) (fixSpace T) := by
  have : Finite V := Module.finite_of_finite K
  exact Module.Finite.of_finite

include hσσ hTT hc in
theorem finrank_fixSpace [Finite K] [FiniteDimensional K V] :
    finrank (descentField σ) (fixSpace T) = finrank K V := by
  have := finite_fixSpace (σ := σ) (T := T)
  rw [finrank_eq_card_basis (fixSpaceBasis hσσ hTT hc
    (Module.finBasis (descentField σ) (fixSpace T))), Fintype.card_fin]

include hσσ hTT hc in
theorem liftBaseChange_fixSpace_bijective [Finite K] [FiniteDimensional K V] :
    Function.Bijective (LinearMap.liftBaseChange K (fixSpace T).subtype) := by
  have := finite_fixSpace (σ := σ) (T := T)
  have heq : LinearMap.liftBaseChange K (fixSpace T).subtype =
      ((Algebra.TensorProduct.basis K (Module.finBasis (descentField σ) (fixSpace T))).equiv
        (fixSpaceBasis hσσ hTT hc (Module.finBasis (descentField σ) (fixSpace T)))
          (Equiv.refl _)).toLinearMap := by
    refine (Algebra.TensorProduct.basis K (Module.finBasis (descentField σ) (fixSpace T))).ext
      fun i => ?_
    rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul,
      LinearEquiv.coe_coe, ← Algebra.TensorProduct.basis_apply, Basis.equiv_apply,
      Equiv.refl_apply, fixSpaceBasis_apply]
    rfl
  rw [heq]
  exact LinearEquiv.bijective _

end Fixed

section Form

variable {σ : K ≃+* K} {T : V →ₛₗ[(σ : K →+* K)] V} {Q : QuadraticForm K V}
  (hTQ : ∀ v, Q (T v) = σ (Q v))

include hTQ in
theorem polar_semilinear (x y : V) : polar Q (T x) (T y) = σ (polar Q x y) := by
  rw [polar, polar, ← map_add T, hTQ, hTQ, hTQ, map_sub, map_sub]

include hTQ in
theorem map_mem_descentField {w : V} (hw : w ∈ fixSpace T) : Q w ∈ descentField σ := by
  rw [mem_descentField, ← hTQ, mem_fixSpace.1 hw]

include hTQ in
theorem polar_mem_descentField {w w' : V} (hw : w ∈ fixSpace T) (hw' : w' ∈ fixSpace T) :
    polar Q w w' ∈ descentField σ := by
  rw [mem_descentField, ← polar_semilinear hTQ, mem_fixSpace.1 hw, mem_fixSpace.1 hw']

@[expose] noncomputable def descentPolar :
    LinearMap.BilinMap (descentField σ) (fixSpace T) (descentField σ) :=
  LinearMap.mk₂ (descentField σ)
    (fun w w' => ⟨polar Q w w', polar_mem_descentField hTQ w.2 w'.2⟩)
    (fun w₁ w₂ w' => Subtype.ext (by simp [polar_add_left]))
    (fun a w w' => Subtype.ext (by simp [Subfield.smul_def, polar_smul_left]))
    (fun w w₁ w₂ => Subtype.ext (by simp [polar_add_right]))
    (fun a w w' => Subtype.ext (by simp [Subfield.smul_def, polar_smul_right]))

@[expose] noncomputable def descentForm : QuadraticForm (descentField σ) (fixSpace T) where
  toFun w := ⟨Q w, map_mem_descentField hTQ w.2⟩
  toFun_smul a w := Subtype.ext (by
    change Q ((a : K) • (w : V)) = ((a : K) * a) * Q w
    rw [QuadraticMap.map_smul, smul_eq_mul])
  exists_companion' := ⟨descentPolar hTQ, fun w w' => Subtype.ext (by
    change Q ((w : V) + w') = Q w + Q w' + polar Q w w'
    exact QuadraticMap.map_add Q w w')⟩

theorem coe_descentForm (w : fixSpace T) : (descentForm hTQ w : K) = Q w :=
  rfl

theorem coe_polar_descentForm (w w' : fixSpace T) :
    ((polar (descentForm hTQ) w w' : descentField σ) : K) = polar Q w w' := by
  simp [polar, coe_descentForm]

include hTQ in
theorem nondegenerate_descentForm (hQ : (polarBilin Q).Nondegenerate)
    (hspan : Submodule.span K (fixSpace T : Set V) = ⊤) :
    (polarBilin (descentForm hTQ)).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun w hw => ?_
  have h : ∀ v, polar Q w v = 0 := by
    intro v
    have hv : v ∈ Submodule.span K (fixSpace T : Set V) := hspan ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      have h1 := congrArg (fun a : descentField σ => (a : K)) (hw ⟨x, hx⟩)
      simpa only [coe_polar_descentForm, ZeroMemClass.coe_zero] using h1
    | zero => exact polar_zero_right Q _
    | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [polar_smul_right_eq, hx, mul_zero]
  exact Subtype.ext (eq_zero_of_polar_eq_zero hQ h)

end Form

theorem polar_comp_linearMap {M : Type*} [AddCommGroup M] [Module K M] (Q : QuadraticForm K V)
    (f : M →ₗ[K] V) (x y : M) : polar (Q.comp f) x y = polar Q (f x) (f y) := by
  simp only [polar, QuadraticMap.comp_apply, map_add]

theorem eq_of_eq_on_span {Q₁ Q₂ : QuadraticForm K V} {S : Set V} (h₁ : ∀ x ∈ S, Q₁ x = Q₂ x)
    (h₂ : ∀ x ∈ S, ∀ y ∈ S, polar Q₁ x y = polar Q₂ x y) {x : V}
    (hx : x ∈ Submodule.span K S) : Q₁ x = Q₂ x := by
  have step1 : ∀ y ∈ Submodule.span K S, ∀ z ∈ S, polar Q₁ y z = polar Q₂ y z := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact fun z hz => h₂ y hy z hz
    | zero =>
      intro z _
      rw [polar_zero_left, polar_zero_left]
    | add y z _ _ hy hz =>
      intro w hw
      rw [polar_add_left, polar_add_left, hy w hw, hz w hw]
    | smul a y _ hy =>
      intro w hw
      rw [polar_smul_left_eq, polar_smul_left_eq, hy w hw]
  have step2 : ∀ y ∈ Submodule.span K S, ∀ z ∈ Submodule.span K S,
      polar Q₁ y z = polar Q₂ y z := by
    intro y hy z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact step1 y hy z hz
    | zero => rw [polar_zero_right, polar_zero_right]
    | add z z' _ _ hz hz' => rw [polar_add_right, polar_add_right, hz, hz']
    | smul a z _ hz => rw [polar_smul_right_eq, polar_smul_right_eq, hz]
  induction hx using Submodule.span_induction with
  | mem y hy => exact h₁ y hy
  | zero => rw [QuadraticMap.map_zero, QuadraticMap.map_zero]
  | add y z hy hz ihy ihz =>
    rw [QuadraticMap.map_add Q₁, QuadraticMap.map_add Q₂, ihy, ihz, step2 y hy z hz]
  | smul a y _ ihy => rw [map_smul_eq_sq, map_smul_eq_sq, ihy]

section Centralizer

variable {σ : K ≃+* K} (T : V →ₛₗ[(σ : K →+* K)] V)

@[expose] def semilinCentralizer : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ v, g (T v) = T (g v)}
  one_mem' v := rfl
  mul_mem' {g h} hg hh v := by
    change g (h (T v)) = T (g (h v))
    rw [hh, hg]
  inv_mem' {g} hg v := by
    have h := hg (g⁻¹ v)
    rw [LinearEquiv.apply_inv_apply'] at h
    rw [← h, LinearEquiv.inv_apply_apply']

variable {T}

theorem mem_semilinCentralizer {g : V ≃ₗ[K] V} :
    g ∈ semilinCentralizer T ↔ ∀ v, g (T v) = T (g v) :=
  Iff.rfl

theorem apply_mem_fixSpace {g : V ≃ₗ[K] V} (hg : g ∈ semilinCentralizer T) {w : V}
    (hw : w ∈ fixSpace T) : g w ∈ fixSpace T := by
  rw [mem_fixSpace, ← hg w, mem_fixSpace.1 hw]

@[expose] noncomputable def restrictFix {g : V ≃ₗ[K] V} (hg : g ∈ semilinCentralizer T) :
    fixSpace T ≃ₗ[descentField σ] fixSpace T where
  toFun w := ⟨g w, apply_mem_fixSpace hg w.2⟩
  invFun w := ⟨g⁻¹ w, apply_mem_fixSpace (inv_mem hg) w.2⟩
  map_add' w w' := Subtype.ext (map_add g _ _)
  map_smul' a w := Subtype.ext (by
    simp only [Submodule.coe_smul, Subfield.smul_def, map_smul, RingHom.id_apply])
  left_inv w := Subtype.ext (LinearEquiv.inv_apply_apply' g w)
  right_inv w := Subtype.ext (LinearEquiv.apply_inv_apply' g w)

theorem coe_restrictFix {g : V ≃ₗ[K] V} (hg : g ∈ semilinCentralizer T) (w : fixSpace T) :
    (restrictFix hg w : V) = g w :=
  rfl

end Centralizer

theorem even_quadratic_semilinear_involution_descent [Finite K] [FiniteDimensional K V]
    {σ : K ≃+* K} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {T : V →ₛₗ[(σ : K →+* K)] V} (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = σ (Q v)) :
    finrank (descentField σ) (fixSpace T) = finrank K V ∧
    Function.Bijective (LinearMap.liftBaseChange K (fixSpace T).subtype) ∧
    (∀ w : fixSpace T, (descentForm hTQ w : K) = Q w) ∧
    (polarBilin (descentForm hTQ)).Nondegenerate ∧
    (∀ (a : K) (w : fixSpace T),
      (Q.comp (LinearMap.liftBaseChange K (fixSpace T).subtype)) (a ⊗ₜ w) =
        descentForm hTQ w • (a * a)) ∧
    (∀ (a a' : K) (w w' : fixSpace T),
      polar (Q.comp (LinearMap.liftBaseChange K (fixSpace T).subtype)) (a ⊗ₜ w) (a' ⊗ₜ w') =
        a * a' * ((polar (descentForm hTQ) w w' : descentField σ) : K)) ∧
    (∀ Q' : QuadraticForm K (K ⊗[descentField σ] fixSpace T),
      (∀ w, Q' (1 ⊗ₜ w) = (descentForm hTQ w : K)) →
        Q' = Q.comp (LinearMap.liftBaseChange K (fixSpace T).subtype)) ∧
    ∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓ semilinCentralizer T) ≃*
        ↥(TauCeti.QuadraticMap.orthogonalGroup (descentForm hTQ)),
      ∀ g w, (((e g : fixSpace T ≃ₗ[descentField σ] fixSpace T) w : fixSpace T) : V) =
        (g : V ≃ₗ[K] V) w := by
  have hσσ' : ∀ a, σ (σ a) = a := fun a => by
    change (σ * σ) a = a
    rw [hσσ]
    rfl
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  have hspan := span_fixSpace hσσ' hTT hc
  have hbij := liftBaseChange_fixSpace_bijective hσσ' hTT hc
  set W := fixSpace T
  set φ := LinearMap.liftBaseChange K W.subtype with hφ
  have hφt : ∀ (a : K) (w : W), φ (a ⊗ₜ w) = a • (w : V) := fun a w => rfl
  have hQt : ∀ (a : K) (w : W), (Q.comp φ) (a ⊗ₜ w) = descentForm hTQ w • (a * a) := by
    intro a w
    rw [QuadraticMap.comp_apply, hφt, QuadraticMap.map_smul, Subfield.smul_def, smul_eq_mul,
      smul_eq_mul, coe_descentForm, mul_comm]
  have hpolar : ∀ (a a' : K) (w w' : W),
      polar (Q.comp φ) (a ⊗ₜ w) (a' ⊗ₜ w') =
        a * a' * ((polar (descentForm hTQ) w w' : descentField σ) : K) := by
    intro a a' w w'
    rw [polar_comp_linearMap, hφt, hφt, polar_smul_left_eq, polar_smul_right_eq,
      coe_polar_descentForm]
    ring
  let φe : K ⊗[descentField σ] W ≃ₗ[K] V := LinearEquiv.ofBijective φ hbij
  have hφe : ∀ x, φe x = φ x := fun x => rfl
  let ext : (W ≃ₗ[descentField σ] W) → (V ≃ₗ[K] V) := fun h =>
    (φe.symm.trans (LinearEquiv.baseChange (descentField σ) K W W h)).trans φe
  have hext_smul : ∀ (h : W ≃ₗ[descentField σ] W) (a : K) (w : W),
      ext h (a • (w : V)) = a • (h w : V) := by
    intro h a w
    have h1 : φe.symm (a • (w : V)) = a ⊗ₜ w := by
      rw [LinearEquiv.symm_apply_eq, hφe, hφt]
    change φe (LinearEquiv.baseChange (descentField σ) K W W h (φe.symm (a • (w : V)))) = _
    rw [h1, LinearEquiv.baseChange_tmul, hφe, hφt]
  have hext : ∀ (h : W ≃ₗ[descentField σ] W) (w : W), ext h w = h w := by
    intro h w
    have := hext_smul h 1 w
    rwa [one_smul, one_smul] at this
  have hagree : ∀ f g : V →ₗ[K] V, (∀ w ∈ W, f w = g w) → f = g := fun f g hfg =>
    LinearMap.ext_on hspan fun w hw => hfg w hw
  have hextT : ∀ h : W ≃ₗ[descentField σ] W, ∀ v, ext h (T v) = T (ext h v) := by
    intro h v
    have hv : v ∈ Submodule.span K (W : Set V) := hspan ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rw [mem_fixSpace.1 hx]
      have h1 := hext h ⟨x, hx⟩
      simp only at h1
      rw [h1, mem_fixSpace.1 (h ⟨x, hx⟩).2]
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | smul a x _ hx => rw [map_smulₛₗ, map_smul, hx, map_smul, map_smulₛₗ]
  have hextO : ∀ h ∈ TauCeti.QuadraticMap.orthogonalGroup (descentForm hTQ),
      ext h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro h hh
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hh ⊢
    intro v
    have hv : v ∈ Submodule.span K (W : Set V) := hspan ▸ Submodule.mem_top
    refine eq_of_eq_on_span (Q₁ := Q.comp (ext h : V →ₗ[K] V)) (Q₂ := Q) ?_ ?_ hv
    · intro x hx
      rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe]
      have h1 := hext h ⟨x, hx⟩
      simp only at h1
      rw [h1, ← coe_descentForm hTQ, ← coe_descentForm hTQ ⟨x, hx⟩, hh]
    · intro x hx y hy
      rw [polar_comp_linearMap, LinearEquiv.coe_coe]
      have h1 := hext h ⟨x, hx⟩
      have h2 := hext h ⟨y, hy⟩
      simp only at h1 h2
      rw [h1, h2, ← coe_polar_descentForm hTQ, ← coe_polar_descentForm hTQ ⟨x, hx⟩ ⟨y, hy⟩,
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          ((TauCeti.QuadraticMap.mem_orthogonalGroup_iff).2 hh)]
  have hresO : ∀ (g : V ≃ₗ[K] V)
      (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ⊓ semilinCentralizer T),
      restrictFix (Subgroup.mem_inf.1 hg).2 ∈
        TauCeti.QuadraticMap.orthogonalGroup (descentForm hTQ) := by
    intro g hg
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    refine Subtype.ext ?_
    rw [coe_descentForm, coe_descentForm, coe_restrictFix, map_of_mem (Subgroup.mem_inf.1 hg).1]
  refine ⟨finrank_fixSpace hσσ' hTT hc, hbij, fun w => coe_descentForm hTQ w,
    nondegenerate_descentForm hTQ hQ hspan, hQt, hpolar,
    fun Q' hQ' => baseChange_ext fun w => by rw [hQ', QuadraticMap.comp_apply, hφt, one_smul]; rfl,
    ⟨{ toFun := fun g => ⟨restrictFix (Subgroup.mem_inf.1 g.2).2, hresO g g.2⟩
       invFun := fun h => ⟨ext h, hextO h h.2, fun v => hextT h v⟩
       left_inv := fun g => ?_
       right_inv := fun h => ?_
       map_mul' := fun g g' => ?_ }, fun g w => rfl⟩⟩
  · refine Subtype.ext (LinearEquiv.toLinearMap_injective (hagree _ _ fun w hw => ?_))
    change ext _ w = (g : V ≃ₗ[K] V) w
    have h1 := hext (restrictFix (Subgroup.mem_inf.1 g.2).2) ⟨w, hw⟩
    simp only at h1
    rw [h1, coe_restrictFix]
  · refine Subtype.ext (LinearEquiv.ext fun w => Subtype.ext ?_)
    change ext h.1 w = (h.1 w : V)
    exact hext h.1 w
  · refine Subtype.ext (LinearEquiv.ext fun w => Subtype.ext ?_)
    rfl

end CFSG.ComponentClassification.UnbalancedCatalog
