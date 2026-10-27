module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutToral
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPin

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped Matrix MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

section Conjugation

variable {Q : QuadraticForm F V}

theorem spinAction_mul_apply (a b : spinGroup Q) (w : V) :
    spinAction Q (a * b) w = spinAction Q a (spinAction Q b w) := by
  rw [_root_.map_mul]
  rfl

theorem spinAction_apply_inv (k : spinGroup Q) (w : V) :
    spinAction Q k (spinAction Q k⁻¹ w) = w := by
  rw [← spinAction_mul_apply, mul_inv_cancel, _root_.map_one]
  rfl

theorem spinAction_inv_apply (k : spinGroup Q) (w : V) :
    spinAction Q k⁻¹ (spinAction Q k w) = w := by
  rw [← spinAction_mul_apply, inv_mul_cancel, _root_.map_one]
  rfl

namespace SemiSim

@[expose] noncomputable def conjSpin (g : SemiSim Q) (k : spinGroup Q) : SemiSim Q where
  toFun x := spinAction Q k⁻¹ (g (spinAction Q k x))
  φ := g.φ
  μ := g.μ
  map_add x y := by rw [_root_.map_add, g.map_add, _root_.map_add]
  map_smul c x := by rw [_root_.map_smul, g.map_smul, _root_.map_smul]
  bijective := (spinAction Q k⁻¹).bijective.comp (g.bijective.comp (spinAction Q k).bijective)
  map_Q x := by rw [map_spinAction Q k⁻¹, g.map_Q, map_spinAction Q k]

theorem conjSpin_apply (g : SemiSim Q) (k : spinGroup Q) (x : V) :
    g.conjSpin k x = spinAction Q k⁻¹ (g (spinAction Q k x)) := rfl

@[expose] def toLinear (g : SemiSim Q) (hφ : ∀ c, g.φ c = c) : V →ₗ[F] V where
  toFun := g.toFun
  map_add' := g.map_add
  map_smul' c x := by
    rw [g.map_smul, hφ c]
    rfl

theorem toLinear_apply (g : SemiSim Q) (hφ : ∀ c, g.φ c = c) (x : V) :
    g.toLinear hφ x = g x := rfl

end SemiSim

@[expose] def conjTwist (α : spinGroup Q ≃* spinGroup Q) (k : spinGroup Q) :
    spinGroup Q ≃* spinGroup Q :=
  (MulAut.conj k).trans (α.trans (MulAut.conj k⁻¹))

theorem conjTwist_apply (α : spinGroup Q ≃* spinGroup Q) (k y : spinGroup Q) :
    conjTwist α k y = k⁻¹ * α (k * y * k⁻¹) * k := by
  simp [conjTwist, MulAut.conj_apply]

variable {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q}

theorem IsConj.conjSpin (h : IsConj α g) (k : spinGroup Q) :
    IsConj (conjTwist α k) (g.conjSpin k) := by
  intro y z
  rw [conjTwist_apply, SemiSim.conjSpin_apply, SemiSim.conjSpin_apply, spinAction_mul_apply,
    spinAction_mul_apply, spinAction_apply_inv, h (k * y * k⁻¹) (spinAction Q k z),
    spinAction_mul_apply, spinAction_mul_apply, spinAction_inv_apply]

theorem IsConj.comm_sq (h : IsConj α g) (hα2 : ∀ y, α (α y) = y) (y : spinGroup Q) (z : V) :
    g (g (spinAction Q y z)) = spinAction Q y (g (g z)) := by
  have h1 := h (α y) (g z)
  rw [hα2, h y z] at h1
  exact h1.symm

end Conjugation

section Ambiguity

variable {K : Type*} [Group K] {p : ℕ}

theorem eq_of_central_ambiguity (hZ : ∀ ζ ∈ Subgroup.center K, ζ ^ p = 1 → ζ = 1) (α : K ≃* K)
    {y : K} (hy : y ^ p = 1) (h : α y * y⁻¹ ∈ Subgroup.center K) : α y = y := by
  have hαy : α y = (α y * y⁻¹) * y := by group
  have hc : Commute (α y * y⁻¹) y := (Subgroup.mem_center_iff.mp h y).symm
  have hp : (α y * y⁻¹) ^ p = 1 := by
    have h1 : (α y) ^ p = 1 := by rw [← map_pow, hy, map_one]
    rw [hαy, hc.mul_pow, hy, mul_one] at h1
    exact h1
  rw [hαy, hZ _ h hp, one_mul]

end Ambiguity

section PhiFix

variable {Q : QuadraticForm F V} {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q}

theorem IsConj.phi_eq_of_fix (h : IsConj α g) {m : ℕ} (Fr : HypFrame Q m) {i j : Fin m}
    (hij : i ≠ j) (s t : Bool)
    (hfix : ∀ c : F, α (Fr.longRoot hij s t (.ofAdd c)) = Fr.longRoot hij s t (.ofAdd c)) (c : F) :
    g.φ c = c := by
  have hμ : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hQu : Q (Fr.vec j t) = 0 := Fr.map_vec j t
  have hQw : Q (Fr.vec i s) = 0 := Fr.map_vec i s
  have huw : polar Q (Fr.vec j t) (Fr.vec i s) = 0 := Fr.polar_vec_of_ne hij.symm t s
  have hxu : polar Q (Fr.vec j (!t)) (Fr.vec j t) = 1 := Fr.polar_not_vec j t
  have hxw : polar Q (Fr.vec j (!t)) (Fr.vec i s) = 0 := Fr.polar_vec_of_ne hij.symm (!t) s
  have hgu : Q (g (Fr.vec j t)) = 0 := g.map_isSingular hQu
  have hgw : Q (g (Fr.vec i s)) = 0 := g.map_isSingular hQw
  have hgpol : polar Q (g (Fr.vec j t)) (g (Fr.vec i s)) = 0 := by
    rw [g.polar_apply, huw, map_zero, mul_zero]
  obtain ⟨D, hD⟩ : ∃ D : V, D = polar Q (Fr.vec j (!t)) (g (Fr.vec j t)) • g (Fr.vec i s) -
      polar Q (Fr.vec j (!t)) (g (Fr.vec i s)) • g (Fr.vec j t) := ⟨_, rfl⟩
  have hR : ∀ ν : F, eichler Q (g (Fr.vec j t)) (ν • g (Fr.vec i s)) (Fr.vec j (!t)) =
      Fr.vec j (!t) + ν • D := fun ν => by
    have hw'' : polar Q (g (Fr.vec j t)) (ν • g (Fr.vec i s)) = 0 := by
      rw [polar_smul_right, hgpol, smul_zero]
    rw [eichler_apply hgu hw'', polar_smul_right, QuadraticMap.map_smul, hgw, hD]
    simp only [smul_eq_mul]
    module
  have key : ∀ c' : F, c' • Fr.vec i s = ((g.μ : F)⁻¹ * g.φ c') • D := fun c' => by
    have hw : polar Q (Fr.vec j t) (c' • Fr.vec i s) = 0 := by
      rw [polar_smul_right, huw, smul_zero]
    have h1 := h.spinAction_eq_eichler (Fr.spinAction_longRoot_eq_eichler hij s t c') hQu hw
    rw [hfix c', Fr.spinAction_longRoot_eq_eichler hij s t c'] at h1
    have h2 := DFunLike.congr_fun h1 (Fr.vec j (!t))
    have hL : eichler Q (Fr.vec j t) (c' • Fr.vec i s) (Fr.vec j (!t)) =
        Fr.vec j (!t) + c' • Fr.vec i s := by
      rw [eichler_apply hQu hw, polar_smul_right, hxw, hxu, QuadraticMap.map_smul, hQw]
      simp
    rw [hL, g.map_smul, smul_smul, hR] at h2
    exact add_left_cancel h2
  have k1 := key 1
  rw [map_one, mul_one, one_smul] at k1
  have hD' : (g.μ : F) • Fr.vec i s = D := by
    conv_lhs => rw [k1]
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
  have kc := key c
  have hs : (g.μ : F)⁻¹ * g.φ c * g.μ = g.φ c := by field_simp
  rw [← hD', smul_smul, hs] at kc
  have h0 : (c - g.φ c) • Fr.vec i s = 0 := by rw [sub_smul, kc, sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right (polar_vec_ne_zero Fr i s))).symm

end PhiFix

section Diag

variable {Q : QuadraticForm F V} {p : ℕ} [Fact p.Prime] [CharP F p] {m : ℕ}

omit [Fact p.Prime] in
theorem longRoot_pow_char (Fr : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool) (c : F) :
    (Fr.longRoot hij s t (.ofAdd c)) ^ p = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_zero_of_charP, ofAdd_zero, map_one]

omit [Fact p.Prime] [CharP F p] in
theorem conjTwist_eq_of_central (hZ : ∀ ζ ∈ Subgroup.center (spinGroup Q), ζ ^ p = 1 → ζ = 1)
    (α : spinGroup Q ≃* spinGroup Q) (k : spinGroup Q) {x : spinGroup Q} (hx : x ^ p = 1)
    (h : α (k * x * k⁻¹) * (k * x * k⁻¹)⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    conjTwist α k x = x := by
  have hy : (k * x * k⁻¹) ^ p = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have h1 := eq_of_central_ambiguity hZ α hy h
  rw [conjTwist_apply, h1]
  group

theorem conjTwist_mul_inv_mem_center (α : spinGroup Q ≃* spinGroup Q) (k y : spinGroup Q)
    (h : α (k * y * k⁻¹) * (k * y * k⁻¹)⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    conjTwist α k y * y⁻¹ ∈ Subgroup.center (spinGroup Q) := by
  have h1 := Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center (spinGroup Q)).Normal) _ h k⁻¹
  have h2 : conjTwist α k y * y⁻¹ = k⁻¹ * (α (k * y * k⁻¹) * (k * y * k⁻¹)⁻¹) * k⁻¹⁻¹ := by
    rw [conjTwist_apply]
    group
  rw [h2]
  exact h1

theorem conjTwist_sq (α : spinGroup Q ≃* spinGroup Q) (hα2 : ∀ y, α (α y) = y)
    (k y : spinGroup Q) : conjTwist α k (conjTwist α k y) = y := by
  have h1 : k * (k⁻¹ * α (k * y * k⁻¹) * k) * k⁻¹ = α (k * y * k⁻¹) := by group
  rw [conjTwist_apply, conjTwist_apply, h1, hα2]
  group


variable (Fr : HypFrame Q m) {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem exists_diag_form (hm : 5 ≤ m)
    (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0) (h2 : (2 : F) ≠ 0)
    (hp2 : p ≠ 2) (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1)
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup Q), ζ ^ p = 1 → ζ = 1)
    (hcent : ∀ ζ ∈ Subgroup.center (spinGroup Q),
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x, spinAction Q ζ x = η • x)
    {u : Fˣ} (hu1 : (u : F) ≠ 1) (hu2 : (u : F) ≠ -1)
    {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g) (hα2 : ∀ y, α (α y) = y)
    (k : spinGroup Q)
    (hA1 : ∀ c : F, α (k * Fr.longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹) *
      (k * Fr.longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹)⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hA1' : ∀ c : F, α (k * Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹) *
      (k * Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹)⁻¹ ∈
        Subgroup.center (spinGroup Q))
    (hA2 : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ →
      α (k * Fr.longTorus hij true false u * k⁻¹) *
        (k * Fr.longTorus hij true false u * k⁻¹)⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ (κ : spinGroup Q) (lam : Fin m → Bool → F), (∀ i, lam i true * lam i false = g.μ) ∧
      ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
        α (κ * Fr.longRoot hij s t (.ofAdd c) * κ⁻¹) =
          κ * Fr.longRoot hij s t (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * c)))) * κ⁻¹ := by
  classical
  set α₁ := conjTwist α k with hα₁
  set g₁ := g.conjSpin k with hg₁
  have hα₁c : IsConj α₁ g₁ := hα.conjSpin k
  have hfix1 : ∀ c : F, α₁ (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c) := fun c =>
    conjTwist_eq_of_central hZ α k (longRoot_pow_char Fr h01 s₀ t₀ c) (hA1 c)
  have hfix1' : ∀ c : F, α₁ (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) := fun c =>
    conjTwist_eq_of_central hZ α k (longRoot_pow_char Fr h01.symm (!t₀) (!s₀) c) (hA1' c)
  have hφ : ∀ c, g₁.φ c = c := fun c => hα₁c.phi_eq_of_fix Fr h01 s₀ t₀ hfix1 c
  let gL : V →ₗ[F] V := g₁.toLinear hφ
  have hgL : ∀ x, gL x = g₁ x := fun x => rfl
  have hfixSL : ∀ A : SL(2, F), α₁ (Fr.longSL2 h01 s₀ t₀ A) = Fr.longSL2 h01 s₀ t₀ A := by
    intro A
    have := Frame.sl2_apply_mem (Fr.longSL2 h01 s₀ t₀)
      (MonoidHom.eqLocus (α₁ : spinGroup Q →* spinGroup Q) (MonoidHom.id _))
      (fun c => ?_) (fun c => ?_) A
    · exact this
    · rw [← coe_upperSL2_eq_transvection, HypFrame.longSL2_upperSL2]
      exact hfix1 c
    · rw [← coe_lowerSL2_eq_transvection, HypFrame.longSL2_lowerSL2]
      exact hfix1' c
  have hα₁2 : ∀ y, α₁ (α₁ y) = y := conjTwist_sq α hα2 k
  have hI1 : ∀ (A : SL(2, F)) x, gL ((firstFrame Fr h01 s₀ t₀).La A x) =
      (firstFrame Fr h01 s₀ t₀).La A (gL x) := by
    intro A x
    have hLA : (firstFrame Fr h01 s₀ t₀).La A = spinAction Q (Fr.longSL2 h01 s₀ t₀ A) :=
      (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ t₀) A).symm
    rw [hLA, hgL, hgL, ← hα₁c (Fr.longSL2 h01 s₀ t₀ A) x, hfixSL A]
  have hI2 : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ →
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x,
        gL (spinAction Q (Fr.longTorus hij true false u) x) =
          η • spinAction Q (Fr.longTorus hij true false u) (gL x) := by
    intro i j hij hi0 hi1 hj0 hj1
    have hζ := conjTwist_mul_inv_mem_center α k _ (hA2 i j hij hi0 hi1 hj0 hj1)
    obtain ⟨η, hη, hηact⟩ := hcent _ hζ
    refine ⟨η, hη, fun x => ?_⟩
    have e : α₁ (Fr.longTorus hij true false u) = (α₁ (Fr.longTorus hij true false u) *
        (Fr.longTorus hij true false u)⁻¹) * Fr.longTorus hij true false u := by group
    rw [hgL, hgL, ← hα₁c, e, spinAction_mul_apply, hηact]
  have hI3 : ∀ (B : SL(2, F)) x, gL (gL ((firstFrame Fr h01 s₀ t₀).swap.La B x)) =
      (firstFrame Fr h01 s₀ t₀).swap.La B (gL (gL x)) := by
    intro B x
    have hLB : (firstFrame Fr h01 s₀ t₀).swap.La B =
        spinAction Q (Fr.longSL2 h01 s₀ (!t₀) B) := by
      rw [firstFrame, swap_toFrame]
      exact (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ (!t₀)) B).symm
    rw [hLB, hgL, hgL, hgL, hgL]
    exact hα₁c.comm_sq hα₁2 _ x
  obtain ⟨i₂, hi20, hi21⟩ := exists_ne_and_ne (show 3 ≤ m by omega) i₀ i₁
  have hI4 : ∀ x, gL (gL (eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) x)) =
      eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (gL (gL x)) := by
    intro x
    have e := Fr.spinAction_longRoot_eq_eichler (show i₁ ≠ i₂ from hi21.symm) (!t₀) false 1
    rw [one_smul] at e
    rw [← e, hgL, hgL, hgL, hgL]
    exact hα₁c.comm_sq hα₁2 _ x
  have hginj : Function.Injective gL := fun x y hxy => g₁.bijective.1 hxy
  have hμL : ∀ x, Q (gL x) = (g.μ : F) * Q x := fun x => by
    rw [hgL, g₁.map_Q, hφ]
    rfl
  obtain ⟨B, lam, hlam, hprod⟩ :=
    exists_eigenframe Fr h01 s₀ t₀ hm hspan h2 gL hginj hμL hu1 hu2 hI1 hI2 hI3 hi20 hi21 hI4
  set r := Fr.longSL2 h01 s₀ (!t₀) B with hr
  have hρ : (firstFrame Fr h01 s₀ t₀).swap.La B = spinAction Q r := by
    rw [firstFrame, swap_toFrame]
    exact (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ (!t₀)) B).symm
  have hρsymm : ∀ w, ((firstFrame Fr h01 s₀ t₀).swap.La B).symm w = spinAction Q r⁻¹ w :=
    fun w => by
    rw [LinearEquiv.symm_apply_eq, hρ, spinAction_apply_inv]
  have hg₂ : ∀ i s, g.conjSpin (k * r⁻¹) (Fr.vec i s) = lam i s • Fr.vec i s := by
    intro i s
    have h1 := hlam i s
    rw [hρsymm, hρ, hgL] at h1
    rw [SemiSim.conjSpin_apply, mul_inv_rev, inv_inv, spinAction_mul_apply r k⁻¹,
      spinAction_mul_apply k r⁻¹]
    exact h1
  have hα₂c : IsConj (conjTwist α (k * r⁻¹)) (g.conjSpin (k * r⁻¹)) := hα.conjSpin _
  have hφ₂ : ∀ c, (g.conjSpin (k * r⁻¹)).φ c = c := hφ
  refine ⟨k * r⁻¹, lam, hprod, fun i j hij s t c => ?_⟩
  have h3 := IsConj.longRoot_eq hp2 hker2 Fr hα₂c lam (fun _ s => s) hg₂ hij s t c
  have e1 : α (k * r⁻¹ * Fr.longRoot hij s t (.ofAdd c) * (k * r⁻¹)⁻¹) =
      k * r⁻¹ * conjTwist α (k * r⁻¹) (Fr.longRoot hij s t (.ofAdd c)) * (k * r⁻¹)⁻¹ := by
    rw [conjTwist_apply]
    group
  rw [e1, h3, hφ₂ c]
  rfl

end Diag

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
