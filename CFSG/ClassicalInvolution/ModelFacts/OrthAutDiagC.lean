module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutCompl
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiag

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped Matrix MatrixGroups

section DiagCompl

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {p : ℕ} [Fact p.Prime] [CharP F p] {m : ℕ} (Fr : HypFrame Q m) {i₀ i₁ : Fin m}
  (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem exists_diag_form_compl (hm : 4 ≤ m) (h2 : (2 : F) ≠ 0)
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
    (hA2 : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ t : Bool,
      α (k * Fr.longTorus hij true t u * k⁻¹) *
        (k * Fr.longTorus hij true t u * k⁻¹)⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ (κ : spinGroup Q) (lam : Fin m → Bool → F), (∀ c, g.φ c = c) ∧
      (∀ i, lam i true * lam i false = g.μ) ∧
      (∀ i s, g.conjSpin κ (Fr.vec i s) = lam i s • Fr.vec i s) ∧
      (∀ y : V, (∀ a r, polar Q y (Fr.vec a r) = 0) →
        ∀ a r, polar Q (g.conjSpin κ y) (Fr.vec a r) = 0) ∧
      (∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
        α (κ * Fr.longRoot hij s t (.ofAdd c) * κ⁻¹) =
          κ * Fr.longRoot hij s t (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * c)))) * κ⁻¹) ∧
      ∃ r : spinGroup Q, κ = k * r⁻¹ ∧
        ∀ x : V, (firstFrame Fr h01 s₀ t₀).coords x = 0 → spinAction Q r x = x := by
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
  have hI2 : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ t : Bool,
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x,
        gL (spinAction Q (Fr.longTorus hij true t u) x) =
          η • spinAction Q (Fr.longTorus hij true t u) (gL x) := by
    intro i j hij hi0 hi1 hj0 hj1 t
    have hζ := conjTwist_mul_inv_mem_center α k _ (hA2 i j hij hi0 hi1 hj0 hj1 t)
    obtain ⟨η, hη, hηact⟩ := hcent _ hζ
    refine ⟨η, hη, fun x => ?_⟩
    have e : α₁ (Fr.longTorus hij true t u) = (α₁ (Fr.longTorus hij true t u) *
        (Fr.longTorus hij true t u)⁻¹) * Fr.longTorus hij true t u := by group
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
  obtain ⟨B, lam, hlam, hprod, hC⟩ :=
    exists_eigenframe_compl Fr h01 s₀ t₀ hm h2 gL hginj hμL hu1 hu2 hI1 hI2 hI3 hi20 hi21 hI4
  set r := Fr.longSL2 h01 s₀ (!t₀) B with hr
  have hρ : (firstFrame Fr h01 s₀ t₀).swap.La B = spinAction Q r := by
    rw [firstFrame, swap_toFrame]
    exact (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ (!t₀)) B).symm
  have hρsymm : ∀ w, ((firstFrame Fr h01 s₀ t₀).swap.La B).symm w = spinAction Q r⁻¹ w :=
    fun w => by
    rw [LinearEquiv.symm_apply_eq, hρ, spinAction_apply_inv]
  have hconj : ∀ y, g.conjSpin (k * r⁻¹) y = (firstFrame Fr h01 s₀ t₀).swap.La B
      (gL (((firstFrame Fr h01 s₀ t₀).swap.La B).symm y)) := by
    intro y
    rw [hρsymm, hρ, hgL, SemiSim.conjSpin_apply, mul_inv_rev, inv_inv,
      spinAction_mul_apply r k⁻¹, spinAction_mul_apply k r⁻¹]
    rfl
  have hg₂ : ∀ i s, g.conjSpin (k * r⁻¹) (Fr.vec i s) = lam i s • Fr.vec i s := fun i s => by
    rw [hconj]
    exact hlam i s
  have hα₂c : IsConj (conjTwist α (k * r⁻¹)) (g.conjSpin (k * r⁻¹)) := hα.conjSpin _
  have hφ₂ : ∀ c, (g.conjSpin (k * r⁻¹)).φ c = c := hφ
  refine ⟨k * r⁻¹, lam, hφ, hprod, hg₂, fun y hy a r' => ?_, fun i j hij s t c => ?_,
    r, rfl, fun x hx => ?_⟩
  · rw [hconj]
    exact hC y hy a r'
  · have h3 := IsConj.longRoot_eq hp2 hker2 Fr hα₂c lam (fun _ s => s) hg₂ hij s t c
    have e1 : α (k * r⁻¹ * Fr.longRoot hij s t (.ofAdd c) * (k * r⁻¹)⁻¹) =
        k * r⁻¹ * conjTwist α (k * r⁻¹) (Fr.longRoot hij s t (.ofAdd c)) * (k * r⁻¹)⁻¹ := by
      rw [conjTwist_apply]
      group
    rw [e1, h3, hφ₂ c]
    rfl
  · rw [← hρ]
    exact Frame.La_apply_of_coords_eq_zero (firstFrame Fr h01 s₀ t₀).swap B
      (by rw [Frame.coords_swap, hx, map_zero])

end DiagCompl

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
