module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutNormal
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutChar

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Lift

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}

theorem exists_lift_of_scalar_odd (h2 : (2 : F) ≠ 0) (Fr : OddFrame Q m)
    (hperpz : ∀ y : V, (∀ a r, polar Q y (Fr.vec a r) = 0) → ∃ c : F, y = c • Fr.z)
    {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g)
    (hα2 : ∀ y, α (α y) = y) (x : spinGroup Q) {O : Fin m → Prop} {a₁ a₂ : Fin m}
    (ha₁ : O a₁) (ha₂ : O a₂) (h12 : a₁ ≠ a₂) (hφ : ∀ c, g.φ c = c)
    (hO : ∀ (a b : Fin m) (hab : a ≠ b), O a → O b → ∀ (s t : Bool) (c : F),
      conjTwist α x (Fr.longRoot hab s t (.ofAdd c)) = Fr.longRoot hab s t (.ofAdd c)) :
    ∃ g₀ : V ≃ₗ[F] V, g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction Q (α y) (g₀ z) = g₀ (spinAction Q y z)) ∧
      ∀ a, O a → ∀ s, g₀ (spinAction Q x (Fr.vec a s)) = spinAction Q x (Fr.vec a s) := by
  classical
  have hα₁ : IsConj (conjTwist α x) (g.conjSpin x) := hα.conjSpin x
  have hα₁2 : ∀ y, conjTwist α x (conjTwist α x y) = y := conjTwist_sq α hα2 x
  have hφ₁ : ∀ c, (g.conjSpin x).φ c = c := hφ
  let G : V →ₗ[F] V := (g.conjSpin x).toLinear hφ₁
  have hG : ∀ v, G v = g.conjSpin x v := fun v => rfl
  set μ : F := ((g.conjSpin x).μ : F) with hμdef
  have hμ : ∀ v, Q (G v) = μ * Q v := fun v => by
    rw [hG, (g.conjSpin x).map_Q v, hφ₁]
  have hμ0 : μ ≠ 0 := (g.conjSpin x).μ.ne_zero
  have hGinj : Function.Injective G := fun a b h => (g.conjSpin x).bijective.1 h
  have hcommO : ∀ a b, a ≠ b → O a → O b → ∀ (s t : Bool) v,
      G (eichler Q (Fr.vec b t) (Fr.vec a s) v) = eichler Q (Fr.vec b t) (Fr.vec a s) (G v) := by
    intro a b hab ha hb s t v
    have e := Fr.spinAction_longRoot_eq_eichler hab s t 1
    rw [one_smul] at e
    have h1 := hα₁ (Fr.longRoot hab s t (.ofAdd 1)) v
    rw [hO a b hab ha hb s t 1, e] at h1
    exact h1.symm
  obtain ⟨r, hr0, hrr, hr⟩ := diag_of_commuting_roots Fr.toHypFrame G hGinj hμ (O := O) ha₁ ha₂
    h12 hcommO
  have hcomm2 : ∀ a b, a ≠ b → ∀ (s t : Bool) v,
      G (G (eichler Q (Fr.vec b t) (Fr.vec a s) v)) =
        eichler Q (Fr.vec b t) (Fr.vec a s) (G (G v)) := by
    intro a b hab s t v
    have e := Fr.spinAction_longRoot_eq_eichler hab s t 1
    rw [one_smul] at e
    have h1 := IsConj.comm_sq hα₁ hα₁2 (Fr.longRoot hab s t (.ofAdd 1)) v
    rw [e] at h1
    exact h1
  have hGG : ∀ v, Q ((G ∘ₗ G) v) = (μ * μ) * Q v := fun v => by
    simp only [LinearMap.comp_apply, hμ]
    ring
  obtain ⟨r', hr'0, hr'r', hr'⟩ := diag_of_commuting_roots Fr.toHypFrame (G ∘ₗ G)
    (hGinj.comp hGinj) hGG
    (O := fun _ => True) (a₁ := a₁) (a₂ := a₂) trivial trivial h12
    (fun a b hab _ _ s t v => by
      simp only [LinearMap.comp_apply]
      exact hcomm2 a b hab s t v)
  have hr'' : r' = r * r := by
    have h1 := hr' a₁ trivial true
    have h2' := hr a₁ ha₁ true
    have : (G ∘ₗ G) (Fr.vec a₁ true) = (r * r) • Fr.vec a₁ true := by
      simp only [LinearMap.comp_apply, h2', map_smul, smul_smul]
    rw [this] at h1
    have h3 : (r * r - r') • Fr.vec a₁ true = 0 := by rw [sub_smul, h1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right
      (polar_vec_ne_zero Fr.toHypFrame a₁ true))).symm
  have hrr0 : r * r ≠ 0 := mul_ne_zero hr0 hr0
  have hGGw : ∀ a s, G (G (Fr.vec a s)) = (r * r) • Fr.vec a s := by
    intro a s
    have := hr' a trivial s
    simpa only [LinearMap.comp_apply, hr''] using this
  have hGGz : G (G Fr.z) = (r * r) • Fr.z := by
    have hperpv : ∀ a s, polar Q (G (G Fr.z)) (Fr.vec a s) = 0 ∧
        polar Q (G (G Fr.z)) Fr.z = 2 * (r * r) := by
      intro a s
      have hs := IsConj.comm_sq hα₁ hα₁2 (Fr.shortRoot a s (.ofAdd 1)) Fr.z
      rw [Fr.spinAction_shortRoot_z a s 1] at hs
      have hs' : G (G (Fr.z - (2 * 1 : F) • Fr.vec a s)) =
          spinAction Q (Fr.shortRoot a s (.ofAdd 1)) (G (G Fr.z)) := hs
      rw [map_sub, map_sub, map_smul, map_smul, hGGw a s,
        Fr.spinAction_shortRoot a s 1 (G (G Fr.z))] at hs'
      have hli := (LinearIndependent.pair_iff.mp (Fr.linearIndependent_z_vec a s))
        (-(1 * polar Q (G (G Fr.z)) (Fr.vec a s)))
        (-(2 * 1 * (r * r)) + (1 * polar Q (G (G Fr.z)) Fr.z +
          1 ^ 2 * polar Q (G (G Fr.z)) (Fr.vec a s))) (by
        have h3 := sub_eq_zero.mpr hs'
        rw [← h3]
        simp only [smul_smul]
        module)
      refine ⟨by simpa using hli.1, ?_⟩
      have := hli.2
      have h4 : polar Q (G (G Fr.z)) (Fr.vec a s) = 0 := by simpa using hli.1
      rw [h4] at this
      linear_combination this
    obtain ⟨c, hc⟩ := hperpz _ fun a s => (hperpv a s).1
    have h5 := (hperpv a₁ true).2
    rw [hc, polar_smul_left_eq, Fr.polar_z_self] at h5
    have hc2 : c = r * r := by
      have : (2 : F) * (c - r * r) = 0 := by linear_combination h5
      have := (mul_eq_zero.mp this).resolve_left h2
      linear_combination this
    rw [hc, hc2]
  have hGGv : ∀ v, G (G v) = (r * r) • v := by
    intro v
    have hpol := polar_map_of_similitude (G ∘ₗ G) hGG
    have key : ∀ a s, polar Q (G (G v)) (Fr.vec a s) = (r * r) * polar Q v (Fr.vec a s) := by
      intro a s
      have h1 := hpol v (Fr.vec a s)
      simp only [LinearMap.comp_apply] at h1
      rw [hGGw a s, polar_smul_right, hμdef] at h1
      have hμeq : μ = r * r := hrr.symm
      rw [← hμdef, hμeq] at h1
      have h3 : (r * r) * (polar Q (G (G v)) (Fr.vec a s) - (r * r) * polar Q v (Fr.vec a s)) =
          0 := by
        simp only [smul_eq_mul] at h1
        linear_combination h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hrr0
      · linear_combination h
    have keyz : polar Q (G (G v)) Fr.z = (r * r) * polar Q v Fr.z := by
      have h1 := hpol v Fr.z
      simp only [LinearMap.comp_apply] at h1
      rw [hGGz, polar_smul_right, hμdef] at h1
      have hμeq : μ = r * r := hrr.symm
      rw [← hμdef, hμeq] at h1
      have h3 : (r * r) * (polar Q (G (G v)) Fr.z - (r * r) * polar Q v Fr.z) = 0 := by
        simp only [smul_eq_mul] at h1
        linear_combination h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hrr0
      · linear_combination h
    obtain ⟨c, hc⟩ := hperpz (G (G v) - (r * r) • v) (fun a s => by
      rw [polar_sub_left, polar_smul_left, key a s]
      simp only [smul_eq_mul]
      ring)
    have hc0 : c = 0 := by
      have h5 : polar Q (G (G v) - (r * r) • v) Fr.z = 0 := by
        rw [polar_sub_left, polar_smul_left, keyz]
        simp only [smul_eq_mul]
        ring
      rw [hc, polar_smul_left_eq, Fr.polar_z_self] at h5
      have : (2 : F) * c = 0 := by linear_combination h5
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [hc0, zero_smul] at hc
    exact sub_eq_zero.mp hc
  have hDD' : (r⁻¹ • G) ∘ₗ (r⁻¹ • G) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, hGGv, smul_smul,
      LinearMap.id_apply]
    have : r⁻¹ * (r⁻¹ * (r * r)) = 1 := by field_simp
    rw [this, one_smul]
  let Dm : V →ₗ[F] V := r⁻¹ • G
  have hDmv : ∀ v, Dm v = r⁻¹ • G v := fun v => rfl
  have hDD : ∀ v, Dm (Dm v) = v := fun v => by
    have := LinearMap.congr_fun hDD' v
    exact this
  let DmE : V ≃ₗ[F] V := LinearEquiv.ofLinearMap Dm Dm hDD' hDD'
  let g₀ : V ≃ₗ[F] V := (spinAction Q x⁻¹).trans (DmE.trans (spinAction Q x))
  have hg₀ : ∀ v, g₀ v = spinAction Q x (Dm (spinAction Q x⁻¹ v)) := fun v => rfl
  have hgζ : ∀ v, g v = r • g₀ v := by
    intro v
    have e1 : g (spinAction Q x (spinAction Q x⁻¹ v)) =
        spinAction Q x ((g.conjSpin x) (spinAction Q x⁻¹ v)) := by
      simp only [SemiSim.conjSpin_apply, spinAction_apply_inv]
    rw [spinAction_apply_inv] at e1
    have e2 : (g.conjSpin x) (spinAction Q x⁻¹ v) = r • Dm (spinAction Q x⁻¹ v) := by
      simp only [Dm, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hr0, one_smul]
      rfl
    rw [e1, e2, map_smul, hg₀]
  have hiso : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [hg₀, map_spinAction, hDmv, QuadraticMap.map_smul, hμ, map_spinAction]
    have hμeq : μ = r * r := hrr.symm
    rw [hμeq, smul_eq_mul]
    field_simp
  have hsq : g₀ * g₀ = 1 := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply, hg₀, spinAction_inv_apply, hDD, spinAction_apply_inv]
    rfl
  have hconj : ∀ y z, spinAction Q (α y) (g₀ z) = g₀ (spinAction Q y z) := by
    intro y z
    have h := hα y z
    rw [hgζ z, hgζ (spinAction Q y z), map_smul] at h
    exact smul_right_injective _ hr0 h
  refine ⟨g₀, hiso, hsq, hconj, fun a ha s => ?_⟩
  rw [hg₀, spinAction_inv_apply, hDmv, hr a ha s, smul_smul, inv_mul_cancel₀ hr0, one_smul]

end Lift

end CFSG.ClassicalInvolution.RouteD.TWE.B4
