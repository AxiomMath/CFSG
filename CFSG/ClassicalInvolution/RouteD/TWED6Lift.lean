module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.D6

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Lift

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
theorem exists_lift_of_scalar (Fr : HypFrame Q m)
    (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0)
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
  obtain ⟨r, hr0, hrr, hr⟩ := diag_of_commuting_roots Fr G hGinj hμ (O := O) ha₁ ha₂ h12 hcommO
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
  obtain ⟨r', hr'0, hr'r', hr'⟩ := diag_of_commuting_roots Fr (G ∘ₗ G) (hGinj.comp hGinj) hGG
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
      (polar_vec_ne_zero Fr a₁ true))).symm
  have hrr0 : r * r ≠ 0 := mul_ne_zero hr0 hr0
  have hGGv : ∀ v, G (G v) = (r * r) • v := by
    intro v
    have hpol := polar_map_of_similitude (G ∘ₗ G) hGG
    have key : ∀ a s, polar Q (G (G v)) (Fr.vec a s) = (r * r) * polar Q v (Fr.vec a s) := by
      intro a s
      have h1 := hpol v (Fr.vec a s)
      simp only [LinearMap.comp_apply] at h1
      have h2' : G (G (Fr.vec a s)) = (r * r) • Fr.vec a s := by
        have := hr' a trivial s
        simpa only [LinearMap.comp_apply, hr''] using this
      rw [h2', polar_smul_right, hμdef] at h1
      have hμeq : μ = r * r := hrr.symm
      rw [← hμdef, hμeq] at h1
      have h3 : (r * r) * (polar Q (G (G v)) (Fr.vec a s) - (r * r) * polar Q v (Fr.vec a s)) =
          0 := by
        simp only [smul_eq_mul] at h1
        linear_combination h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hrr0
      · linear_combination h
    have hz := hspan (G (G v) - (r * r) • v) (fun a s => by
      rw [polar_sub_left, polar_smul_left, key a s]
      simp only [smul_eq_mul]
      ring)
    exact sub_eq_zero.mp hz
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

section Plus

variable {p f : ℕ} [Fact p.Prime]


theorem toral_lift_plus_six (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (θ : spinGroup (quadPlus 6 (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus 6 (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus 6 (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus 6 (GaloisField p f)))}
    (hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) (by norm_num)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) (by norm_num)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) (by norm_num)))
    (hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b))
    (hM : ∀ a ≤ 2, Commutes RM (R a))
    (hdist : ∀ i j, IsFundamental (quadPlus 6 (GaloisField p f))
      ((R 0).map (spinAction (quadPlus 6 (GaloisField p f)))) i →
      IsFundamental (quadPlus 6 (GaloisField p f))
        ((R 2).map (spinAction (quadPlus 6 (GaloisField p f)))) j → i ≠ j)
    (hne : Rtw ≠ R 2)
    (htwin : ∀ i j, IsFundamental (quadPlus 6 (GaloisField p f))
      ((R 2).map (spinAction (quadPlus 6 (GaloisField p f)))) i →
      IsFundamental (quadPlus 6 (GaloisField p f))
        (Rtw.map (spinAction (quadPlus 6 (GaloisField p f)))) j → i = j)
    (hfix : ∀ a, 1 ≤ a → a ≤ 2 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (x : spinGroup (quadPlus 6 (GaloisField p f))) (t : Bool)
      (α : spinGroup (quadPlus 6 (GaloisField p f)) ≃* spinGroup (quadPlus 6 (GaloisField p f)))
      (g₀ : (Fin 6 ⊕ Fin 6 → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 6 ⊕ Fin 6 → GaloisField p f)),
      (∀ a (ha : a ≤ 2), R a = ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 2 3 (by omega) (by omega)
        (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      RM = ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 4 5 (by omega) (by omega)
        (by omega) true t).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, θ (α y) = σ (θ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField p f)) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadPlus 6 (GaloisField p f)) (α y) (g₀ z) =
        g₀ (spinAction (quadPlus 6 (GaloisField p f)) y z)) ∧
      (∀ a : Fin 6, 1 ≤ a.val → a.val ≤ 3 → ∀ s,
        g₀ (spinAction (quadPlus 6 (GaloisField p f)) x
          ((plusFrame 6 (GaloisField p f) (by norm_num)).vec a s)) =
        spinAction (quadPlus 6 (GaloisField p f)) x
          ((plusFrame 6 (GaloisField p f) (by norm_num)).vec a s)) := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := centralQuot_plus (m := 6) hp2 (by norm_num) hm3 hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin 6 ⊕ Fin 6 → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hQ : (quadPlus 6 (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 6 (GaloisField p f))
  set F₀ := plusFrame 6 (GaloisField p f) hm3 with hF₀
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := 2) (by omega) F₀
    hdim cq hRf hRtwf hRMf hadj hlin hcomm hM
    (fun a b hab hb i j hi hj => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
      exact hdist i j hi hj) hne htwin
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift hp2 (by norm_num : 5 ≤ 6) hf hK θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadPlus 6 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadPlus 6 (GaloisField p f)) →* _).comp
      (α : spinGroup (quadPlus 6 (GaloisField p f)) →* _))
      (MonoidHom.id (spinGroup (quadPlus 6 (GaloisField p f)))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  obtain ⟨hZ, hcent⟩ := plus_center_facts (F := GaloisField p f) hp2 hm3
  have hscal : ∀ z ∈ Subgroup.center (spinGroup (quadPlus 6 (GaloisField p f))),
      ∃ η : GaloisField p f, ∀ v, spinAction (quadPlus 6 (GaloisField p f)) z v = η • v :=
    fun z hz => by
      obtain ⟨η, -, hη⟩ := hcent z hz
      exact ⟨η, hη⟩
  obtain ⟨H1g, H2g, -⟩ := frame_chain_fixed_data (s := 2) (by omega) F₀ θ hker σ hscal x t hxR hxtw
    hxM hfix hfixtw hfixM hnorm0
  let i₀ : Fin 6 := ⟨4, by omega⟩
  let i₁ : Fin 6 := ⟨5, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hfixr : ∀ {i j : Fin 6} (hij : i ≠ j) (s' t' : Bool) (c : GaloisField p f),
      σ (θ (x * F₀.longRoot hij s' t' (.ofAdd c) * x⁻¹)) =
        θ (x * F₀.longRoot hij s' t' (.ofAdd c) * x⁻¹) →
      conjTwist α x (F₀.longRoot hij s' t' (.ofAdd c)) = F₀.longRoot hij s' t' (.ofAdd c) :=
    fun hij s' t' c h => conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ x
      (longRoot_pow_char F₀ hij s' t' c) (longRoot_pow_char F₀ hij s' t' c) h
  have hA1 : ∀ c, conjTwist α x (F₀.longRoot h01 true t (.ofAdd c)) =
      F₀.longRoot h01 true t (.ofAdd c) := fun c =>
    hfixr h01 true t c (H1g _ ⟨F₀.longRoot h01 true t (.ofAdd c),
      ⟨upperSL2 c, HypFrame.longSL2_upperSL2 F₀ _ true t c⟩, rfl⟩)
  have hO : ∀ (a b : Fin 6) (hab : a ≠ b), (a.val ≠ 4 ∧ a.val ≠ 5 ∧ a.val ≠ 0) →
      (b.val ≠ 4 ∧ b.val ≠ 5 ∧ b.val ≠ 0) → ∀ (s' t' : Bool) (c : GaloisField p f),
      conjTwist α x (F₀.longRoot hab s' t' (.ofAdd c)) = F₀.longRoot hab s' t' (.ofAdd c) :=
    fun a b hab ha hb s' t' c => hfixr hab s' t' c
      (H2g a b hab ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 s' t' c)
  have hφ : ∀ c, g.φ c = c := fun c => (hα.conjSpin x).phi_eq_of_fix F₀ h01 true t hA1 c
  obtain ⟨g₀, hg₀O, hg₀2, hconj, hfixv⟩ := exists_lift_of_scalar F₀ (plus_hspan hm3) hα hα2 x
    (O := fun a => a.val ≠ 4 ∧ a.val ≠ 5 ∧ a.val ≠ 0) (a₁ := ⟨1, by omega⟩) (a₂ := ⟨2, by omega⟩)
    ⟨by simp, by simp, by simp⟩ ⟨by simp, by simp, by simp⟩
    (fun h => by have := congrArg Fin.val h; simp at this) hφ hO
  exact ⟨x, t, α, g₀, hxR, hxtw, hxM, hαθ, hg₀O, hg₀2, hconj,
    fun a h1 h3 s => hfixv a ⟨by omega, by omega, by omega⟩ s⟩

end Plus

end CFSG.ClassicalInvolution.RouteD.TWE.D6
