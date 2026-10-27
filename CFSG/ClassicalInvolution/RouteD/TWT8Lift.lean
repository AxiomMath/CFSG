module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Rec
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Generic

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_involution_lift {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q}
    (hα : IsConj α g) (x : spinGroup Q) (hφ : ∀ c', g.φ c' = c') {r : F} (hr0 : r ≠ 0)
    (hrr : r * r = ((g.conjSpin x).μ : F))
    (hGGv : ∀ v, (g.conjSpin x) ((g.conjSpin x) v) = (r * r) • v) :
    ∃ g₀ : V ≃ₗ[F] V, g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction Q (α y) (g₀ z) = g₀ (spinAction Q y z)) ∧
      ∀ v, g₀ (spinAction Q x v) = spinAction Q x (r⁻¹ • (g.conjSpin x) v) := by
  classical
  have hφ₁ : ∀ c', (g.conjSpin x).φ c' = c' := hφ
  let G : V →ₗ[F] V := (g.conjSpin x).toLinear hφ₁
  have hG : ∀ v, G v = g.conjSpin x v := fun v => rfl
  have hGGv' : ∀ v, G (G v) = (r * r) • v := fun v => hGGv v
  set μ : F := ((g.conjSpin x).μ : F) with hμdef
  have hμ : ∀ v, Q (G v) = μ * Q v := fun v => by
    rw [hG, (g.conjSpin x).map_Q v, hφ₁]
  have hDD' : (r⁻¹ • G) ∘ₗ (r⁻¹ • G) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, hGGv', smul_smul,
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
      rw [hDmv, smul_smul, mul_inv_cancel₀ hr0, one_smul]
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
  refine ⟨g₀, hiso, hsq, hconj, fun v => ?_⟩
  rw [hg₀, spinAction_inv_apply, hDmv]
  rfl

end Generic

section Lift

variable {F : Type} [Field F] {n : ℕ} {b c : F}

theorem exists_lift_of_scalar_minus (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {α : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c)}
    {g : SemiSim (quadMinus n F b c)} (hα : IsConj α g) (hα2 : ∀ y, α (α y) = y)
    (x : spinGroup (quadMinus n F b c)) {O : Fin (n - 1) → Prop} {a₁ a₂ : Fin (n - 1)}
    (ha₁ : O a₁) (ha₂ : O a₂) (h12 : a₁ ≠ a₂) (hφ : ∀ c', g.φ c' = c')
    (hO : ∀ (a b' : Fin (n - 1)) (hab : a ≠ b'), O a → O b' → ∀ (s t : Bool) (c' : F),
      conjTwist α x ((minusFrame n b c).longRoot hab s t (.ofAdd c')) =
        (minusFrame n b c).longRoot hab s t (.ofAdd c')) :
    ∃ g₀ : Vm n F ≃ₗ[F] Vm n F,
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadMinus n F b c) (α y) (g₀ z) =
        g₀ (spinAction (quadMinus n F b c) y z)) ∧
      ∀ a, O a → ∀ s, g₀ (spinAction (quadMinus n F b c) x ((minusFrame n b c).vec a s)) =
        spinAction (quadMinus n F b c) x ((minusFrame n b c).vec a s) := by
  classical
  set Fr := minusFrame n b c with hFr
  have hα₁ : IsConj (conjTwist α x) (g.conjSpin x) := hα.conjSpin x
  have hα₁2 : ∀ y, conjTwist α x (conjTwist α x y) = y := conjTwist_sq α hα2 x
  have hφ₁ : ∀ c', (g.conjSpin x).φ c' = c' := hφ
  let G : Vm n F →ₗ[F] Vm n F := (g.conjSpin x).toLinear hφ₁
  have hG : ∀ v, G v = g.conjSpin x v := fun v => rfl
  set μ : F := ((g.conjSpin x).μ : F) with hμdef
  have hμ : ∀ v, quadMinus n F b c (G v) = μ * quadMinus n F b c v := fun v => by
    rw [hG, (g.conjSpin x).map_Q v, hφ₁]
  have hμ0 : μ ≠ 0 := (g.conjSpin x).μ.ne_zero
  have hGinj : Function.Injective G := fun a b h => (g.conjSpin x).bijective.1 h
  have hcommO : ∀ a b', a ≠ b' → O a → O b' → ∀ (s t : Bool) v,
      G (eichler (quadMinus n F b c) (Fr.vec b' t) (Fr.vec a s) v) =
        eichler (quadMinus n F b c) (Fr.vec b' t) (Fr.vec a s) (G v) := by
    intro a b' hab ha hb s t v
    have e := Fr.spinAction_longRoot_eq_eichler hab s t 1
    rw [one_smul] at e
    have h1 := hα₁ (Fr.longRoot hab s t (.ofAdd 1)) v
    rw [hO a b' hab ha hb s t 1, e] at h1
    exact h1.symm
  obtain ⟨r, hr0, hrr, hr⟩ := diag_of_commuting_roots Fr.toHypFrame G hGinj hμ (O := O) ha₁ ha₂
    h12 hcommO
  have hcomm2 : ∀ a b', a ≠ b' → ∀ (s t : Bool) v,
      G (G (eichler (quadMinus n F b c) (Fr.vec b' t) (Fr.vec a s) v)) =
        eichler (quadMinus n F b c) (Fr.vec b' t) (Fr.vec a s) (G (G v)) := by
    intro a b' hab s t v
    have e := Fr.spinAction_longRoot_eq_eichler hab s t 1
    rw [one_smul] at e
    have h1 := IsConj.comm_sq hα₁ hα₁2 (Fr.longRoot hab s t (.ofAdd 1)) v
    rw [e] at h1
    exact h1
  have hGG : ∀ v, quadMinus n F b c ((G ∘ₗ G) v) = (μ * μ) * quadMinus n F b c v := fun v => by
    simp only [LinearMap.comp_apply, hμ]
    ring
  obtain ⟨r', hr'0, hr'r', hr'⟩ := diag_of_commuting_roots Fr.toHypFrame (G ∘ₗ G)
    (hGinj.comp hGinj) hGG
    (O := fun _ => True) (a₁ := a₁) (a₂ := a₂) trivial trivial h12
    (fun a b' hab _ _ s t v => by
      simp only [LinearMap.comp_apply]
      exact hcomm2 a b' hab s t v)
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
  have hGGw' : ∀ a s, G (G (minusVec n a s)) = (r * r) • minusVec n a s := hGGw
  have hGGp : ∀ w, G (G (planeVec n w)) = (r * r) • planeVec n w := by
    intro w
    let S := spinAction (quadMinus n F b c) (twShortRoot n hirr a₁ true (.ofAdd w))
    have hu : polar (quadMinus n F b c) (minusVec n a₁ false) (minusVec n a₁ true) = 1 := by
      have := polar_minusVec_minusVec n (K := F) b c a₁ a₁ false true
      simpa using this
    have hup : polar (quadMinus n F b c) (minusVec n a₁ false) (planeVec n w) = 0 :=
      polar_minusVec_planeVec n b c a₁ false w
    have hSf : S (minusVec n a₁ false) = minusVec n a₁ false + planeVec n w -
        planeNorm b c w • minusVec n a₁ true := by
      show spinAction (quadMinus n F b c) (twShortRoot n hirr a₁ true (.ofAdd w)) _ = _
      rw [spinAction_twShortRoot, hu, hup]
      simp
    have hs : G (G (S (minusVec n a₁ false))) = S (G (G (minusVec n a₁ false))) :=
      IsConj.comm_sq hα₁ hα₁2 _ _
    rw [hGGw' a₁ false, map_smul, hSf] at hs
    simp only [map_sub, map_add, map_smul, hGGw'] at hs
    have e3 : G (G (planeVec n w)) - (r * r) • planeVec n w = 0 := by
      have := sub_eq_zero.mpr hs
      rw [← this]
      module
    exact sub_eq_zero.mp e3
  have hbasis : ∀ (j : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (y : F),
      G (G (Pi.single j y : Vm n F)) = (r * r) • (Pi.single j y : Vm n F) := by
    intro j y
    have hy : (Pi.single j y : Vm n F) = y • (Pi.single j 1 : Vm n F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hy, map_smul, map_smul, smul_comm]
    congr 1
    rcases j with i | i | t
    · exact hGGw' i true
    · exact hGGw' i false
    · have : (Pi.single (.inr (.inr t)) 1 : Vm n F) = planeVec n (Pi.single t 1) := by
        funext x
        rcases x with i | i | t'
        · simp [planeVec]
        · simp [planeVec]
        · simp [planeVec, Pi.single_apply]
      rw [this]
      exact hGGp _
  have hGGv : ∀ v, G (G v) = (r * r) • v := by
    intro v
    have key : G ∘ₗ G = (r * r) • (LinearMap.id : Vm n F →ₗ[F] Vm n F) :=
      LinearMap.pi_ext fun j y => by
        simpa using hbasis j y
    have := LinearMap.congr_fun key v
    simpa using this
  obtain ⟨g₀, hiso, hsq, hconj, hg₀⟩ := exists_involution_lift hα x hφ hr0 hrr
    (fun v => hGGv v)
  refine ⟨g₀, hiso, hsq, hconj, fun a ha s => ?_⟩
  have hGv : (g.conjSpin x) ((minusFrame n b c).vec a s) = G ((minusFrame n b c).vec a s) := rfl
  rw [hg₀, hGv, hr a ha s, smul_smul, inv_mul_cancel₀ hr0, one_smul]

end Lift

section Rec

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B4 CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]


theorem lift_td5 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (θ : spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {RM RM' : Subgroup (spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr p f)))
    (hRM'f : RM' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr p f)))
    (hne : RM' ≠ RM)
    (htwin : ∀ i j, IsFundamental (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) (RM.map (spinAction (quadMinus 5 (GaloisField p f)
          (minusCoeffs p f).1 (minusCoeffs p f).2))) i →
      IsFundamental (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        (RM'.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2))) j → i = j)
    (hfixM : ∀ y ∈ RM, σ (θ y) = θ y) (hfixM' : ∀ y ∈ RM', σ (θ y) = θ y) :
    ∃ (x : spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
      (α : spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ≃*
        spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
      (g₀ : Vm 5 (GaloisField p f) ≃ₗ[GaloisField p f] Vm 5 (GaloisField p f)),
      RM = ((rootSL2 (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 2 3
        (by omega) (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      RM' = ((rootSL2 (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 2 3
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, θ (α y) = σ (θ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) (α y) (g₀ z) =
        g₀ (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) y z)) ∧
      (∀ a : Fin (5 - 1), 2 ≤ a.val → ∀ s,
        g₀ (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) x ((minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).vec a s)) =
        spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x
          ((minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).vec a s)) := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have hadm : StatedLieAdmissible .POmegaMinus 5 p f := ⟨Fact.out, hf, by show 4 ≤ 5; omega⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hq4 : 4 ≤ p ^ f := by omega
  have hirr := minusCoeffs_irr p f
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f 5 (by omega)]
    omega
  have hQ : (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField p f) hirr)
  set F₀ : HypFrame (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
      (5 - 1) := (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame with hF₀
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRMf
  obtain ⟨FM, hFM, hiMe⟩ := hiM
  obtain ⟨x, hx1, hx2⟩ := exists_spin_twin_pair hodd hQ F₀ hdim FM
  have hRM : RM = ((rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true true).map
      (MulAut.conj x).toMonoidHom) :=
    cq.map_inj hRMf (rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ true true x) (by rw [hFM, hx1])
  obtain ⟨iM', hiM'⟩ := cq.map_mem _ hRM'f
  obtain ⟨FM', hFM', hiM'e⟩ := hiM'
  have hii : FM'.La (-1) = FM.La (-1) := by
    have := htwin iM iM' ⟨FM, hFM, hiMe⟩ ⟨FM', hFM', hiM'e⟩
    rw [← hiMe, ← hiM'e]
    exact this.symm
  have hRM' : RM' = ((rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj x).toMonoidHom) := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with h | h
    · exact absurd (cq.map_inj hRM'f hRMf (by rw [hFM', h, hFM])) hne
    · exact cq.map_inj hRM'f (rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ true false x)
        (by rw [hFM', h, hx2])
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_minus hp2 (by norm_num : 4 ≤ 5) hf hK hirr θ hker σ
    hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := isPerfect_spinGroup_quadMinus (by norm_num : 4 ≤ 5) hirr
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) →* _).comp
      (α : spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) →* _))
      (MonoidHom.id (spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hαM : ∀ r ∈ RM, α r = r :=
    eq_of_fixed_of_perfect θ hker α σ hαθ (cq.perf _ hRMf) hfixM
  have hαM' : ∀ r ∈ RM', α r = r :=
    eq_of_fixed_of_perfect θ hker α σ hαθ (cq.perf _ hRM'f) hfixM'
  let i2 : Fin (5 - 1) := ⟨2, by omega⟩
  let i3 : Fin (5 - 1) := ⟨3, by omega⟩
  have h23 : i2 ≠ i3 := fun h => by have := congrArg Fin.val h; simp [i2, i3] at this
  have h32 : i3 ≠ i2 := h23.symm
  have hmem : ∀ (s t : Bool) (c : GaloisField p f), ∃ t' : Bool,
      F₀.longRoot h23 s t (.ofAdd c) ∈
        rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true t' := by
    intro s t c
    cases s
    · refine ⟨!t, ?_⟩
      rw [F₀.longRoot_swap h23 false t c]
      have e : F₀.longRoot h23.symm t false (.ofAdd (-c)) =
          F₀.longSL2 h23 true (!t) (lowerSL2 (-c)) := by
        rw [HypFrame.longSL2_lowerSL2]
        simp
      show _ ∈ (F₀.longSL2 h23 true (!t)).range
      rw [e]
      exact ⟨_, rfl⟩
    · refine ⟨t, ?_⟩
      show _ ∈ (F₀.longSL2 h23 true t).range
      rw [← HypFrame.longSL2_upperSL2]
      exact ⟨_, rfl⟩
  have hfix23 : ∀ (s t : Bool) (c : GaloisField p f),
      conjTwist α x (F₀.longRoot h23 s t (.ofAdd c)) = F₀.longRoot h23 s t (.ofAdd c) := by
    intro s t c
    obtain ⟨t', ht'⟩ := hmem s t c
    have hy : x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹ ∈
        (rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true t').map
          (MulAut.conj x).toMonoidHom := ⟨_, ht', rfl⟩
    have hα' : α (x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹) =
        x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹ := by
      cases t'
      · rw [← hRM'] at hy
        exact hαM' _ hy
      · rw [← hRM] at hy
        exact hαM _ hy
    rw [conjTwist_apply, hα']
    group
  have hO : ∀ (a b : Fin (5 - 1)) (hab : a ≠ b), (fun a : Fin (5 - 1) => 2 ≤ a.val) a →
      (fun a : Fin (5 - 1) => 2 ≤ a.val) b → ∀ (s t : Bool) (c : GaloisField p f),
      conjTwist α x ((minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hab s t
        (.ofAdd c)) =
        (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hab s t (.ofAdd c) := by
    intro a b hab ha hb s t c
    have ha' : a = i2 ∨ a = i3 := by
      have ha2 : 2 ≤ a.val := ha
      have ha3 := a.isLt
      rcases (by omega : a.val = 2 ∨ a.val = 3) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    have hb' : b = i2 ∨ b = i3 := by
      have hb2 : 2 ≤ b.val := hb
      have hb3 := b.isLt
      rcases (by omega : b.val = 2 ∨ b.val = 3) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hab
    · exact hfix23 s t c
    · rw [show (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hab s t
          (.ofAdd c) = F₀.longRoot hab s t (.ofAdd c) from rfl, F₀.longRoot_swap h32 s t c]
      exact hfix23 t s (-c)
    · exact absurd rfl hab
  have hA1 : ∀ c, conjTwist α x (F₀.longRoot h23 true true (.ofAdd c)) =
      F₀.longRoot h23 true true (.ofAdd c) := fun c => hfix23 true true c
  have hφ : ∀ c, g.φ c = c := fun c => (hα.conjSpin x).phi_eq_of_fix F₀ h23 true true hA1 c
  obtain ⟨g₀, hg₀O, hg₀2, hconj, hfixv⟩ := exists_lift_of_scalar_minus hirr hα hα2 x
    (O := fun a : Fin (5 - 1) => 2 ≤ a.val) (a₁ := i2) (a₂ := i3) (by simp [i2]) (by simp [i3])
    h23 hφ hO
  exact ⟨x, α, g₀, hRM, hRM', hαθ, hg₀O, hg₀2, hconj, fun a ha s => hfixv a ha s⟩

end Rec

end CFSG.ClassicalInvolution.RouteD.TWT8
