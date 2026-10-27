module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinusNormalized

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.ModelFacts.OrthAut
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

section Defs

variable {F : Type} [Field F] {n : ℕ} {b c : F} {X : Type} [Group X]

@[expose] def MinusLift (θ : spinGroup (quadMinus n F b c) →* X) (σ : X ≃* X) : Prop :=
  ∃ (α : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c))
    (g₀ : Vm n F ≃ₗ[F] Vm n F),
    (∀ y, θ (α y) = σ (θ y)) ∧ g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c) ∧
    g₀ * g₀ = 1 ∧
    ∀ y z, spinAction (quadMinus n F b c) (α y) (g₀ z) = g₀ (spinAction (quadMinus n F b c) y z)

end Defs

section SqData

variable {F : Type} [Field F] [Finite F] {n : ℕ} {b c : F}
  {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0}
  {A : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c)}
  {lam : Fin (n - 1) → Bool → F} {μ : F} {L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)}

omit [Finite F] in
theorem minusAct_sq_data (h2 : (2 : F) ≠ 0) (h : MinusAct hirr A lam μ L) (i₀ : Fin (n - 1)) :
    (∀ i s, lam i s * lam i s = μ) ∧ ∀ w, L (L w) = μ • w := by
  have hp0 : (planeOne : Fin 2 → F) ≠ 0 := planeOne_ne_zero
  have hμ0 := h.ne_zero
  have hLLne : L (L planeOne) ≠ 0 := by
    intro h0
    have h1 := h.norm (L planeOne)
    rw [h0, planeNorm_zero, h.norm planeOne, planeNorm_planeOne] at h1
    exact hμ0 (by
      have : μ * (μ * 1) = 0 := h1.symm
      rw [mul_one] at this
      exact mul_self_eq_zero.mp this)
  have hconst : ∀ i s, lam i s * lam i s = lam i₀ true * lam i₀ true := by
    intro i s
    have h3 : ((lam i s * μ⁻¹ * (lam i s * μ⁻¹)) -
        (lam i₀ true * μ⁻¹ * (lam i₀ true * μ⁻¹))) • L (L planeOne) = 0 := by
      rw [sub_smul, h.msq i s planeOne, h.msq i₀ true planeOne, sub_self]
    have h4 := (smul_eq_zero.mp h3).resolve_right hLLne
    have h5 : (lam i s * lam i s - lam i₀ true * lam i₀ true) * (μ⁻¹ * μ⁻¹) = 0 := by
      linear_combination h4
    have h6 := (mul_eq_zero.mp h5).resolve_right (mul_ne_zero (inv_ne_zero hμ0) (inv_ne_zero hμ0))
    exact sub_eq_zero.mp h6
  have hν2 : (lam i₀ true * lam i₀ true) * (lam i₀ true * lam i₀ true) = μ * μ := by
    calc _ = (lam i₀ true * lam i₀ true) * (lam i₀ false * lam i₀ false) := by
          rw [hconst i₀ false]
      _ = (lam i₀ true * lam i₀ false) * (lam i₀ true * lam i₀ false) := by ring
      _ = μ * μ := by rw [h.prod i₀]
  have hνμ : lam i₀ true * lam i₀ true = μ := by
    rcases mul_self_eq_mul_self_iff.mp hν2 with h' | h'
    · exact h'
    · exfalso
      have hL2 : ∀ w, L (L w) = (-μ) • w := by
        intro w
        have e : (-μ) * ((lam i₀ true * μ⁻¹) * (lam i₀ true * μ⁻¹)) = 1 := by
          calc _ = (-μ) * ((lam i₀ true * lam i₀ true) * (μ⁻¹ * μ⁻¹)) := by ring
            _ = 1 := by rw [h']; field_simp
        calc L (L w) = ((-μ) * ((lam i₀ true * μ⁻¹) * (lam i₀ true * μ⁻¹))) • L (L w) := by
              rw [e, one_smul]
          _ = (-μ) • (((lam i₀ true * μ⁻¹) * (lam i₀ true * μ⁻¹)) • L (L w)) := mul_smul _ _ _
          _ = (-μ) • w := by rw [h.msq i₀ true w]
      exact no_neg_square hirr h2 L hμ0 h.norm hL2 h'
  have hlamsq : ∀ i s, lam i s * lam i s = μ := fun i s => (hconst i s).trans hνμ
  refine ⟨hlamsq, fun w => ?_⟩
  have h1 := h.msq i₀ true w
  have e : (lam i₀ true * μ⁻¹) * (lam i₀ true * μ⁻¹) = μ⁻¹ := by
    calc _ = (lam i₀ true * lam i₀ true) * (μ⁻¹ * μ⁻¹) := by ring
      _ = μ⁻¹ := by rw [hνμ]; field_simp
  rw [e] at h1
  calc L (L w) = μ • (μ⁻¹ • L (L w)) := by rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    _ = μ • w := by rw [h1]

end SqData

section Diag

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] {b c : F}

theorem minusLift_of_diag (hp2 : p ≠ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (h2 : (2 : F) ≠ 0) {X : Type} [Group X] (θ : spinGroup (quadMinus n F b c) →* X) (σ : X ≃* X)
    {α : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c)}
    {g : SemiSim (quadMinus n F b c)} (hα : IsConj α g) (hαθ : ∀ y, θ (α y) = σ (θ y))
    (hα2 : ∀ y, α (α y) = y) (i₀ : Fin (n - 1)) (κ : spinGroup (quadMinus n F b c))
    (lam : Fin (n - 1) → Bool → F) (hφ : ∀ c', g.φ c' = c')
    (hprod : ∀ i, lam i true * lam i false = g.μ)
    (hg₂ : ∀ i s, g.conjSpin κ (minusVec n i s) = lam i s • minusVec n i s)
    (hCpres : ∀ y : Vm n F, (∀ a r, polar (quadMinus n F b c) y (minusVec n a r) = 0) →
      ∀ a r, polar (quadMinus n F b c) (g.conjSpin κ y) (minusVec n a r) = 0)
    (hdiag : ∀ (i j : Fin (n - 1)) (hij : i ≠ j) (s t : Bool) (c' : F),
      α (κ * (minusFrame n b c).longRoot hij s t (.ofAdd c') * κ⁻¹) =
        κ * (minusFrame n b c).longRoot hij s t
          (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * c')))) * κ⁻¹) :
    MinusLift θ σ := by
  classical
  obtain ⟨L, hLw, hLN⟩ := exists_planeMap (g.conjSpin κ) hφ hCpres
  set A := conjTwist α κ with hAdef
  have hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹ := fun y => by
    rw [hAdef, conjTwist_apply]
    group
  have hα₂c : IsConj A (g.conjSpin κ) := hα.conjSpin κ
  have hact : MinusAct hirr A lam (g.μ : F) L :=
    { ne_zero := g.μ.ne_zero
      involutive := conjTwist_sq α hα2 κ
      prod := hprod
      norm := hLN
      long := fun i j hij s t c' => by
        have h1 := hdiag i j hij s t c'
        rw [hA] at h1
        rw [mul_left_cancel (mul_right_cancel h1)]
        congr 2
        ring
      short := fun i s w => IsConj.twShortRoot_eq hirr hp2 (minus_hker2 hirr) hα₂c lam hg₂ L hLw
        i s w }
  obtain ⟨hlam2, hL2⟩ := minusAct_sq_data h2 hact i₀
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  set ζ := lam i₀ true with hζdef
  have hζ2 : ζ * ζ = (g.μ : F) := hlam2 i₀ true
  have hζ0 : ζ ≠ 0 := fun h0 => hμ0 (by rw [← hζ2, h0, zero_mul])
  have hφ' : ∀ c', (g.conjSpin κ).φ c' = c' := hφ
  let gC : Vm n F →ₗ[F] Vm n F := (g.conjSpin κ).toLinear hφ'
  have hgC : ∀ x, gC x = g.conjSpin κ x := fun x => rfl
  have hsqC : gC ∘ₗ gC = (g.μ : F) • LinearMap.id := by
    refine (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).ext fun c' => ?_
    rcases c' with i | i | t
    · have e : (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (.inl i) = minusVec n i true :=
        by simp [Pi.basisFun_apply, minusVec, eVec]
      rw [e]
      simp only [LinearMap.comp_apply, hgC, hg₂, LinearMap.smul_apply, LinearMap.id_apply]
      change (g.conjSpin κ) (lam i true • minusVec n i true) = _
      rw [(g.conjSpin κ).map_smul, hφ' _, hg₂, smul_smul, hlam2]
    · have e : (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (.inr (.inl i)) =
          minusVec n i false := by simp [Pi.basisFun_apply, minusVec, fVec]
      rw [e]
      simp only [LinearMap.comp_apply, hgC, hg₂, LinearMap.smul_apply, LinearMap.id_apply]
      change (g.conjSpin κ) (lam i false • minusVec n i false) = _
      rw [(g.conjSpin κ).map_smul, hφ' _, hg₂, smul_smul, hlam2]
    · have e : (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (.inr (.inr t)) =
          planeVec n (Pi.single t 1) := by
        funext v
        rcases v with i' | i' | t' <;> simp [Pi.basisFun_apply, planeVec, Pi.single_apply]
      rw [e]
      simp only [LinearMap.comp_apply, hgC, hLw, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hL2, planeVec_smul]
  have hgg : ∀ x, g (g x) = (g.μ : F) • x := by
    intro x
    have h1 := LinearMap.congr_fun hsqC (spinAction (quadMinus n F b c) κ⁻¹ x)
    simp only [LinearMap.comp_apply, hgC, SemiSim.conjSpin_apply, spinAction_apply_inv,
      LinearMap.smul_apply, LinearMap.id_apply] at h1
    have h3 := congrArg (spinAction (quadMinus n F b c) κ) h1
    rw [spinAction_apply_inv, map_smul, spinAction_apply_inv] at h3
    exact h3
  let gF : Vm n F →ₗ[F] Vm n F := g.toLinear hφ
  have hgF : ∀ x, gF x = g x := fun x => rfl
  let g₀L : Vm n F →ₗ[F] Vm n F := ζ⁻¹ • gF
  have hg₀L : ∀ x, g₀L x = ζ⁻¹ • g x := fun x => rfl
  have hinv : Function.Involutive g₀L := fun x => by
    rw [hg₀L, hg₀L, g.map_smul, hφ, smul_smul, hgg, smul_smul]
    have : ζ⁻¹ * ζ⁻¹ * (g.μ : F) = 1 := by
      rw [← hζ2]
      field_simp
    rw [this, one_smul]
  let g₀ : Vm n F ≃ₗ[F] Vm n F := LinearEquiv.ofInvolutive g₀L hinv
  have hg₀ : ∀ x, g₀ x = ζ⁻¹ • g x := fun x => rfl
  refine ⟨α, g₀, hαθ, ?_, ?_, ?_⟩
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    have h1 := g.map_Q x
    rw [hg₀, QuadraticMap.map_smul, h1, hφ]
    have : ζ⁻¹ * ζ⁻¹ * (g.μ : F) = 1 := by
      rw [← hζ2]
      field_simp
    rw [smul_eq_mul, ← mul_assoc, this, one_mul]
  · refine LinearEquiv.ext fun x => ?_
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
    exact hinv x
  · intro y z
    rw [hg₀, hg₀, map_smul, hα y z]

end Diag

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {b c : F}

theorem minusLift_of_normalized (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 6 ≤ n) {X : Type} [Group X]
    (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin (n - 1)} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) (s₀ t₀ s₁ t₁ : Bool) (k : spinGroup (quadMinus n F b c))
    (H1 : ∀ c' : F, σ (θ (k * (minusFrame n b c).longRoot h01 s₀ t₀ (.ofAdd c') * k⁻¹)) =
      θ (k * (minusFrame n b c).longRoot h01 s₀ t₀ (.ofAdd c') * k⁻¹))
    (H1' : ∀ c' : F, σ (θ (k * (minusFrame n b c).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c') *
        k⁻¹)) = θ (k * (minusFrame n b c).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c') * k⁻¹))
    (H2 : ∀ (a a' : Fin (n - 1)) (haa : a ≠ a'), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → a' ≠ i₀ → a' ≠ i₁ →
      a' ≠ c₀ → ∀ (s t : Bool) (c' : F),
        σ (θ (k * (minusFrame n b c).longRoot haa s t (.ofAdd c') * k⁻¹)) =
          θ (k * (minusFrame n b c).longRoot haa s t (.ofAdd c') * k⁻¹))
    (H3 : ∀ c' : F, ∃ c'' : F,
      σ (θ (k * (minusFrame n b c).longRoot hjc s₁ t₁ (.ofAdd c') * k⁻¹)) =
        θ (k * (minusFrame n b c).longRoot hjc s₁ t₁ (.ofAdd c'') * k⁻¹)) :
    MinusLift θ σ := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have hn4 : 4 ≤ n := by omega
  have hm5 : 5 ≤ n - 1 := by omega
  obtain ⟨hZ, -⟩ := minus_center_facts hirr hp2 hn4
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_minus hp2 hn4 hf hF hirr θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadMinus n F b c)) := isPerfect_spinGroup_quadMinus hn4 hirr
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadMinus n F b c) →* _).comp
      (α : spinGroup (quadMinus n F b c) →* _)) (MonoidHom.id (spinGroup (quadMinus n F b c)))
      (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  set Fr := minusFrame n b c with hFr
  have hfix : ∀ {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (c' : F),
      σ (θ (k * Fr.longRoot hij s t (.ofAdd c') * k⁻¹)) =
        θ (k * Fr.longRoot hij s t (.ofAdd c') * k⁻¹) →
      conjTwist α k (Fr.longRoot hij s t (.ofAdd c')) = Fr.longRoot hij s t (.ofAdd c') :=
    fun hij s t c' h => conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k
      (longRoot_pow_char Fr.toHypFrame hij s t c') (longRoot_pow_char Fr.toHypFrame hij s t c') h
  have hA1 : ∀ c' : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c')) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c') := fun c' => hfix h01 s₀ t₀ c' (H1 c')
  have hA1' : ∀ c' : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c')) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c') :=
    fun c' => hfix h01.symm (!t₀) (!s₀) c' (H1' c')
  obtain ⟨c₁, hc₁⟩ := H3 1
  have hN : conjTwist α k (Fr.longRoot hjc s₁ t₁ (.ofAdd 1)) =
      Fr.longRoot hjc s₁ t₁ (.ofAdd c₁) :=
    conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k (longRoot_pow_char Fr.toHypFrame hjc s₁ t₁ 1)
      (longRoot_pow_char Fr.toHypFrame hjc s₁ t₁ c₁) hc₁
  have hO : ∀ (a a' : Fin (n - 1)) (haa : a ≠ a'), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → a' ≠ i₀ →
      a' ≠ i₁ → a' ≠ c₀ → ∀ (s t : Bool) (c' : F),
        conjTwist α k (Fr.longRoot haa s t (.ofAdd c')) = Fr.longRoot haa s t (.ofAdd c') :=
    fun a a' haa ha0 ha1 hac ha0' ha1' hac' s t c' =>
      hfix haa s t c' (H2 a a' haa ha0 ha1 hac ha0' ha1' hac' s t c')
  have hC : ∀ x : Vm n F, (∀ a r, polar (quadMinus n F b c) x (Fr.vec a r) = 0) →
      x ∈ planeSub n F := fun x hx => ⟨_, eq_planeVec_of_polar_minusVec n b c hx⟩
  have hCorth : ∀ x ∈ planeSub n F, ∀ a r, polar (quadMinus n F b c) x (Fr.vec a r) = 0 := by
    rintro x ⟨w, rfl⟩ a r
    exact polar_planeVec_minusVec n b c w a r
  have hY : ∀ e ∈ planeSub n F, ∃ y : spinGroup (quadMinus n F b c),
      spinAction (quadMinus n F b c) y = eichler (quadMinus n F b c) (Fr.vec c₀ s₁) e ∧
      ∀ (i j : Fin (n - 1)) (hij : i ≠ j), i ≠ c₀ → j ≠ c₀ → ∀ (t t' : Bool) (c' : F),
        Commute y (Fr.longRoot hij t t' (.ofAdd c')) := by
    rintro e ⟨w, rfl⟩
    exact ⟨twShortRoot n hirr c₀ s₁ (.ofAdd w), spinAction_twShortRoot_eq_eichler hirr c₀ s₁ w,
      fun i j hij hi hj t t' c' =>
        (commute_longRoot_twShortRoot_of_ne n hirr hij hi.symm hj.symm t t' s₁ c' w).symm⟩
  obtain ⟨k', hk1, hk1', hmul⟩ := exists_adjusted_frame Fr.toHypFrame h01 s₀ t₀ h2 hm5
    (planeSub n F) hC hCorth hα hα2 k hA1 hA1' hc0 hc1 hj0 hj1 hjc s₁ t₁ hO hN hY
  obtain ⟨κ, lam, hφ, hprod, hg₂, hCpres, hdiag, -⟩ := exists_diag_form_of_diag_compl
    Fr.toHypFrame h01 s₀ t₀ (by omega) h2 hp2 (minus_hker2 hirr) hα hα2 k' hk1 hk1' hmul
  exact minusLift_of_diag hp2 hirr h2 θ σ hα hαθ hα2 i₀ κ lam hφ hprod hg₂ hCpres hdiag

theorem minusLift_of_normalized_subgroups (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 6 ≤ n)
    {X : Type} [Group X] (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin (n - 1)} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) {s₀ t₀ s₁ t₁ : Bool} {γ₀ γ₁ : Fin (n - 1) → ℤ}
    (hγ₀ : toStdB (n - 1) γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (hγ₁ : toStdB (n - 1) γ₁ = Pi.single c₀ (boolSign s₁) + Pi.single j (boolSign t₁))
    (k : spinGroup (quadMinus n F b c))
    (H1 : ∀ y ∈ (((minusDatum n hirr).rootGroup γ₀ ⊔ (minusDatum n hirr).rootGroup (-γ₀)).map
        (MulAut.conj k).toMonoidHom), σ (θ y) = θ y)
    (H2 : ∀ (a a' : Fin (n - 1)), a ≠ a' → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → a' ≠ i₀ → a' ≠ i₁ →
      a' ≠ c₀ → ∀ (s t : Bool) {γ : Fin (n - 1) → ℤ},
        toStdB (n - 1) γ = Pi.single a (boolSign s) + Pi.single a' (boolSign t) →
          ∀ y ∈ ((minusDatum n hirr).rootGroup γ).map (MulAut.conj k).toMonoidHom,
            σ (θ y) = θ y)
    (H3 : ∀ y ∈ ((minusDatum n hirr).rootGroup γ₁).map (MulAut.conj k).toMonoidHom,
      σ (θ y) ∈ (((minusDatum n hirr).rootGroup γ₁).map (MulAut.conj k).toMonoidHom).map θ) :
    MinusLift θ σ := by
  classical
  have hX1 : (minusDatum n hirr).rootGroup γ₀ = ((minusFrame n b c).longRoot h01 s₀ t₀).range :=
    minusRootGroup_eq_long n hirr h01 s₀ t₀ hγ₀
  have hstd' : toStdB (n - 1) (-γ₀) =
      Pi.single i₁ (boolSign (!t₀)) + Pi.single i₀ (boolSign (!s₀)) := by
    have e : toStdB (n - 1) (-γ₀) = -toStdB (n - 1) γ₀ := toStdB_neg (n - 1) γ₀
    rw [e, hγ₀, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add, add_comm]
  have hX2 : (minusDatum n hirr).rootGroup (-γ₀) =
      ((minusFrame n b c).longRoot h01.symm (!t₀) (!s₀)).range :=
    minusRootGroup_eq_long n hirr h01.symm (!t₀) (!s₀) hstd'
  have hX3 : (minusDatum n hirr).rootGroup γ₁ = ((minusFrame n b c).longRoot hjc s₁ t₁).range :=
    minusRootGroup_eq_long n hirr hjc s₁ t₁ hγ₁
  refine minusLift_of_normalized hp2 hf hF hirr hn θ hker σ hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc
    s₀ t₀ s₁ t₁ k (fun c' => ?_) (fun c' => ?_)
    (fun a a' haa ha0 ha1 hac ha0' ha1' hac' s t c' => ?_) (fun c' => ?_)
  · refine H1 _ ⟨_, Subgroup.mem_sup_left ?_, rfl⟩
    rw [hX1]
    exact ⟨_, rfl⟩
  · refine H1 _ ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
    rw [hX2]
    exact ⟨_, rfl⟩
  · have hγ : toStdB (n - 1) (ofStdB (n - 1) (Pi.single a (boolSign s) +
        Pi.single a' (boolSign t))) = Pi.single a (boolSign s) + Pi.single a' (boolSign t) :=
      toStdB_ofStdB (n - 1) _
    have hXγ : (minusDatum n hirr).rootGroup (ofStdB (n - 1) (Pi.single a (boolSign s) +
        Pi.single a' (boolSign t))) = ((minusFrame n b c).longRoot haa s t).range :=
      minusRootGroup_eq_long n hirr haa s t hγ
    refine H2 a a' haa ha0 ha1 hac ha0' ha1' hac' s t hγ _ ⟨_, ?_, rfl⟩
    rw [hXγ]
    exact ⟨_, rfl⟩
  · have h1 := H3 (k * (minusFrame n b c).longRoot hjc s₁ t₁ (.ofAdd c') * k⁻¹) ⟨_, ?_, rfl⟩
    · obtain ⟨y', ⟨y, hy, rfl⟩, hy'⟩ := h1
      rw [hX3] at hy
      obtain ⟨c'', rfl⟩ := hy
      refine ⟨Multiplicative.toAdd c'', ?_⟩
      rw [← hy', ofAdd_toAdd]
      rfl
    · rw [hX3]
      exact ⟨_, rfl⟩

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
