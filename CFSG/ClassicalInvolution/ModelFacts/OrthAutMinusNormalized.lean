module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutNormalCompl
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinus

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

@[expose] def planeSub (n : ℕ) (F : Type) [Field F] : Submodule F (Vm n F) where
  carrier := {x | ∃ w : Fin 2 → F, x = planeVec n w}
  zero_mem' := ⟨0, (planeVec_zero n).symm⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', (planeVec_add n w w').symm⟩
  smul_mem' := by
    rintro r _ ⟨w, rfl⟩
    exact ⟨r • w, (planeVec_smul n r w).symm⟩

theorem mem_planeSub {n : ℕ} {F : Type} [Field F] {x : Vm n F} :
    x ∈ planeSub n F ↔ ∃ w : Fin 2 → F, x = planeVec n w := Iff.rfl

section Tail

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] {b c : F}

theorem toralNormal_minus_of_diag (hp2 : p ≠ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (h2 : (2 : F) ≠ 0)
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup (quadMinus n F b c)), ζ ^ p = 1 → ζ = 1)
    {X : Type} [Group X] (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c))) (σ : X ≃* X)
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
    (∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0)) ∨
    (∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          (∑ i, (γ i : ZMod 2) * v i = 0 ∧
            ¬ ∃ (i : Fin (n - 1)) (s : Bool),
              toStdB (n - 1) γ = Pi.single i (boolSign s)))) := by
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
  by_cases hS : ∃ ρ : F, ∀ w, L w = ρ • w
  · obtain ⟨ρ, hρ⟩ := hS
    obtain ⟨v, hv⟩ := minus_scalar h2 hZ θ hker σ α A κ hαθ hA hact ρ hρ
    exact Or.inl ⟨κ, v, fun γ hγ => hv γ hγ⟩
  · obtain ⟨v, hv⟩ := minus_nonscalar h2 hZ θ hker σ α A κ hαθ hA hact i₀ hS
    exact Or.inr ⟨κ, v, fun γ hγ => hv γ hγ⟩

end Tail

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {b c : F}

theorem toralNormal_minus_of_normalized (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
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
    (∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0)) ∨
    (∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          (∑ i, (γ i : ZMod 2) * v i = 0 ∧
            ¬ ∃ (i : Fin (n - 1)) (s : Bool),
              toStdB (n - 1) γ = Pi.single i (boolSign s)))) := by
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
  exact toralNormal_minus_of_diag hp2 hirr h2 hZ θ hker σ hα hαθ hα2 i₀ κ lam hφ hprod hg₂ hCpres
    hdiag

theorem toralNormal_minus_of_normalized_subgroups (hp2 : p ≠ 2) (hf : 1 ≤ f)
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
    (∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0)) ∨
    (∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          (∑ i, (γ i : ZMod 2) * v i = 0 ∧
            ¬ ∃ (i : Fin (n - 1)) (s : Bool),
              toStdB (n - 1) γ = Pi.single i (boolSign s)))) := by
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
  refine toralNormal_minus_of_normalized hp2 hf hF hirr hn θ hker σ hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc
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

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
