module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutNormalCompl
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutOdd

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

section Tail

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem toralNormal_odd_of_diag (hp2 : p ≠ 2) {m : ℕ} (h2 : (2 : F) ≠ 0)
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup (quadOdd m F)), ζ ^ p = 1 → ζ = 1)
    {X : Type} [Group X] (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F))) (σ : X ≃* X)
    {α : spinGroup (quadOdd m F) ≃* spinGroup (quadOdd m F)} {g : SemiSim (quadOdd m F)}
    (hα : IsConj α g) (hαθ : ∀ y, θ (α y) = σ (θ y)) (hα2 : ∀ y, α (α y) = y)
    (κ : spinGroup (quadOdd m F)) (lam : Fin m → Bool → F) (hφ : ∀ c, g.φ c = c)
    (hprod : ∀ i, lam i true * lam i false = g.μ)
    (hg₂ : ∀ i s, g.conjSpin κ ((oddFrame m F).vec i s) = lam i s • (oddFrame m F).vec i s)
    (hCpres : ∀ y : Fin m ⊕ Fin m ⊕ Unit → F,
      (∀ a r, polar (quadOdd m F) y ((oddFrame m F).vec a r) = 0) →
        ∀ a r, polar (quadOdd m F) (g.conjSpin κ y) ((oddFrame m F).vec a r) = 0)
    (hdiag : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
      α (κ * (oddFrame m F).longRoot hij s t (.ofAdd c) * κ⁻¹) =
        κ * (oddFrame m F).longRoot hij s t
          (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * c)))) * κ⁻¹) :
    ∃ (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (oddDatum m F).roots →
        ((((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  set Fr := oddFrame m F with hFr
  have hzorth : ∀ a r, polar (quadOdd m F) Fr.z (Fr.vec a r) = 0 := fun a r => by
    rw [polar_comm]
    exact Fr.polar_vec_z a r
  obtain ⟨ζ, hζ⟩ := odd_orth_eq_smul_z m (fun a r => hCpres Fr.z hzorth a r)
  have hζ2 : ζ * ζ = (g.μ : F) := by
    have h1 := (g.conjSpin κ).map_Q Fr.z
    rw [hζ, QuadraticMap.map_smul, Fr.map_z] at h1
    change (ζ * ζ) • (1 : F) = (g.μ : F) * g.φ 1 at h1
    simpa using h1
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hζ0 : ζ ≠ 0 := fun h0 => hμ0 (by rw [← hζ2, h0, zero_mul])
  have hlam2 : ∀ k s, lam k (!s) * lam k s = (g.μ : F) := by
    intro k s
    cases s
    · simpa using hprod k
    · simpa [mul_comm] using hprod k
  have hlam0 : ∀ k s, lam k s ≠ 0 := fun k s h0 => hμ0 (by rw [← hlam2 k s, h0, mul_zero])
  let a : Fin m → Fˣ := fun k => Units.mk0 (lam k true / ζ) (div_ne_zero (hlam0 k true) hζ0)
  have hlamζ : ∀ k s, lam k s = ζ * (a k : F) ^ boolSign s := by
    intro k s
    have h0 := hlam0 k true
    cases s
    · simp only [boolSign_false, a, Units.val_mk0, zpow_neg, zpow_one]
      have hp := hprod k
      rw [← hζ2] at hp
      field_simp
      linear_combination hp
    · simp only [boolSign_true, a, Units.val_mk0, zpow_one]
      field_simp
  set A := conjTwist α κ with hAdef
  have hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹ := fun y => by
    rw [hAdef, conjTwist_apply]
    group
  have hA2 : ∀ y, A (A y) = y := conjTwist_sq α hα2 κ
  have hAlong : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
      A (Fr.longRoot hij s t (.ofAdd c)) =
        Fr.longRoot hij s t (.ofAdd ((lam j t * ((g.μ : F)⁻¹ * lam i s)) * c)) := by
    intro i j hij s t c
    have h1 := hdiag i j hij s t c
    rw [hA] at h1
    rw [mul_left_cancel (mul_right_cancel h1)]
    congr 2
    ring
  have hα₂c : IsConj A (g.conjSpin κ) := hα.conjSpin κ
  have hAshort : ∀ (i : Fin m) (s : Bool) (c : F),
      A (Fr.shortRoot i s (.ofAdd c)) =
        Fr.shortRoot i s (.ofAdd ((lam i s * ((g.μ : F)⁻¹ * ζ)) * c)) := by
    intro i s c
    have h3 := IsConj.shortRoot_eq hp2 (odd_hker2 h2 m) Fr hα₂c lam (fun _ s => s) hg₂ ζ hζ i s c
    have hφc : (g.conjSpin κ).φ c = c := hφ c
    have hμc : (((g.conjSpin κ).μ : Fˣ) : F) = (g.μ : F) := rfl
    rw [h3, hφc, hμc]
    congr 2
    ring
  have hχL2 : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool),
      (lam j t * ((g.μ : F)⁻¹ * lam i s)) * (lam j t * ((g.μ : F)⁻¹ * lam i s)) = 1 :=
    fun i j hij s t => sq_eq_one_of_scalar A hA2 (Fr.longRoot hij s t)
      (Fr.longRoot_injective hij s t) _ (hAlong i j hij s t)
  have hχS2 : ∀ (i : Fin m) (s : Bool),
      (lam i s * ((g.μ : F)⁻¹ * ζ)) * (lam i s * ((g.μ : F)⁻¹ * ζ)) = 1 :=
    fun i s => sq_eq_one_of_scalar A hA2 (Fr.shortRoot i s) (Fr.shortRoot_injective i s) _
      (hAshort i s)
  have hψlong : ∀ (γ : Fin m → ℤ) (i j : Fin m) (s t : Bool),
      toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam j t * ((g.μ : F)⁻¹ * lam i s) := by
    intro γ i j s t h
    rw [charPsiB_long a s t h, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val, hlamζ i s, hlamζ j t, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    have haj : (a j : F) ≠ 0 := (a j).ne_zero
    field_simp
  have hψshort : ∀ (γ : Fin m → ℤ) (i : Fin m) (s : Bool),
      toStdB m γ = Pi.single i (boolSign s) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam i s * ((g.μ : F)⁻¹ * ζ) := by
    intro γ i s h
    rw [charPsiB_short a s h, Units.val_zpow_eq_zpow_val, hlamζ i s, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    field_simp
  have hψ1 : ∀ a₀ : Fin m, charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = 1 ∨
      charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = -1 := by
    intro a₀
    by_cases hlt : a₀.val + 1 < m
    · have hkj : a₀ ≠ ⟨a₀.val + 1, hlt⟩ := Fin.ne_of_val_ne (by simp)
      have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) +
          Pi.single (⟨a₀.val + 1, hlt⟩ : Fin m) (boolSign false) := by
        rw [toStdB_single_of_lt m hlt, boolSign_true, boolSign_false, Pi.single_neg,
          sub_eq_add_neg]
      have h1 := hψlong _ _ _ true false hrep
      have h2' := hχL2 _ _ hkj true false
      rw [← h1] at h2'
      rcases mul_self_eq_one_iff.mp h2' with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
    · have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) := by
        rw [toStdB_single_of_not_lt m hlt, boolSign_true]
      have h1 := hψshort _ _ true hrep
      have h2' := hχS2 a₀ true
      rw [← h1] at h2'
      rcases mul_self_eq_one_iff.mp h2' with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
  obtain ⟨v, hv⟩ := exists_vec_of_hom h2 (charPsiB a) hψ1
  refine ⟨κ, v, fun γ hγ => ?_⟩
  rcases odd_root_cases hγ with ⟨i, j, hij, s, t, hstd⟩ | ⟨i, s, hstd⟩
  · have hX1 : (oddDatum m F).rootGroup γ = (Fr.longRoot hij s t).range :=
      oddRootGroup_eq_long hij s t hstd
    have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) + Pi.single j (boolSign (!t)) := by
      have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
      rw [e, hstd, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add]
    have hX2 : (oddDatum m F).rootGroup (-γ) = (Fr.longRoot hij (!s) (!t)).range :=
      oddRootGroup_eq_long hij (!s) (!t) hstd'
    rw [hX1, hX2]
    have hχ : lam j t * ((g.μ : F)⁻¹ * lam i s) = 1 →
        lam j (!t) * ((g.μ : F)⁻¹ * lam i (!s)) = 1 := by
      intro h1
      have hprod' : (lam j (!t) * ((g.μ : F)⁻¹ * lam i (!s))) *
          (lam j t * ((g.μ : F)⁻¹ * lam i s)) = 1 := by
        calc _ = (lam j (!t) * lam j t) * (lam i (!s) * lam i s) *
              ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by ring
          _ = (g.μ : F) * (g.μ : F) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by rw [hlam2, hlam2]
          _ = 1 := by field_simp
      rw [h1, mul_one] at hprod'
      exact hprod'
    have hmain := normalizes_and_fixes_of_scalar hZ θ hker σ α A κ hαθ hA hA2
      (Fr.longRoot hij s t) (Fr.longRoot hij (!s) (!t)) (Fr.longRoot_injective hij s t)
      (fun c => longRoot_pow_char Fr.toHypFrame hij s t c) _ _ (hAlong i j hij s t)
      (hAlong i j hij (!s) (!t)) hχ
    refine ⟨hmain.1, ?_⟩
    rw [hmain.2, ← hv γ, Units.ext_iff, hψlong γ i j s t hstd, Units.val_one]
  · have hX1 : (oddDatum m F).rootGroup γ = (Fr.shortRoot i s).range :=
      oddRootGroup_eq_short i s hstd
    have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) := by
      have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
      rw [e, hstd, boolSign_not, Pi.single_neg]
    have hX2 : (oddDatum m F).rootGroup (-γ) = (Fr.shortRoot i (!s)).range :=
      oddRootGroup_eq_short i (!s) hstd'
    rw [hX1, hX2]
    have hχ : lam i s * ((g.μ : F)⁻¹ * ζ) = 1 → lam i (!s) * ((g.μ : F)⁻¹ * ζ) = 1 := by
      intro h1
      have hprod' : (lam i (!s) * ((g.μ : F)⁻¹ * ζ)) * (lam i s * ((g.μ : F)⁻¹ * ζ)) = 1 := by
        calc _ = (lam i (!s) * lam i s) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) * (ζ * ζ) := by ring
          _ = (g.μ : F) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) * (g.μ : F) := by rw [hlam2, hζ2]
          _ = 1 := by field_simp
      rw [h1, mul_one] at hprod'
      exact hprod'
    have hmain := normalizes_and_fixes_of_scalar hZ θ hker σ α A κ hαθ hA hA2
      (Fr.shortRoot i s) (Fr.shortRoot i (!s)) (Fr.shortRoot_injective i s)
      (fun c => shortRoot_pow_char Fr i s c) _ _ (hAshort i s) (hAshort i (!s)) hχ
    refine ⟨hmain.1, ?_⟩
    rw [hmain.2, ← hv γ, Units.ext_iff, hψshort γ i s hstd, Units.val_one]

end Tail

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem toralNormal_odd_of_normalized (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {m : ℕ} (hm : 5 ≤ m) {X : Type} [Group X] (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin m} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) (s₀ t₀ s₁ t₁ : Bool) (k : spinGroup (quadOdd m F))
    (H1 : ∀ c : F, σ (θ (k * (oddFrame m F).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹)) =
      θ (k * (oddFrame m F).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹))
    (H1' : ∀ c : F, σ (θ (k * (oddFrame m F).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) *
        k⁻¹)) = θ (k * (oddFrame m F).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹))
    (H2 : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) (c : F),
        σ (θ (k * (oddFrame m F).longRoot hab s t (.ofAdd c) * k⁻¹)) =
          θ (k * (oddFrame m F).longRoot hab s t (.ofAdd c) * k⁻¹))
    (H3 : ∀ c : F, ∃ c' : F,
      σ (θ (k * (oddFrame m F).longRoot hjc s₁ t₁ (.ofAdd c) * k⁻¹)) =
        θ (k * (oddFrame m F).longRoot hjc s₁ t₁ (.ofAdd c') * k⁻¹)) :
    ∃ (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (oddDatum m F).roots →
        ((((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have hm3 : 3 ≤ m := by omega
  obtain ⟨hZ, -⟩ := odd_center_facts (F := F) hp2 hm3
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_odd hp2 hm3 hf hF θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadOdd m F)) := isPerfect_spinGroup_quadOdd h2 hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadOdd m F) →* _).comp
      (α : spinGroup (quadOdd m F) →* _)) (MonoidHom.id (spinGroup (quadOdd m F))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  set Fr := oddFrame m F with hFr
  have hfix : ∀ {i j : Fin m} (hij : i ≠ j) (s t : Bool) (c : F),
      σ (θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹)) =
        θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹) →
      conjTwist α k (Fr.longRoot hij s t (.ofAdd c)) = Fr.longRoot hij s t (.ofAdd c) :=
    fun hij s t c h => conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k
      (longRoot_pow_char Fr.toHypFrame hij s t c) (longRoot_pow_char Fr.toHypFrame hij s t c) h
  have hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c) := fun c => hfix h01 s₀ t₀ c (H1 c)
  have hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) := fun c => hfix h01.symm (!t₀) (!s₀) c (H1' c)
  obtain ⟨c', hc'⟩ := H3 1
  have hN : conjTwist α k (Fr.longRoot hjc s₁ t₁ (.ofAdd 1)) =
      Fr.longRoot hjc s₁ t₁ (.ofAdd c') :=
    conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k (longRoot_pow_char Fr.toHypFrame hjc s₁ t₁ 1)
      (longRoot_pow_char Fr.toHypFrame hjc s₁ t₁ c') hc'
  have hO : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ →
      b ≠ c₀ → ∀ (s t : Bool) (c : F), conjTwist α k (Fr.longRoot hab s t (.ofAdd c)) =
        Fr.longRoot hab s t (.ofAdd c) :=
    fun a b hab ha0 ha1 hac hb0 hb1 hbc s t c =>
      hfix hab s t c (H2 a b hab ha0 ha1 hac hb0 hb1 hbc s t c)
  let C : Submodule F (Fin m ⊕ Fin m ⊕ Unit → F) := Submodule.span F {Fr.z}
  have hC : ∀ x : Fin m ⊕ Fin m ⊕ Unit → F,
      (∀ a r, polar (quadOdd m F) x (Fr.vec a r) = 0) → x ∈ C := fun x hx => by
    obtain ⟨c, hc⟩ := odd_orth_eq_smul_z m hx
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hCorth : ∀ x ∈ C, ∀ a r, polar (quadOdd m F) x (Fr.vec a r) = 0 := fun x hx a r => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [polar_smul_left, polar_comm, Fr.polar_vec_z a r, smul_zero]
  have hY : ∀ e ∈ C, ∃ y : spinGroup (quadOdd m F),
      spinAction (quadOdd m F) y = eichler (quadOdd m F) (Fr.vec c₀ s₁) e ∧
      ∀ (i j : Fin m) (hij : i ≠ j), i ≠ c₀ → j ≠ c₀ → ∀ (t t' : Bool) (c : F),
        Commute y (Fr.longRoot hij t t' (.ofAdd c)) := by
    intro e he
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp he
    exact ⟨Fr.shortRoot c₀ s₁ (.ofAdd c), Fr.spinAction_shortRoot_eq_eichler c₀ s₁ c,
      fun i j hij hi hj t t' c₁ =>
        (Fr.commute_longRoot_shortRoot_of_ne hij hi.symm hj.symm t t' s₁ c₁ c).symm⟩
  obtain ⟨k', hk1, hk1', hmul⟩ := exists_adjusted_frame Fr.toHypFrame h01 s₀ t₀ h2 hm C hC hCorth
    hα hα2 k hA1 hA1' hc0 hc1 hj0 hj1 hjc s₁ t₁ hO hN hY
  obtain ⟨κ, lam, hφ, hprod, hg₂, hCpres, hdiag, -⟩ := exists_diag_form_of_diag_compl
    Fr.toHypFrame h01 s₀ t₀ hm3 h2 hp2 (odd_hker2 h2 m) hα hα2 k' hk1 hk1' hmul
  exact toralNormal_odd_of_diag hp2 h2 hZ θ hker σ hα hαθ hα2 κ lam hφ hprod hg₂ hCpres hdiag

theorem toralNormal_odd_of_normalized_subgroups (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {m : ℕ} (hm : 5 ≤ m) {X : Type} [Group X]
    (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin m} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) {s₀ t₀ s₁ t₁ : Bool} {γ₀ γ₁ : Fin m → ℤ}
    (hγ₀ : toStdB m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (hγ₁ : toStdB m γ₁ = Pi.single c₀ (boolSign s₁) + Pi.single j (boolSign t₁))
    (k : spinGroup (quadOdd m F))
    (H1 : ∀ y ∈ (((oddDatum m F).rootGroup γ₀ ⊔ (oddDatum m F).rootGroup (-γ₀)).map
        (MulAut.conj k).toMonoidHom), σ (θ y) = θ y)
    (H2 : ∀ (a b : Fin m), a ≠ b → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) {γ : Fin m → ℤ},
        toStdB m γ = Pi.single a (boolSign s) + Pi.single b (boolSign t) →
          ∀ y ∈ ((oddDatum m F).rootGroup γ).map (MulAut.conj k).toMonoidHom, σ (θ y) = θ y)
    (H3 : ∀ y ∈ ((oddDatum m F).rootGroup γ₁).map (MulAut.conj k).toMonoidHom,
      σ (θ y) ∈ (((oddDatum m F).rootGroup γ₁).map (MulAut.conj k).toMonoidHom).map θ) :
    ∃ (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (oddDatum m F).roots →
        ((((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have hX1 : (oddDatum m F).rootGroup γ₀ = ((oddFrame m F).longRoot h01 s₀ t₀).range :=
    oddRootGroup_eq_long h01 s₀ t₀ hγ₀
  have hstd' : toStdB m (-γ₀) = Pi.single i₁ (boolSign (!t₀)) + Pi.single i₀ (boolSign (!s₀)) := by
    have e : toStdB m (-γ₀) = -toStdB m γ₀ := toStdB_neg m γ₀
    rw [e, hγ₀, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add, add_comm]
  have hX2 : (oddDatum m F).rootGroup (-γ₀) =
      ((oddFrame m F).longRoot h01.symm (!t₀) (!s₀)).range :=
    oddRootGroup_eq_long h01.symm (!t₀) (!s₀) hstd'
  have hX3 : (oddDatum m F).rootGroup γ₁ = ((oddFrame m F).longRoot hjc s₁ t₁).range :=
    oddRootGroup_eq_long hjc s₁ t₁ hγ₁
  refine toralNormal_odd_of_normalized hp2 hf hF hm θ hker σ hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc
    s₀ t₀ s₁ t₁ k (fun c => ?_) (fun c => ?_)
    (fun a b hab ha0 ha1 hac hb0 hb1 hbc s t c => ?_) (fun c => ?_)
  · refine H1 _ ⟨_, Subgroup.mem_sup_left ?_, rfl⟩
    rw [hX1]
    exact ⟨_, rfl⟩
  · refine H1 _ ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
    rw [hX2]
    exact ⟨_, rfl⟩
  · have hγ : toStdB m (ofStdB m (Pi.single a (boolSign s) + Pi.single b (boolSign t))) =
        Pi.single a (boolSign s) + Pi.single b (boolSign t) := toStdB_ofStdB m _
    have hXγ : (oddDatum m F).rootGroup
        (ofStdB m (Pi.single a (boolSign s) + Pi.single b (boolSign t))) =
        ((oddFrame m F).longRoot hab s t).range := oddRootGroup_eq_long hab s t hγ
    refine H2 a b hab ha0 ha1 hac hb0 hb1 hbc s t hγ _ ⟨_, ?_, rfl⟩
    rw [hXγ]
    exact ⟨_, rfl⟩
  · have h1 := H3 (k * (oddFrame m F).longRoot hjc s₁ t₁ (.ofAdd c) * k⁻¹) ⟨_, ?_, rfl⟩
    · obtain ⟨y', ⟨y, hy, rfl⟩, hy'⟩ := h1
      rw [hX3] at hy
      obtain ⟨c', rfl⟩ := hy
      refine ⟨Multiplicative.toAdd c', ?_⟩
      rw [← hy', ofAdd_toAdd]
      rfl
    · rw [hX3]
      exact ⟨_, rfl⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
