module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutNormal
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

section Tail

variable {F : Type} [Field F] {p : ℕ} [CharP F p] {m : ℕ}

theorem toralNormal_plus_of_diag (hm3 : 3 ≤ m) (h2 : (2 : F) ≠ 0)
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup (quadPlus m F)), ζ ^ p = 1 → ζ = 1)
    {X : Type} [Group X] (θ : spinGroup (quadPlus m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m F))) (σ : X ≃* X)
    (α : spinGroup (quadPlus m F) ≃* spinGroup (quadPlus m F))
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (hα2 : ∀ y, α (α y) = y) (μ : Fˣ)
    (κ : spinGroup (quadPlus m F)) (lam : Fin m → Bool → F)
    (hprod : ∀ i, lam i true * lam i false = μ)
    (hdiag : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
      α (κ * (plusFrame m F hm3).longRoot hij s t (.ofAdd c) * κ⁻¹) =
        κ * (plusFrame m F hm3).longRoot hij s t
          (.ofAdd (lam j t * ((μ : F)⁻¹ * (lam i s * c)))) * κ⁻¹) :
    ∃ (k₀ : spinGroup (quadPlus m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m F hm3).roots →
        ((((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  set A := conjTwist α κ with hAdef
  have hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹ := fun y => by
    rw [hAdef, conjTwist_apply]
    group
  have hA2 : ∀ y, A (A y) = y := conjTwist_sq α hα2 κ
  set Fr := plusFrame m F hm3 with hFr
  set χ : Fin m → Bool → Fin m → Bool → F := fun i s j t =>
    lam j t * ((μ : F)⁻¹ * lam i s) with hχ
  have hAroot : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
      A (Fr.longRoot hij s t (.ofAdd c)) = Fr.longRoot hij s t (.ofAdd (χ i s j t * c)) := by
    intro i j hij s t c
    have h1 := hdiag i j hij s t c
    rw [hA] at h1
    rw [mul_left_cancel (mul_right_cancel h1)]
    congr 2
    simp only [hχ]
    ring
  have hχ2 : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool), χ i s j t * χ i s j t = 1 := by
    intro i j hij s t
    have h1 := hA2 (Fr.longRoot hij s t (.ofAdd 1))
    rw [hAroot, hAroot] at h1
    have h3 := Multiplicative.ofAdd.injective (Fr.longRoot_injective hij s t h1)
    simpa [mul_one] using h3
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  have hlam2 : ∀ k s, lam k (!s) * lam k s = (μ : F) := by
    intro k s
    cases s
    · simpa using hprod k
    · simpa [mul_comm] using hprod k
  have hlam0 : ∀ k s, lam k s ≠ 0 := fun k s h0 => hμ0 (by rw [← hlam2 k s, h0, mul_zero])
  let a : Fin m → Fˣ := fun k => Units.mk0 (lam k true) (hlam0 k true)
  have hlamOf : ∀ k s, lamOf a μ k s = lam k s := by
    intro k s
    cases s
    · have h0 := hlam0 k true
      simp only [lamOf, a, Bool.false_eq_true, ite_false, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [← hprod k]
      field_simp
    · simp [lamOf, a]
  have hm2 : 2 ≤ m := by omega
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin m, ℓ.val + 1 = m := ⟨⟨m - 1, by omega⟩, by simp only; omega⟩
  set ψ := charPsi a μ ℓ with hψdef
  have hψχ : ∀ (γ : Fin m → ℤ) (i j : Fin m) (s t : Bool),
      toStdD m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) →
        ((ψ (Multiplicative.ofAdd γ) : Fˣ) : F) = χ i s j t := by
    intro γ i j s t h
    rw [hψdef, charPsi_eq_chi hm2 ℓ hℓ a μ s t h, hlamOf, hlamOf]
  have hψ1 : ∀ a₀ : Fin m, ψ (Multiplicative.ofAdd (Pi.single a₀ 1)) = 1 ∨
      ψ (Multiplicative.ofAdd (Pi.single a₀ 1)) = -1 := by
    intro a₀
    have h1 := hψχ _ _ _ true (rootSignD m a₀) (toStdD_single_eq hm2 a₀)
    have h2 := hχ2 _ _ (rootIdxD_ne m hm2 a₀) true (rootSignD m a₀)
    rw [← h1] at h2
    rcases mul_self_eq_one_iff.mp h2 with h3 | h3
    · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
    · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
  obtain ⟨v, hv⟩ := exists_vec_of_hom h2 ψ hψ1
  refine ⟨κ, v, fun γ hγ => ?_⟩
  obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := F) hm3 hγ
  have hstd' : toStdD m (-γ) = Pi.single i (boolSign (!s)) + Pi.single j (boolSign (!t)) := by
    have e : toStdD m (-γ) = -toStdD m γ := toStdD_neg m γ
    rw [e, hstd, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add]
  have hX1 : (plusDatum m F hm3).rootGroup γ = (Fr.longRoot hij s t).range := hX
  have hX2 : (plusDatum m F hm3).rootGroup (-γ) = (Fr.longRoot hij (!s) (!t)).range :=
    plusRootGroup_eq hm3 hij (!s) (!t) hstd'
  have hχγ : ((ψ (Multiplicative.ofAdd γ) : Fˣ) : F) = χ i s j t := hψχ γ i j s t hstd
  rw [hX1, hX2]
  have hAmem : ∀ (s' t' : Bool) (y : spinGroup (quadPlus m F)),
      y ∈ (Fr.longRoot hij s' t').range → A y ∈ (Fr.longRoot hij s' t').range := by
    rintro s' t' y ⟨c, rfl⟩
    rw [← ofAdd_toAdd c, hAroot]
    exact ⟨_, rfl⟩
  have hSA : ∀ y ∈ (Fr.longRoot hij s t).range ⊔ (Fr.longRoot hij (!s) (!t)).range,
      A y ∈ (Fr.longRoot hij s t).range ⊔ (Fr.longRoot hij (!s) (!t)).range := by
    have hle : (Fr.longRoot hij s t).range ⊔ (Fr.longRoot hij (!s) (!t)).range ≤
        ((Fr.longRoot hij s t).range ⊔ (Fr.longRoot hij (!s) (!t)).range).comap
          A.toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left (hAmem s t y hy)
      · exact Subgroup.mem_sup_right (hAmem (!s) (!t) y hy)
    exact fun y hy => hle hy
  refine ⟨map_normalized θ σ α A κ hαθ hA hA2 _ hSA, ?_⟩
  rw [← hv γ]
  constructor
  · intro hfix
    apply Units.ext
    rw [hχγ, Units.val_one]
    have hxS : Fr.longRoot hij s t (.ofAdd 1) ∈
        (Fr.longRoot hij s t).range ⊔ (Fr.longRoot hij (!s) (!t)).range :=
      Subgroup.mem_sup_left ⟨.ofAdd 1, rfl⟩
    have h1 := hfix (θ (κ * Fr.longRoot hij s t (.ofAdd 1) * κ⁻¹))
      ⟨κ * Fr.longRoot hij s t (.ofAdd 1) * κ⁻¹, ⟨_, hxS, rfl⟩, rfl⟩
    rw [← hαθ, hA, hAroot, mul_one] at h1
    have h2 : κ * Fr.longRoot hij s t (.ofAdd (χ i s j t - 1)) * κ⁻¹ ∈
        Subgroup.center (spinGroup (quadPlus m F)) := by
      apply hker
      rw [MonoidHom.mem_ker]
      have e : Fr.longRoot hij s t (.ofAdd (χ i s j t - 1)) =
          (Fr.longRoot hij s t (.ofAdd 1))⁻¹ * Fr.longRoot hij s t (.ofAdd (χ i s j t)) := by
        rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
        congr 2
        ring
      have e2 : κ * Fr.longRoot hij s t (.ofAdd (χ i s j t - 1)) * κ⁻¹ =
          (κ * Fr.longRoot hij s t (.ofAdd 1) * κ⁻¹)⁻¹ *
            (κ * Fr.longRoot hij s t (.ofAdd (χ i s j t)) * κ⁻¹) := by
        rw [e]
        group
      rw [e2, map_mul, map_inv, ← h1, inv_mul_cancel]
    exact sub_eq_zero.mp (eq_zero_of_conj_central hZ Fr hij s t _ κ h2)
  · intro hψ'
    have hχ1 : χ i s j t = 1 := by rw [← hχγ, hψ', Units.val_one]
    have hχ' : χ i (!s) j (!t) = 1 := by
      have hprod' : χ i (!s) j (!t) * χ i s j t = 1 := by
        calc χ i (!s) j (!t) * χ i s j t
            = (lam j (!t) * lam j t) * (lam i (!s) * lam i s) * ((μ : F)⁻¹ * (μ : F)⁻¹) := by
              simp only [hχ]
              ring
          _ = (μ : F) * (μ : F) * ((μ : F)⁻¹ * (μ : F)⁻¹) := by rw [hlam2, hlam2]
          _ = 1 := by field_simp
      rw [hχ1, mul_one] at hprod'
      exact hprod'
    have hle : (Fr.longRoot hij s t).range ⊔ (Fr.longRoot hij (!s) (!t)).range ≤
        MonoidHom.eqLocus A.toMonoidHom (MonoidHom.id _) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨c, rfl⟩ := hy
        rw [← ofAdd_toAdd c]
        change A _ = _
        rw [hAroot, hχ1, one_mul]
        rfl
      · obtain ⟨c, rfl⟩ := hy
        rw [← ofAdd_toAdd c]
        change A _ = _
        rw [hAroot, hχ', one_mul]
        rfl
    exact fixed_of_fixed θ σ α A κ hαθ hA _ (fun y hy => hle hy)

end Tail

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem toralNormal_plus_of_normalized (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {m : ℕ} (hm : 5 ≤ m) (hm3 : 3 ≤ m := by omega)
    {X : Type} [Group X] (θ : spinGroup (quadPlus m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin m} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) (s₀ t₀ s₁ t₁ : Bool) (k : spinGroup (quadPlus m F))
    (H1 : ∀ c : F, σ (θ (k * (plusFrame m F hm3).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹)) =
      θ (k * (plusFrame m F hm3).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹))
    (H1' : ∀ c : F, σ (θ (k * (plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) *
        k⁻¹)) = θ (k * (plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹))
    (H2 : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) (c : F),
        σ (θ (k * (plusFrame m F hm3).longRoot hab s t (.ofAdd c) * k⁻¹)) =
          θ (k * (plusFrame m F hm3).longRoot hab s t (.ofAdd c) * k⁻¹))
    (H3 : ∀ c : F, ∃ c' : F,
      σ (θ (k * (plusFrame m F hm3).longRoot hjc s₁ t₁ (.ofAdd c) * k⁻¹)) =
        θ (k * (plusFrame m F hm3).longRoot hjc s₁ t₁ (.ofAdd c') * k⁻¹)) :
    ∃ (k₀ : spinGroup (quadPlus m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m F hm3).roots →
        ((((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  obtain ⟨hZ, -⟩ := plus_center_facts (F := F) hp2 hm3
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift hp2 hm hf hF θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadPlus m F)) := isPerfect_spinGroup_quadPlus hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadPlus m F) →* _).comp
      (α : spinGroup (quadPlus m F) →* _)) (MonoidHom.id (spinGroup (quadPlus m F))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  set Fr := plusFrame m F hm3 with hFr
  have hfix : ∀ {i j : Fin m} (hij : i ≠ j) (s t : Bool) (c : F),
      σ (θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹)) =
        θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹) →
      conjTwist α k (Fr.longRoot hij s t (.ofAdd c)) = Fr.longRoot hij s t (.ofAdd c) :=
    fun hij s t c h => conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k
      (longRoot_pow_char Fr hij s t c) (longRoot_pow_char Fr hij s t c) h
  have hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c) := fun c => hfix h01 s₀ t₀ c (H1 c)
  have hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) := fun c => hfix h01.symm (!t₀) (!s₀) c (H1' c)
  obtain ⟨c', hc'⟩ := H3 1
  have hN : conjTwist α k (Fr.longRoot hjc s₁ t₁ (.ofAdd 1)) =
      Fr.longRoot hjc s₁ t₁ (.ofAdd c') :=
    conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k (longRoot_pow_char Fr hjc s₁ t₁ 1)
      (longRoot_pow_char Fr hjc s₁ t₁ c') hc'
  have hO : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ →
      b ≠ c₀ → ∀ (s t : Bool) (c : F), conjTwist α k (Fr.longRoot hab s t (.ofAdd c)) =
        Fr.longRoot hab s t (.ofAdd c) :=
    fun a b hab ha0 ha1 hac hb0 hb1 hbc s t c => hfix hab s t c (H2 a b hab ha0 ha1 hac hb0 hb1 hbc s t c)
  have hmul := hmul_of_normalized_group Fr h01 s₀ t₀ (plus_hspan hm3) hm hα k hA1 hA1' hc0 hc1 hj0
    hj1 hjc s₁ t₁ hO hN
  obtain ⟨κ, lam, hprod, hdiag⟩ := exists_diag_form_of_diag Fr h01 s₀ t₀ hm3 h2 hp2 (plus_hker2 m)
    hα hα2 k hA1 hA1' hmul
  exact toralNormal_plus_of_diag hm3 h2 hZ θ hker σ α hαθ hα2 g.μ κ lam hprod hdiag

theorem toralNormal_plus_of_normalized_subgroups (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {m : ℕ} (hm : 5 ≤ m) (hm3 : 3 ≤ m := by omega)
    {X : Type} [Group X] (θ : spinGroup (quadPlus m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin m} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) {s₀ t₀ s₁ t₁ : Bool} {γ₀ γ₁ : Fin m → ℤ}
    (hγ₀ : toStdD m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (hγ₁ : toStdD m γ₁ = Pi.single c₀ (boolSign s₁) + Pi.single j (boolSign t₁))
    (k : spinGroup (quadPlus m F))
    (H1 : ∀ y ∈ (((plusDatum m F hm3).rootGroup γ₀ ⊔ (plusDatum m F hm3).rootGroup (-γ₀)).map
        (MulAut.conj k).toMonoidHom), σ (θ y) = θ y)
    (H2 : ∀ (a b : Fin m), a ≠ b → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) {γ : Fin m → ℤ},
        toStdD m γ = Pi.single a (boolSign s) + Pi.single b (boolSign t) →
          ∀ y ∈ ((plusDatum m F hm3).rootGroup γ).map (MulAut.conj k).toMonoidHom,
            σ (θ y) = θ y)
    (H3 : ∀ y ∈ ((plusDatum m F hm3).rootGroup γ₁).map (MulAut.conj k).toMonoidHom,
      σ (θ y) ∈ (((plusDatum m F hm3).rootGroup γ₁).map (MulAut.conj k).toMonoidHom).map θ) :
    ∃ (k₀ : spinGroup (quadPlus m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m F hm3).roots →
        ((((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have hX1 : (plusDatum m F hm3).rootGroup γ₀ = ((plusFrame m F hm3).longRoot h01 s₀ t₀).range :=
    plusRootGroup_eq hm3 h01 s₀ t₀ hγ₀
  have hstd' : toStdD m (-γ₀) = Pi.single i₁ (boolSign (!t₀)) + Pi.single i₀ (boolSign (!s₀)) := by
    have e : toStdD m (-γ₀) = -toStdD m γ₀ := toStdD_neg m γ₀
    rw [e, hγ₀, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add, add_comm]
  have hX2 : (plusDatum m F hm3).rootGroup (-γ₀) =
      ((plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀)).range :=
    plusRootGroup_eq hm3 h01.symm (!t₀) (!s₀) hstd'
  have hX3 : (plusDatum m F hm3).rootGroup γ₁ = ((plusFrame m F hm3).longRoot hjc s₁ t₁).range :=
    plusRootGroup_eq hm3 hjc s₁ t₁ hγ₁
  refine toralNormal_plus_of_normalized hp2 hf hF hm hm3 θ hker σ hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc
    s₀ t₀ s₁ t₁ k (fun c => ?_) (fun c => ?_)
    (fun a b hab ha0 ha1 hac hb0 hb1 hbc s t c => ?_) (fun c => ?_)
  · refine H1 _ ⟨_, Subgroup.mem_sup_left ?_, rfl⟩
    rw [hX1]
    exact ⟨_, rfl⟩
  · refine H1 _ ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
    rw [hX2]
    exact ⟨_, rfl⟩
  · obtain ⟨γ, -, hγ⟩ := exists_mem_rootsD_toStdD_eq m hab (boolSign_eq_one_or_eq_neg_one s)
      (boolSign_eq_one_or_eq_neg_one t)
    have hXγ : (plusDatum m F hm3).rootGroup γ = ((plusFrame m F hm3).longRoot hab s t).range :=
      plusRootGroup_eq hm3 hab s t hγ
    refine H2 a b hab ha0 ha1 hac hb0 hb1 hbc s t hγ _ ⟨_, ?_, rfl⟩
    rw [hXγ]
    exact ⟨_, rfl⟩
  · have h1 := H3 (k * (plusFrame m F hm3).longRoot hjc s₁ t₁ (.ofAdd c) * k⁻¹) ⟨_, ?_, rfl⟩
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
