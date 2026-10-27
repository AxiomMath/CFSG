module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiag
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutChar
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

section Abstract

variable {K X : Type*} [Group K] [Group X]

theorem map_normalized (θ : K →* X) (σ : X ≃* X) (α A : K ≃* K) (κ : K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹)
    (hA2 : ∀ y, A (A y) = y) (S : Subgroup K) (hS : ∀ y ∈ S, A y ∈ S) :
    ((S.map (MulAut.conj κ).toMonoidHom).map θ).map σ.toMonoidHom =
      (S.map (MulAut.conj κ).toMonoidHom).map θ := by
  ext z
  constructor
  · rintro ⟨w, ⟨y', ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨κ * A y * κ⁻¹, ⟨A y, hS y hy, rfl⟩, ?_⟩
    change θ (κ * A y * κ⁻¹) = σ (θ (κ * y * κ⁻¹))
    rw [← hA, hαθ]
  · rintro ⟨y', ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨θ (κ * A y * κ⁻¹), ⟨κ * A y * κ⁻¹, ⟨A y, hS y hy, rfl⟩, rfl⟩, ?_⟩
    change σ (θ (κ * A y * κ⁻¹)) = θ (κ * y * κ⁻¹)
    rw [← hαθ, hA (A y), hA2]

theorem fixed_of_fixed (θ : K →* X) (σ : X ≃* X) (α A : K ≃* K) (κ : K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹)
    (S : Subgroup K) (hS : ∀ y ∈ S, A y = y) :
    ∀ z ∈ (S.map (MulAut.conj κ).toMonoidHom).map θ, σ z = z := by
  rintro _ ⟨y', ⟨y, hy, rfl⟩, rfl⟩
  change σ (θ (κ * y * κ⁻¹)) = θ (κ * y * κ⁻¹)
  rw [← hαθ, hA, hS y hy]

end Abstract

section PlusFacts

variable {F : Type} [Field F]

theorem plus_hspan {m : ℕ} (hn : 3 ≤ m) :
    ∀ x : Fin m ⊕ Fin m → F,
      (∀ a r, polar (quadPlus m F) x ((plusFrame m F hn).vec a r) = 0) → x = 0 := by
  intro x hx
  funext z
  rcases z with a | a
  · have h := hx a false
    simp only [plusFrame_vec, plusVec_false, polar_quadPlus_single_inr] at h
    simpa using h
  · have h := hx a true
    simp only [plusFrame_vec, plusVec_true, polar_quadPlus_single_inl] at h
    simpa using h

theorem plus_hker2 (m : ℕ) : ∀ x ∈ (spinAction (quadPlus m F)).ker, x * x = 1 := fun x hx => by
  rcases eq_one_or_eq_neg_one_of_spinAction_eq_one m F x (MonoidHom.mem_ker.mp hx) with h | h
  · exact spin_mul_self_eq_one (Or.inl (Subtype.ext h))
  · exact spin_mul_self_eq_one (Or.inr h)

variable [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem plus_center_facts (hp2 : p ≠ 2) {m : ℕ} (hn : 3 ≤ m) :
    (∀ ζ ∈ Subgroup.center (spinGroup (quadPlus m F)), ζ ^ p = 1 → ζ = 1) ∧
    (∀ ζ ∈ Subgroup.center (spinGroup (quadPlus m F)),
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x, spinAction (quadPlus m F) ζ x = η • x) := by
  have : NeZero m := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus m F)) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := F) hn
  have hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus m F))) :=
    not_dvd_card_center_spin (quadPlus m F) (range_spinMatrix_quadPlus hn) hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2
  refine ⟨fun ζ hζ hp1 => ?_, fun ζ hζ => ?_⟩
  · by_contra hne
    have h1 : orderOf ζ ∣ p := orderOf_dvd_of_pow_eq_one hp1
    have h2 : orderOf ζ = p := by
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    exact hC (h2 ▸ Subgroup.orderOf_dvd_natCard _ hζ)
  · have hζ' : ζ ∈ (StatedScalars _ F).comap (spinMatrix (quadPlus m F)) := by
      rw [← hcomap, hZ]
      exact hζ
    obtain ⟨c, hc⟩ := Subgroup.mem_comap.mp hζ'
    have hact : ∀ x, spinAction (quadPlus m F) ζ x = (c : F) • x := fun x => by
      rw [← spinMatrix_mulVec, ← hc]
      ext i
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
    refine ⟨(c : F), ?_, hact⟩
    have hQ : (quadPlus m F) (Pi.single (Sum.inl ⟨0, by omega⟩) 1 + Pi.single (Sum.inr ⟨0, by omega⟩) 1) = 1 := by
      rw [quadPlus_apply]
      simp [Pi.single_apply]
    have h1 := map_spinAction (quadPlus m F) ζ
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1 + Pi.single (Sum.inr ⟨0, by omega⟩) 1)
    rw [hact, QuadraticMap.map_smul, hQ] at h1
    have h2 : (c : F) * (c : F) = 1 := by simpa using h1
    exact mul_self_eq_one_iff.mp h2

end PlusFacts

section Lift

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_isConj_lift (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (θ : spinGroup (quadPlus n F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus n F))) (σ : X ≃* X)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range) :
    ∃ (α : spinGroup (quadPlus n F) ≃* spinGroup (quadPlus n F)) (g : SemiSim (quadPlus n F)),
      (∀ x, θ (α x) = σ (θ x)) ∧ IsConj α g := by
  have hσR : ∀ r ∈ θ.range, σ r ∈ θ.range := by
    rintro r ⟨k, rfl⟩
    exact hσr k
  let σR : θ.range ≃* θ.range :=
    { toFun := fun r => ⟨σ r, hσR r r.2⟩
      invFun := fun r => ⟨σ r, hσR r r.2⟩
      left_inv := fun r => Subtype.ext (hσ2 r)
      right_inv := fun r => Subtype.ext (hσ2 r)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : X) (b : X)) }
  have hkerR : θ.rangeRestrict.ker ≤ Subgroup.center (spinGroup (quadPlus n F)) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨α, hα, A, φ, μ, hQ, hA⟩ := spinPlus_exists_lift_similarity hp2 hn hf hF θ.rangeRestrict
    θ.rangeRestrict_surjective hkerR σR
  exact ⟨α, SemiSim.ofMatrix _ A φ μ hQ, fun x => congrArg Subtype.val (hα x),
    isConj_ofMatrix A φ μ hQ hA⟩

omit [Fact p.Prime] [CharP F p] in
theorem exists_unit_ne_one_ne_neg_one (hq : 5 ≤ Nat.card F) :
    ∃ u : Fˣ, (u : F) ≠ 1 ∧ (u : F) ≠ -1 := by
  classical
  have := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset Fˣ) ⊆ {1, -1} := by
    intro u _
    by_cases h1 : (u : F) = 1
    · have : u = 1 := Units.ext (by rw [Units.val_one]; exact h1)
      simp [this]
    · have : u = -1 := Units.ext (by rw [Units.val_neg, Units.val_one]; exact hcon u h1)
      simp [this]
  have h1 := Finset.card_le_card hsub
  have h2 : ({1, -1} : Finset Fˣ).card ≤ 2 := Finset.card_le_two
  have h3 : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units (α := F)
  rw [Nat.card_eq_fintype_card] at hq
  simp only [Finset.card_univ] at h1
  omega

end Lift

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] [Finite F] in
theorem eq_zero_of_conj_central {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {m : ℕ} (hZ : ∀ ζ ∈ Subgroup.center (spinGroup Q), ζ ^ p = 1 → ζ = 1)
    (Fr : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool) (c : F) (κ : spinGroup Q)
    (h : κ * Fr.longRoot hij s t (.ofAdd c) * κ⁻¹ ∈ Subgroup.center (spinGroup Q)) : c = 0 := by
  have hc : Fr.longRoot hij s t (.ofAdd c) ∈ Subgroup.center (spinGroup Q) := by
    have h1 := Subgroup.Normal.conj_mem
      (inferInstance : (Subgroup.center (spinGroup Q)).Normal) _ h κ⁻¹
    have h2 : κ⁻¹ * (κ * Fr.longRoot hij s t (.ofAdd c) * κ⁻¹) * κ⁻¹⁻¹ =
        Fr.longRoot hij s t (.ofAdd c) := by group
    rwa [h2] at h1
  have h1 := hZ _ hc (longRoot_pow_char Fr hij s t c)
  have h2 : Fr.longRoot hij s t (.ofAdd c) = Fr.longRoot hij s t (.ofAdd 0) := by
    rw [ofAdd_zero, map_one]
    exact h1
  exact Multiplicative.ofAdd.injective (Fr.longRoot_injective hij s t h2)

theorem toralNormal_plus (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hq : 5 ≤ Nat.card F) {m : ℕ} (hm : 5 ≤ m) (hm3 : 3 ≤ m := by omega)
    {X : Type} [Group X] (θ : spinGroup (quadPlus m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool) (k : spinGroup (quadPlus m F))
    (H1 : ∀ c : F, σ (θ (k * (plusFrame m F hm3).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹)) =
      θ (k * (plusFrame m F hm3).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹))
    (H1' : ∀ c : F, σ (θ (k * (plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) *
        k⁻¹)) = θ (k * (plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹))
    (H2 : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ u : Fˣ,
      σ (θ (k * (plusFrame m F hm3).longTorus hij true false u * k⁻¹)) =
        θ (k * (plusFrame m F hm3).longTorus hij true false u * k⁻¹)) :
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
  obtain ⟨hZ, hcent⟩ := plus_center_facts (F := F) hp2 hm3
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
  have hcen : ∀ y, σ (θ y) = θ y → α y * y⁻¹ ∈ Subgroup.center (spinGroup (quadPlus m F)) :=
    fun y hy => hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hy, mul_inv_cancel])
  obtain ⟨u, hu1, hu2⟩ := exists_unit_ne_one_ne_neg_one hq
  obtain ⟨κ, lam, hprod, hdiag⟩ := exists_diag_form (plusFrame m F hm3) h01 s₀ t₀ hm
    (plus_hspan hm3) h2 hp2 (plus_hker2 m) hZ hcent hu1 hu2 hα hα2 k
    (fun c => hcen _ (H1 c)) (fun c => hcen _ (H1' c))
    (fun i j hij hi0 hi1 hj0 hj1 => hcen _ (H2 i j hij hi0 hi1 hj0 hj1 u))
  set A := conjTwist α κ with hAdef
  have hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹ := fun y => by
    rw [hAdef, conjTwist_apply]
    group
  have hA2 : ∀ y, A (A y) = y := conjTwist_sq α hα2 κ
  set Fr := plusFrame m F hm3 with hFr
  set χ : Fin m → Bool → Fin m → Bool → F := fun i s j t =>
    lam j t * ((g.μ : F)⁻¹ * lam i s) with hχ
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
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hlam2 : ∀ k s, lam k (!s) * lam k s = (g.μ : F) := by
    intro k s
    cases s
    · simpa using hprod k
    · simpa [mul_comm] using hprod k
  have hlam0 : ∀ k s, lam k s ≠ 0 := fun k s h0 => hμ0 (by rw [← hlam2 k s, h0, mul_zero])
  let a : Fin m → Fˣ := fun k => Units.mk0 (lam k true) (hlam0 k true)
  have hlamOf : ∀ k s, lamOf a g.μ k s = lam k s := by
    intro k s
    cases s
    · have h0 := hlam0 k true
      simp only [lamOf, a, Bool.false_eq_true, ite_false, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [← hprod k]
      field_simp
    · simp [lamOf, a]
  have hm2 : 2 ≤ m := by omega
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin m, ℓ.val + 1 = m := ⟨⟨m - 1, by omega⟩, by simp only; omega⟩
  set ψ := charPsi a g.μ ℓ with hψdef
  have hψχ : ∀ (γ : Fin m → ℤ) (i j : Fin m) (s t : Bool),
      toStdD m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) →
        ((ψ (Multiplicative.ofAdd γ) : Fˣ) : F) = χ i s j t := by
    intro γ i j s t h
    rw [hψdef, charPsi_eq_chi hm2 ℓ hℓ a g.μ s t h, hlamOf, hlamOf]
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
            = (lam j (!t) * lam j t) * (lam i (!s) * lam i s) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by
              simp only [hχ]
              ring
          _ = (g.μ : F) * (g.μ : F) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by rw [hlam2, hlam2]
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


theorem toralNormal_plus_of_subgroups (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ Nat.card F) {m : ℕ} (hm : 5 ≤ m)
    (hm3 : 3 ≤ m := by omega) {X : Type} [Group X] (θ : spinGroup (quadPlus m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) {s₀ t₀ : Bool} {γ₀ : Fin m → ℤ}
    (hγ₀ : toStdD m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (k : spinGroup (quadPlus m F))
    (H1 : ∀ y ∈ (((plusDatum m F hm3).rootGroup γ₀ ⊔ (plusDatum m F hm3).rootGroup (-γ₀)).map
        (MulAut.conj k).toMonoidHom), σ (θ y) = θ y)
    (T : Subgroup (spinGroup (quadPlus m F)))
    (hT : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ u : Fˣ,
      (plusFrame m F hm3).longTorus hij true false u ∈ T)
    (H2 : ∀ t ∈ T, σ (θ (k * t * k⁻¹)) = θ (k * t * k⁻¹)) :
    ∃ (k₀ : spinGroup (quadPlus m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m F hm3).roots →
        ((((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  have hX1 : (plusDatum m F hm3).rootGroup γ₀ = ((plusFrame m F hm3).longRoot h01 s₀ t₀).range :=
    plusRootGroup_eq hm3 h01 s₀ t₀ hγ₀
  have hstd' : toStdD m (-γ₀) = Pi.single i₁ (boolSign (!t₀)) + Pi.single i₀ (boolSign (!s₀)) := by
    have e : toStdD m (-γ₀) = -toStdD m γ₀ := toStdD_neg m γ₀
    rw [e, hγ₀, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add, add_comm]
  have hX2 : (plusDatum m F hm3).rootGroup (-γ₀) =
      ((plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀)).range :=
    plusRootGroup_eq hm3 h01.symm (!t₀) (!s₀) hstd'
  refine toralNormal_plus hp2 hf hF hq hm hm3 θ hker σ hσ2 hσr h01 s₀ t₀ k (fun c => ?_) (fun c => ?_)
    (fun i j hij hi0 hi1 hj0 hj1 u => H2 _ (hT i j hij hi0 hi1 hj0 hj1 u))
  · refine H1 _ ⟨_, Subgroup.mem_sup_left ?_, rfl⟩
    rw [hX1]
    exact ⟨_, rfl⟩
  · refine H1 _ ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
    rw [hX2]
    exact ⟨_, rfl⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
