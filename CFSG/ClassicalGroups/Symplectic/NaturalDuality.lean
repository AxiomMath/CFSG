module

public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Symplectic

open Matrix CFSG.Open CFSG.Open.StatedAPI
open LinearMap (BilinForm)

section Basis

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

theorem eq_sum_equivFun {W : Submodule K E} (b : Module.Basis ι K W) (w : W) :
    (w : E) = ∑ i, b.equivFun w i • (b i : E) := by
  conv_lhs => rw [← b.sum_equivFun w]
  simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem equivFun_map_of_basis_action [DecidableEq ι] {W : Submodule K E}
    (b : Module.Basis ι K W) (T : E →ₗ[K] E) (A : Matrix ι ι K)
    (hb : ∀ i, T (b i : E) = ∑ j, A j i • (b j : E)) (hT : ∀ w ∈ W, T w ∈ W) (w : W) :
    b.equivFun ⟨T w, hT w w.2⟩ = A *ᵥ b.equivFun w := by
  have h1 : (⟨T w, hT w w.2⟩ : W) = b.equivFun.symm (A *ᵥ b.equivFun w) := by
    apply Subtype.ext
    rw [Module.Basis.equivFun_symm_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    have h := eq_sum_equivFun b w
    have h2 : T (w : E) = ∑ i, ∑ j, (b.equivFun w i * A j i) • (b j : E) := by
      rw [h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hb i, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
    show T (w : E) = _
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [h1, LinearEquiv.apply_symm_apply]

theorem map_basis_eq_sum_of_equivFun [DecidableEq ι] {W : Submodule K E}
    (b : Module.Basis ι K W) (T : E →ₗ[K] E) (hT : ∀ w ∈ W, T w ∈ W) (A : Matrix ι ι K)
    (hA : ∀ w : W, b.equivFun ⟨T w, hT w w.2⟩ = A *ᵥ b.equivFun w) (i : ι) :
    T (b i : E) = ∑ j, A j i • (b j : E) := by
  have h1 := hA (b i)
  have hsingle : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [hsingle, Matrix.mulVec_single_one] at h1
  have h2 := eq_sum_equivFun b ⟨T (b i : E), hT _ (b i).2⟩
  simp only at h2
  rw [h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1]
  rfl

end Basis

section Duality

variable {K : Type} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

theorem perfect_of_isotropic_nondegenerate (B : BilinForm K E) (hsymm : ∀ x y, B x y = B y x)
    {W₁ W₂ : Submodule K E} (hi₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, B x y = 0)
    (hi₂ : ∀ x ∈ W₂, ∀ y ∈ W₂, B x y = 0)
    (hnd : ∀ y ∈ W₁ ⊔ W₂, (∀ z ∈ W₁ ⊔ W₂, B y z = 0) → y = 0) :
    (∀ w ∈ W₂, (∀ v ∈ W₁, B v w = 0) → w = 0) ∧
      ∀ w ∈ W₁, (∀ v ∈ W₂, B w v = 0) → w = 0 := by
  constructor
  · intro w hw h
    refine hnd w (Submodule.mem_sup_right hw) fun z hz => ?_
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
    rw [(B w).map_add, hsymm w z₁, h z₁ hz₁, hi₂ w hw z₂ hz₂, add_zero]
  · intro w hw h
    refine hnd w (Submodule.mem_sup_left hw) fun z hz => ?_
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
    rw [(B w).map_add, hi₁ w hw z₁ hz₁, h z₂ hz₂, add_zero]

variable {m : ℕ}

theorem exists_equiv_of_perfect (B : BilinForm K E) {W₁ W₂ : Submodule K E} [Module.Finite K W₂]
    (b : Module.Basis (Fin m ⊕ Fin m) K W₁)
    (h₂ : ∀ w ∈ W₂, (∀ v ∈ W₁, B v w = 0) → w = 0)
    (h₁ : ∀ w ∈ W₁, (∀ v ∈ W₂, B w v = 0) → w = 0)
    {H : Type*} [Group H] (Φ : H →* (E ≃ₗ[K] E))
    (hΦB : ∀ h u v, B (Φ h u) (Φ h v) = B u v) (hΦ₂ : ∀ h, ∀ w ∈ W₂, Φ h w ∈ W₂)
    (ρ : H →* GL (Fin m ⊕ Fin m) K) (hρ : ∀ h, ρ h ∈ StatedSp m K)
    (hb : ∀ h i, Φ h (b i : E) =
      ∑ j, (ρ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i • (b j : E)) :
    ∃ e : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K), ∀ (h : H) (w : W₂),
      e ⟨Φ h w, hΦ₂ h w w.2⟩ = (ρ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e w := by
  classical
  let c : W₂ →ₗ[K] (Fin m ⊕ Fin m → K) := LinearMap.pi fun i => (B (b i : E)).comp W₂.subtype
  have hc : ∀ (w : W₂) i, c w i = B (b i : E) (w : E) := fun w i => rfl
  have hcinj : Function.Injective c := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hz : ∀ v ∈ W₁, B v (w : E) = 0 := by
      intro v hv
      have hv' := eq_sum_equivFun b ⟨v, hv⟩
      simp only at hv'
      rw [hv']
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      have := congrFun hw i
      rw [hc, Pi.zero_apply] at this
      rw [this, mul_zero]
    exact Subtype.ext (h₂ w w.2 hz)
  have hfin₁ : Module.Finite K W₁ := Module.Finite.of_basis b
  have hr₁ : Module.finrank K W₁ = 2 * m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
    ring
  have hr₂ : Module.finrank K W₂ = 2 * m := by
    apply le_antisymm
    · calc Module.finrank K W₂ ≤ Module.finrank K (Fin m ⊕ Fin m → K) :=
            LinearMap.finrank_le_finrank_of_injective hcinj
        _ = 2 * m := finrank_spSpace
    · rw [← hr₁]
      let d : W₁ →ₗ[K] Module.Dual K W₂ := B.compl₁₂ W₁.subtype W₂.subtype
      have hd : Function.Injective d := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro w hw
        rw [LinearMap.mem_ker] at hw
        exact Subtype.ext (h₁ w w.2 fun v hv => by
          have := LinearMap.congr_fun hw ⟨v, hv⟩
          exact this)
      calc Module.finrank K W₁ ≤ Module.finrank K (Module.Dual K W₂) :=
            LinearMap.finrank_le_finrank_of_injective hd
        _ = Module.finrank K W₂ := Subspace.dual_finrank_eq
  have hcsurj : Function.Surjective c :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hr₂.trans finrank_spSpace.symm)).mp hcinj
  have hJinv : Invertible (spJ m K) :=
    ⟨-spJ m K, by rw [neg_mul, spJ_mul_spJ, neg_neg], by rw [mul_neg, spJ_mul_spJ, neg_neg]⟩
  let Jeq : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K) := Matrix.toLinearEquiv' (spJ m K) hJinv
  have hJeq : ∀ v, Jeq v = spJ m K *ᵥ v := fun v => rfl
  refine ⟨(LinearEquiv.ofBijective c ⟨hcinj, hcsurj⟩).trans Jeq, fun h w => ?_⟩
  show Jeq (c ⟨Φ h w, hΦ₂ h w w.2⟩) = _
  rw [hJeq]
  show _ = _ *ᵥ Jeq (c w)
  rw [hJeq]
  set A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := ((ρ h⁻¹ : GL (Fin m ⊕ Fin m) K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hA
  set R : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := ((ρ h : GL (Fin m ⊕ Fin m) K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hR
  have hcΦ : c ⟨Φ h w, hΦ₂ h w w.2⟩ = Aᵀ *ᵥ c w := by
    funext i
    rw [hc]
    have e1 : B (b i : E) (Φ h w) = B (Φ h⁻¹ (b i : E)) w := by
      have h1 := hΦB h (Φ h⁻¹ (b i : E)) w
      have h2 : Φ h (Φ h⁻¹ (b i : E)) = (b i : E) := by
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h2] at h1
      exact h1
    show B (b i : E) (Φ h w) = _
    rw [e1, hb h⁻¹ i]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc]
  have hAR : A * R = 1 := by
    rw [hA, hR, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hAsp : Aᵀ * spJ m K * A = spJ m K := mem_statedSp_iff.mp (hρ h⁻¹)
  have hAJ : Aᵀ * spJ m K = spJ m K * R := by
    calc Aᵀ * spJ m K = Aᵀ * spJ m K * (A * R) := by rw [hAR, Matrix.mul_one]
      _ = (Aᵀ * spJ m K * A) * R := by simp only [Matrix.mul_assoc]
      _ = spJ m K * R := by rw [hAsp]
  have hJA : spJ m K * Aᵀ = R * spJ m K := by
    have h3 : spJ m K * (Aᵀ * spJ m K) * spJ m K = spJ m K * (spJ m K * R) * spJ m K := by
      rw [hAJ]
    have h4 : spJ m K * (Aᵀ * spJ m K) * spJ m K = -(spJ m K * Aᵀ) := by
      calc spJ m K * (Aᵀ * spJ m K) * spJ m K = spJ m K * Aᵀ * (spJ m K * spJ m K) := by
            simp only [Matrix.mul_assoc]
        _ = -(spJ m K * Aᵀ) := by rw [spJ_mul_spJ]; simp
    have h5 : spJ m K * (spJ m K * R) * spJ m K = -(R * spJ m K) := by
      calc spJ m K * (spJ m K * R) * spJ m K = (spJ m K * spJ m K) * (R * spJ m K) := by
            simp only [Matrix.mul_assoc]
        _ = -(R * spJ m K) := by rw [spJ_mul_spJ]; simp
    exact neg_injective (h4.symm.trans (h3.trans h5))
  rw [hcΦ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hJA]

theorem exists_equiv_of_isotropic_nondegenerate [Module.Finite K E] (B : BilinForm K E)
    (hsymm : ∀ x y, B x y = B y x) {W₁ W₂ : Submodule K E}
    (hi₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, B x y = 0) (hi₂ : ∀ x ∈ W₂, ∀ y ∈ W₂, B x y = 0)
    (hnd : ∀ y ∈ W₁ ⊔ W₂, (∀ z ∈ W₁ ⊔ W₂, B y z = 0) → y = 0)
    (b : Module.Basis (Fin m ⊕ Fin m) K W₁)
    {H : Type*} [Group H] (Φ : H →* (E ≃ₗ[K] E))
    (hΦB : ∀ h u v, B (Φ h u) (Φ h v) = B u v) (hΦ₂ : ∀ h, ∀ w ∈ W₂, Φ h w ∈ W₂)
    (ρ : H →* GL (Fin m ⊕ Fin m) K) (hρ : ∀ h, ρ h ∈ StatedSp m K)
    (hb : ∀ h i, Φ h (b i : E) =
      ∑ j, (ρ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i • (b j : E)) :
    ∃ e : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K), ∀ (h : H) (w : W₂),
      e ⟨Φ h w, hΦ₂ h w w.2⟩ = (ρ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e w := by
  obtain ⟨h₂, h₁⟩ := perfect_of_isotropic_nondegenerate B hsymm hi₁ hi₂ hnd
  exact exists_equiv_of_perfect B b h₂ h₁ Φ hΦB hΦ₂ ρ hρ hb

end Duality

end CFSG.ClassicalGroups.Symplectic
