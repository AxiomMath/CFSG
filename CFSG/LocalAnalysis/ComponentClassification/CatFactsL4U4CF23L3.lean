module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23L3Type
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OddSelector.Catalog7L3
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Forms

variable {k : Type} [Field k] [Finite k]

theorem exists_congr_smul_three (hk2 : ringChar k ≠ 2) (R S : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) (hS : (S : Matrix (Fin 3) (Fin 3) k)ᵀ = S) :
    ∃ (F : Matrix (Fin 3) (Fin 3) k) (c : k), IsUnit F.det ∧ c ≠ 0 ∧
      Fᵀ * (S : Matrix (Fin 3) (Fin 3) k) * F = c • (R : Matrix (Fin 3) (Fin 3) k) := by
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hdim : Module.finrank k (Fin 3 → k) = 2 * 1 + 1 := by rw [Module.finrank_fin_fun]
  obtain ⟨d₁, hd₁, ⟨e₁⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd hk2
    (CatalogueBLinearHigherB.matrixQuadraticForm R)
    (CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR) hdim
  obtain ⟨d₂, hd₂, ⟨e₂⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd hk2
    (CatalogueBLinearHigherB.matrixQuadraticForm S)
    (CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 S hS) hdim
  set f := e₁.trans e₂.symm with hf
  have hfQ : ∀ v, d₂ * CatalogueBLinearHigherB.matrixQuadraticForm S (f v) =
      d₁ * CatalogueBLinearHigherB.matrixQuadraticForm R v := fun v => by
    have := f.map_app v
    simpa using this
  have hpol : ∀ (T : GL (Fin 3) k), (T : Matrix (Fin 3) (Fin 3) k)ᵀ = T → ∀ v w,
      CatalogueBLinearHigherB.matrixQuadraticForm T (v + w) -
        CatalogueBLinearHigherB.matrixQuadraticForm T v -
        CatalogueBLinearHigherB.matrixQuadraticForm T w =
      2 * (v ⬝ᵥ (T : Matrix (Fin 3) (Fin 3) k) *ᵥ w) := by
    intro T hT v w
    have h1 := LinearMap.congr_fun₂
      (CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm T hT) v w
    change QuadraticMap.polar _ v w = _ at h1
    rw [QuadraticMap.polar, Matrix.toBilin'_apply'] at h1
    rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hbil : ∀ v w, (f v ⬝ᵥ (S : Matrix (Fin 3) (Fin 3) k) *ᵥ f w) * d₂ =
      (v ⬝ᵥ (R : Matrix (Fin 3) (Fin 3) k) *ᵥ w) * d₁ := by
    intro v w
    have hS' := hpol S hS (f v) (f w)
    have hR' := hpol R hR v w
    rw [← map_add] at hS'
    have h3 : d₂ * (2 * (f v ⬝ᵥ (S : Matrix (Fin 3) (Fin 3) k) *ᵥ f w)) =
        d₁ * (2 * (v ⬝ᵥ (R : Matrix (Fin 3) (Fin 3) k) *ᵥ w)) := by
      rw [← hS', ← hR', mul_sub, mul_sub, mul_sub, mul_sub, hfQ, hfQ, hfQ]
    have h4 : (2 : k) * ((f v ⬝ᵥ (S : Matrix (Fin 3) (Fin 3) k) *ᵥ f w) * d₂ -
        (v ⬝ᵥ (R : Matrix (Fin 3) (Fin 3) k) *ᵥ w) * d₁) = 0 := by
      linear_combination h3
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left htwo)
  set F := LinearMap.toMatrix' (f.toLinearEquiv : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) with hF
  have hB : (Matrix.toBilin' (d₂ • (S : Matrix (Fin 3) (Fin 3) k))).comp
      (f.toLinearEquiv : (Fin 3 → k) →ₗ[k] (Fin 3 → k))
      (f.toLinearEquiv : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) =
      Matrix.toBilin' (d₁ • (R : Matrix (Fin 3) (Fin 3) k)) := by
    refine LinearMap.ext₂ fun v w => ?_
    rw [LinearMap.BilinForm.comp_apply, Matrix.toBilin'_apply', Matrix.toBilin'_apply',
      Matrix.smul_mulVec, dotProduct_smul, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, mul_comm d₂, mul_comm d₁]
    exact hbil v w
  have hM := congrArg LinearMap.BilinForm.toMatrix' hB
  rw [LinearMap.BilinForm.toMatrix'_comp, LinearMap.BilinForm.toMatrix'_toBilin',
    LinearMap.BilinForm.toMatrix'_toBilin', ← hF] at hM
  refine ⟨F, d₁ / d₂, ?_, div_ne_zero hd₁ hd₂, ?_⟩
  · apply Matrix.isUnit_det_of_right_inverse (B := LinearMap.toMatrix'
      (f.toLinearEquiv.symm : (Fin 3 → k) →ₗ[k] (Fin 3 → k)))
    rw [hF, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v
    simp
  · rw [Matrix.mul_smul, Matrix.smul_mul] at hM
    rw [div_eq_mul_inv, mul_comm, mul_smul, ← hM, smul_smul, inv_mul_cancel₀ hd₂, one_smul]

theorem exists_sl_congr_three (hk2 : ringChar k ≠ 2) (R S : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) (hS : (S : Matrix (Fin 3) (Fin 3) k)ᵀ = S)
    (hdet : (S : Matrix (Fin 3) (Fin 3) k).det = (R : Matrix (Fin 3) (Fin 3) k).det) :
    ∃ D : SpecialLinearGroup (Fin 3) k,
      (D : Matrix (Fin 3) (Fin 3) k)ᵀ * (R : Matrix (Fin 3) (Fin 3) k) * D = S := by
  obtain ⟨F, c, hFd, hc, hFRF⟩ := exists_congr_smul_three hk2 S R hS hR
  have hRd : (R : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := (Matrix.isUnits_det_units R).ne_zero
  have hF0 : F.det ≠ 0 := hFd.ne_zero
  have hdF : F.det ^ 2 = c ^ 3 := by
    have h1 := congrArg Matrix.det hFRF
    rw [det_mul, det_mul, det_transpose, det_smul, Fintype.card_fin, hdet] at h1
    apply mul_right_cancel₀ hRd
    linear_combination h1
  set μ := F.det / c with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero hF0 hc
  have hμ2 : μ ^ 2 = c := by
    rw [hμ, div_pow, hdF]
    field_simp
  have hμ3 : μ ^ 3 = F.det := by
    rw [hμ, div_pow, show F.det ^ 3 = F.det ^ 2 * F.det by ring, hdF]
    field_simp
  have hdetD : (μ⁻¹ • F).det = 1 := by
    rw [det_smul, Fintype.card_fin, inv_pow, hμ3, inv_mul_cancel₀ hF0]
  refine ⟨⟨μ⁻¹ • F, hdetD⟩, ?_⟩
  change (μ⁻¹ • F)ᵀ * (R : Matrix (Fin 3) (Fin 3) k) * (μ⁻¹ • F) = S
  rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hFRF, smul_smul,
    smul_smul, ← hμ2, show μ⁻¹ * μ⁻¹ * μ ^ 2 = 1 by field_simp, one_smul]

end Forms

section Coset

variable {k : Type} [Field k] {n : ℕ}

theorem conj_dual_eq (R D h : GL (Fin n) k)
    (hD : (D : Matrix (Fin n) (Fin n) k)ᵀ * R * D = (h : Matrix (Fin n) (Fin n) k)ᵀ * R) :
    (conjAut n k D)⁻¹ * (conjAut n k R⁻¹ * dualAut n k) * conjAut n k D =
      conjAut n k R⁻¹ * dualAut n k * conjAut n k h := by
  have hD' : (GeneralLinearGroup.inverseTranspose D)⁻¹ * R * D =
      (GeneralLinearGroup.inverseTranspose h)⁻¹ * R := Units.ext (by
    simp only [Units.val_mul]
    rw [coe_inverseTranspose_inv, coe_inverseTranspose_inv]
    exact hD)
  have key : D⁻¹ * R⁻¹ * GeneralLinearGroup.inverseTranspose D =
      R⁻¹ * GeneralLinearGroup.inverseTranspose h := by
    have h1 := congrArg (·⁻¹) hD'
    simp only [_root_.mul_inv_rev, inv_inv] at h1
    rw [← mul_assoc] at h1
    exact h1
  calc (conjAut n k D)⁻¹ * (conjAut n k R⁻¹ * dualAut n k) * conjAut n k D
      = conjAut n k D⁻¹ * conjAut n k R⁻¹ * (dualAut n k * conjAut n k D) := by
        rw [map_inv (conjAut n k) D]; group
    _ = conjAut n k (D⁻¹ * R⁻¹ * GeneralLinearGroup.inverseTranspose D) * dualAut n k := by
        rw [dualAut_mul_conjAut, map_mul, map_mul]; group
    _ = conjAut n k (R⁻¹ * GeneralLinearGroup.inverseTranspose h) * dualAut n k := by rw [key]
    _ = _ := by rw [map_mul, mul_assoc, ← dualAut_mul_conjAut, mul_assoc]

theorem l3_coset_fusion [Finite k] (hk2 : ringChar k ≠ 2) {G : Type} [Group G] {N : Subgroup G}
    (φ : N ≃* projectiveSL 3 k) {ρ : G →* MulAut (projectiveSL 3 k)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : N, ρ w = MulAut.conj (φ w)) {α : G}
    {B : GL (Fin 3) k} (hB : (B : Matrix (Fin 3) (Fin 3) k)ᵀ = B)
    (hρa : ρ α = conjAut 3 k B * dualAut 3 k) :
    ∀ x : G, orderOf x = 2 → α⁻¹ * x ∈ N → ∃ γ ∈ N, γ⁻¹ * α * γ = x := by
  intro x hx hαx
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨M, hM⟩ := proj_surjective 3 k (φ ⟨α⁻¹ * x, hαx⟩)
  have hρn : ρ (α⁻¹ * x) = conjAut 3 k (SpecialLinearGroup.toGL M) := by
    rw [conjAut_toGL, hM]
    exact hρW ⟨α⁻¹ * x, hαx⟩
  set X := B * GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL M) with hXdef
  have hρx : ρ x = conjAut 3 k X * dualAut 3 k := by
    have e : x = α * (α⁻¹ * x) := by group
    rw [e, map_mul, hρa, hρn, mul_assoc, dualAut_mul_conjAut, ← mul_assoc, ← map_mul]
  have hX2 : (conjAut 3 k X * dualAut 3 k) ^ 2 = 1 := by
    rw [← hρx, ← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hXs : (X : Matrix (Fin 3) (Fin 3) k)ᵀ = X := by
    rcases transpose_eq_or_eq_neg_of_pureGraph (le_refl 3) X hX2 with h | h
    · exact h
    · exact (false_of_transpose_eq_neg htwo X h).elim
  have hXinv : ((X⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      ((SpecialLinearGroup.toGL M : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ *
        ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    rw [hXdef, _root_.mul_inv_rev, Units.val_mul, coe_inverseTranspose_inv]
  have hdetX : ((X⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det =
      ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det := by
    rw [hXinv, det_mul, det_transpose]
    have hM1 : ((SpecialLinearGroup.toGL M : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det = 1 :=
      M.2
    rw [hM1, one_mul]
  obtain ⟨D, hD⟩ := exists_sl_congr_three hk2 B⁻¹ X⁻¹
    (CatalogueBLinearHigherB.transpose_inv_of_transpose_eq B hB)
    (CatalogueBLinearHigherB.transpose_inv_of_transpose_eq X hXs) hdetX
  have hD' : ((SpecialLinearGroup.toGL D : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ *
      ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      ((SpecialLinearGroup.toGL D : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      ((SpecialLinearGroup.toGL M : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ *
        ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    rw [← hXinv]
    exact hD
  have hconj := conj_dual_eq B⁻¹ (SpecialLinearGroup.toGL D) (SpecialLinearGroup.toGL M) hD'
  rw [inv_inv] at hconj
  refine ⟨φ.symm (proj 3 k D), (φ.symm (proj 3 k D)).2, ?_⟩
  apply hinj
  rw [map_mul, map_mul, map_inv, hρW, MulEquiv.apply_symm_apply, ← conjAut_toGL, hρa, hconj,
    ← hρa, ← hρn, ← map_mul, mul_inv_cancel_left]

end Coset

theorem cf23InnerFusionFor_PSL3 :
    CF23InnerFusionFor fun Y _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel Y .PSL 3 p f := by
  intro G _ _ N hN hC hτ α J hα hJN hJα hJ hstd hsm hZ hexc
  classical
  obtain ⟨p, f, hp, hp2, hf, hM⟩ := hτ
  have := hN
  obtain ⟨-, K, _, _, hK, ⟨φ₀⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hM
  let φ : N ≃* projectiveSL 3 K :=
    φ₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hZP := center_projectiveSL_eq_bot (k := K) (le_refl 3)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hC φ hZP
  have hL : CFSG.Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (isComponentOf_iff_isComponent_subgroupOf hJα).mpr hJ
  obtain ⟨-, -, -, hL₁⟩ := OddSelector.socle_images φ hinj hρW hJN hL
  have hsrc : (∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) := by
    rcases hsm with ⟨p', f', -, hp'2, -, -, hm⟩ | h7
    · exact Or.inl ⟨p', f', hp'2,
        LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm⟩
    · exact Or.inr h7
  obtain ⟨B, hB, hρa⟩ := l3_graph_form hα hp hp2 hf hK hinj hL₁ hsrc hZ
  exact concl_of_coset hα hJN hJα hZ (l3_coset_fusion hk2 φ hinj hρW hB hρa)

end CFSG.ComponentClassification.GSThmB.CF23I
