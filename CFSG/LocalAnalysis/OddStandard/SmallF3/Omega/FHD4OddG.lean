module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitAction
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddLev

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped MatrixGroups Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

theorem fh_exists_rho {a : V₈ ≃ₗ[𝔽₃] V₈} (hsim : ∀ v, Q₄ (a v) = -1 * Q₄ v)
    (ha2 : ∀ v, a (a v) = -v) :
    ∃ ρ : SL(2, GaussField 𝔽₃) →* (V₈ ≃ₗ[𝔽₃] V₈),
      (∀ z, ρ z ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄) ∧ (∀ z, ρ z * a = a * ρ z) ∧
      ∀ z : SL(2, GaussField 𝔽₃),
        (z : Matrix (Fin 2) (Fin 2) (GaussField 𝔽₃)) * z = -1 → ∀ v, ρ z (ρ z v) = -v := by
  have hK : Nat.card 𝔽₃ = 3 :=
    CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
  have : Fact (Nat.card 𝔽₃ = 3) := ⟨hK⟩
  let _ : Module (GaussField 𝔽₃) V₈ := Gauss.gaussModule a ha2
  have : IsScalarTower 𝔽₃ (GaussField 𝔽₃) V₈ := ⟨fun c z v => by
    show (c • z).re • v + (c • z).im • a v = c • (z.re • v + z.im • a v)
    rw [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_add, smul_eq_mul, smul_eq_mul,
      mul_smul, mul_smul]⟩
  have hω : ∀ v, (QuadraticAlgebra.omega : GaussField 𝔽₃) • v = a v := fun v => by
    show (QuadraticAlgebra.omega : GaussField 𝔽₃).re • v +
      (QuadraticAlgebra.omega : GaussField 𝔽₃).im • a v = a v
    rw [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_smul, one_smul, zero_add]
  have hQ := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  have hfr := Gauss.finrank_gauss (F := 𝔽₃) (V := V₈)
  rw [finrank_d4] at hfr
  have h4 : Module.finrank (GaussField 𝔽₃) V₈ = 4 := by omega
  obtain ⟨hU4, hU0⟩ := flag_data (K := 𝔽₃) (n := 4) (i := 4) le_rfl
  obtain ⟨S, hS2, hS0⟩ := Gauss.exists_ts_plane hK hQ finrank_d4 hω hsim hU4
    (fun x hx => by rw [coe_quadPlus]; exact hU0 x hx)
  have := Gauss.finiteDimensional_gauss 𝔽₃ V₈
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hQq := Gauss.nondegenerate_gaussQuad h2 hω hsim hQ
  obtain ⟨ψ, e, -, -, heS⟩ :=
    split_four_determinant_form_isometry (Gauss.gaussQuad Q₄ hω hsim) hQq h4 S hS2 hS0
  let ρ : SL(2, GaussField 𝔽₃) →* (V₈ ≃ₗ[𝔽₃] V₈) :=
    (Gauss.res 𝔽₃).comp ((Subgroup.subtype _).comp (e.symm.toMonoidHom.comp
      (specialRho.comp (MonoidHom.inl SL(2, GaussField 𝔽₃) SL(2, GaussField 𝔽₃)))))
  have hρv : ∀ (z : SL(2, GaussField 𝔽₃)) v,
      ρ z v = ψ.symm ((z : Matrix (Fin 2) (Fin 2) (GaussField 𝔽₃)) * ψ v) := fun z v => by
    show (e.symm (specialRho (z, 1))).val v = _
    rw [heS, specialRho_apply]
    simp
  refine ⟨ρ, fun z => Gauss.res_mem_orthogonalGroup h2 hω hsim (e.symm (specialRho (z, 1))).2,
    fun z => Gauss.res_mul_a hω _, fun z hz v => ?_⟩
  rw [hρv, hρv, LinearEquiv.apply_symm_apply, ← Matrix.mul_assoc, hz, Matrix.neg_mul,
    Matrix.one_mul, map_neg, LinearEquiv.symm_apply_apply]

theorem fh_simFamO_neg_one_neg_one : FHSimFamO (-1) (-1) := by
  intro a hsim ha2 β hodd hβ
  have hK : Nat.card 𝔽₃ = 3 :=
    CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
  have : Fact (Nat.card 𝔽₃ = 3) := ⟨hK⟩
  have ha2' : ∀ v, a (a v) = -v := fun v => by rw [ha2, neg_one_smul]
  obtain ⟨ρ, hρO, hρa, hρ2⟩ := fh_exists_rho hsim ha2'
  have hE := fh_mem_elementary_of_perfect (isPerfect_specialLinear_gauss hK le_rfl) ρ hρO
  have h3 : (3 : GaussField 𝔽₃) = 0 := by exact_mod_cast CharP.cast_eq_zero (GaussField 𝔽₃) 3
  have hcube : ∀ z : SL(2, GaussField 𝔽₃), z ^ 3 = 1 → ρ z ^ 3 = 1 := fun z hz => by
    rw [← map_pow, hz, map_one]
  refine fh_smul_of_cubes hodd hβ (u₁ := ρ fhLevU2) (u₂ := ρ fhLevL2) (u₃ := ρ fhLevU2)
    (hE _) (hE _) (hE _) (hρa _) (hρa _) (hρa _) (hcube _ (fhLevU2_pow_three h3))
    (hcube _ (fhLevL2_pow_three h3)) (hcube _ (fhLevU2_pow_three h3)) fun v => ?_
  rw [← map_mul, ← map_mul]
  exact hρ2 _ fhLevJ2_sq v

end CFSG.OddStandard.SmallF3.Omega
