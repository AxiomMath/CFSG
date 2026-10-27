module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OP

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise MatrixGroups

section Split

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)] {V : Type} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] [Module (GaussField F) V]
  [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V} {a : V ≃ₗ[F] V}

theorem exists_cplx_comm_of_split (hF : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (h4 : Module.finrank (GaussField F) V = 4)
    {S : Submodule (GaussField F) V} (hS2 : Module.finrank (GaussField F) S = 2)
    (hS0 : ∀ x ∈ S, Gauss.gaussQuad Q hω hg x = 0) :
    ∃ y : V ≃ₗ[F] V, y ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ v, y (y v) = -v) ∧
      y * a = a * y := by
  have := Gauss.finiteDimensional_gauss F V
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hQq := Gauss.nondegenerate_gaussQuad h2 hω hg hQ
  obtain ⟨ψ, e, -, -, heS⟩ :=
    split_four_determinant_form_isometry (Gauss.gaussQuad Q hω hg) hQq h4 S hS2 hS0
  let J : SL(2, GaussField F) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  set g := e.symm (specialRho (J, 1)) with hgdef
  have hgv : ∀ v, (g : V ≃ₗ[GaussField F] V) v =
      ψ.symm (!![0, -1; 1, 0] * ψ v) := fun v => by
    rw [hgdef, heS, specialRho_apply]
    simp [J]
  refine ⟨Gauss.res F (g : V ≃ₗ[GaussField F] V),
    Gauss.res_mem_orthogonalGroup h2 hω hg g.2, fun v => ?_, Gauss.res_mul_a hω _⟩
  rw [Gauss.res_apply, Gauss.res_apply, hgv, hgv, LinearEquiv.apply_symm_apply, ← Matrix.mul_assoc]
  have hJJ : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (GaussField F)) * !![0, -1; 1, 0] = -1 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hJJ, Matrix.neg_mul, Matrix.one_mul, map_neg, LinearEquiv.symm_apply_apply]

end Split

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

theorem exists_cplx_comm_of_sq_neg_one {a : V₈ ≃ₗ[𝔽₃] V₈} (hsim : ∀ v, Q₄ (a v) = -1 * Q₄ v)
    (ha2 : ∀ v, a (a v) = -v) :
    ∃ y : V₈ ≃ₗ[𝔽₃] V₈, y ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ ∧ (∀ v, y (y v) = -v) ∧
      y * a = a * y := by
  have hK : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
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
  exact exists_cplx_comm_of_split hK hQ hω hsim h4 hS2 hS0

theorem simFam_neg_one_neg_one : SimFam (-1) (-1) := by
  intro a hsim ha2 β hodd hβ
  have hK : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  have ha2' : ∀ v, a (a v) = -v := fun v => by rw [ha2, neg_one_smul]
  obtain ⟨y, hyO, hy2, hya⟩ := exists_cplx_comm_of_sq_neg_one hsim ha2'
  have hmem := mem_commutator_of_sq_neg_one hK (nondegenerate_polarBilin_quadPlus 4 𝔽₃)
    finrank_d4 hyO hy2
  have hΩ := symm_mem_statedOmega hmem
  have hE : y ∈ elementaryGroup Q₄ := by
    rwa [commutator_orthogonalGroup_quadPlus (by norm_num)] at hmem
  obtain ⟨x, hx, hxc⟩ := exists_spin_of_mem_elementary hE hΩ
  refine typeII_smul hK β hodd ⟨_, hΩ⟩ (fun v => ?_) ?_
  · simp only [MulEquiv.apply_symm_apply]
    exact hy2 v
  · rw [← hxc]
    exact hβ x (by rw [hx]; exact hya)

section Final


theorem d4OutCentR_proved : D4OutCentR :=
  d4OutCentR_of simFam_one_one simFam_one_neg_one simFam_neg_one_one simFam_neg_one_neg_one

theorem omegaAutOddFreeR_proved : OmegaAutOddFreeR :=
  omegaAutOddFreeR_of_outCent d4OutCentR_proved

end Final

end CFSG.ClassicalInvolution.Q3.TL4
