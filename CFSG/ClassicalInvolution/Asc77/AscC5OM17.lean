module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM16

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem natCard_sl2 (K : Type) [Field K] [Finite K] :
    Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card K with hq
  have hq1 : 1 < q := by rw [hq, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by omega : 0 < q - 1)]

variable (μ : F)

theorem card_quadAlg : Nat.card (QuadraticAlgebra F μ 0) = Nat.card F * Nat.card F := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd μ 0), Nat.card_prod]

theorem finite_quadAlg [Finite F] : Finite (QuadraticAlgebra F μ 0) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd μ 0).symm

variable [Fact (¬ IsSquare μ)]

theorem ker_phiSL_comp {Y : Type} [Group Y] (φ : StatedSp 2 F →* Y)
    (hφ : φ.ker = spScalars 2 F) :
    (φ.comp (phiSL μ)).ker = Subgroup.center SL(2, QuadraticAlgebra F μ 0) := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφ, mem_spScalars_iff,
    CFSG.ClassicalInvolution.mem_center_sl2_iff]
  constructor
  · rintro (h | h)
    · left
      apply Subtype.ext
      apply phiM_injective μ
      rw [Matrix.SpecialLinearGroup.coe_one, phiM_one, ← mat_phiSL, h, map_one]
    · right
      apply Subtype.ext
      apply phiM_injective μ
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, phiM_neg_one,
        ← mat_phiSL, h, mat_negOne]
  · rintro (rfl | rfl)
    · left
      exact map_one _
    · right
      apply mat_injective
      rw [mat_phiSL, mat_negOne, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, phiM_neg_one]

variable [Finite F]

theorem isSimpleGroup_range_phiSL (h4 : 4 ≤ Nat.card F) {Y : Type} [Group Y]
    (φ : StatedSp 2 F →* Y) (hφ : φ.ker = spScalars 2 F) :
    IsSimpleGroup (φ.comp (phiSL μ)).range := by
  have : Finite (QuadraticAlgebra F μ 0) := finite_quadAlg μ
  have h4E : 4 ≤ Nat.card (QuadraticAlgebra F μ 0) := by
    rw [card_quadAlg]
    nlinarith
  have : IsSimpleGroup PSL(2, QuadraticAlgebra F μ 0) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4E
  let e : (φ.comp (phiSL μ)).range ≃* PSL(2, QuadraticAlgebra F μ 0) :=
    (QuotientGroup.quotientKerEquivRange (φ.comp (phiSL μ))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (ker_phiSL_comp μ φ hφ))
  exact e.isSimpleGroup

theorem card_range_phiSL (hodd : Odd (Nat.card F)) {Y : Type} [Group Y]
    (φ : StatedSp 2 F →* Y) (hφ : φ.ker = spScalars 2 F) :
    2 * Nat.card (φ.comp (phiSL μ)).range = Nat.card SL(2, QuadraticAlgebra F μ 0) := by
  have : Finite (QuadraticAlgebra F μ 0) := finite_quadAlg μ
  have hoddE : Odd (Nat.card (QuadraticAlgebra F μ 0)) := by
    rw [card_quadAlg]
    exact hodd.mul hodd
  have h := Subgroup.card_ker_mul_card_range (φ.comp (phiSL μ))
  rw [ker_phiSL_comp μ φ hφ, CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hoddE
    (MulEquiv.refl _)] at h
  exact h

@[expose] def upE : SL(2, QuadraticAlgebra F μ 0) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def loE : SL(2, QuadraticAlgebra F μ 0) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
theorem exists_not_comm_range_phiSL (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y]
    (φ : StatedSp 2 F →* Y) (hφ : φ.ker = spScalars 2 F) :
    ∃ x y : (φ.comp (phiSL μ)).range, x * y ≠ y * x := by
  refine ⟨⟨_, upE μ, rfl⟩, ⟨_, loE μ, rfl⟩, fun h => ?_⟩
  have h1 := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h1
  rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
    ker_phiSL_comp μ φ hφ, CFSG.ClassicalInvolution.mem_center_sl2_iff, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul] at h1
  have hul : ((upE μ * loE μ : SL(2, QuadraticAlgebra F μ 0)) :
      Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) = !![2, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [upE, loE, Matrix.mul_fin_two]
    norm_num
  have hlu : ((loE μ * upE μ : SL(2, QuadraticAlgebra F μ 0)) :
      Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) = !![1, 1; 1, 2] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [upE, loE, Matrix.mul_fin_two]
    norm_num
  rcases h1 with h1 | h1
  · have e1 := congrArg (fun g : SL(2, QuadraticAlgebra F μ 0) =>
      (g : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0))) h1
    simp only [hul, hlu] at e1
    have e := congrArg (fun A : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0) => (A 0 0).re) e1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.re_one] at e
    have : (1 : F) = 0 := by linear_combination e
    exact one_ne_zero this
  · have e1 : ((upE μ * loE μ : SL(2, QuadraticAlgebra F μ 0)) :
        Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) =
        -((loE μ * upE μ : SL(2, QuadraticAlgebra F μ 0)) :
          Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) := by
      rw [h1, Matrix.SpecialLinearGroup.coe_mul (-1), Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, neg_one_mul]
    rw [hul, hlu] at e1
    have e := congrArg (fun A : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0) => (A 0 1).re) e1
    simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, QuadraticAlgebra.re_neg,
      QuadraticAlgebra.re_one] at e
    apply h2
    linear_combination e

end CFSG.ClassicalInvolution.Asc77.C5O.M
