module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPstd
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSL44

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix Subgroup CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd CFSG.ClassicalInvolution.WeakCT
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped MatrixGroups

theorem pSL_eq_lu (a₁ a₂ a₃ a₄ a₅ a₈ : F4) :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ = lu a₁ a₄ a₂ a₈ a₅ a₃ := by
  refine Subtype.ext ?_
  rw [coe_lu]
  rfl

theorem lu_eq_pSL (a b f c d e : F4) : lu a b f c d e = pSL a f e b d c :=
  (pSL_eq_lu a f e b d c).symm

theorem pSL_one_zero (a : F4) :
    pSL a 0 0 0 0 0 = SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) a := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [tv_apply]
  fin_cases i <;> fin_cases j <;> simp [pMat]

theorem pSL_three_two (a : F4) :
    pSL 0 0 a 0 0 0 = SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 2 by decide) a := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [tv_apply]
  fin_cases i <;> fin_cases j <;> simp [pMat]

theorem mem_rootSL_pSL_one_zero (a : F4) : pSL a 0 0 0 0 0 ∈ rootSL F4 1 0 := by
  rw [pSL_one_zero]
  exact Subgroup.subset_closure ⟨_, a, rfl⟩

theorem mem_rootSL_pSL_three_two (a : F4) : pSL 0 0 a 0 0 0 ∈ rootSL F4 3 2 := by
  rw [pSL_three_two]
  exact Subgroup.subset_closure ⟨_, a, rfl⟩

theorem decomp_of_involutions (x u₁ u₂ : SL(4, F4)) (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) :
    x = u₁ * u₂ * (u₂ * (u₁ * x)) :=
  calc x = u₁ * (u₁ * x) := by rw [← mul_assoc, h₁, one_mul]
    _ = u₁ * (u₂ * (u₂ * (u₁ * x))) := by rw [← mul_assoc u₂ u₂, h₂, one_mul]
    _ = u₁ * u₂ * (u₂ * (u₁ * x)) := by rw [mul_assoc]

theorem frobF4_frobF4 (x : F4) : frobeniusEquiv F4 2 (frobeniusEquiv F4 2 x) = x := by
  simp only [frobeniusEquiv_apply, frobenius_def]
  exact F4.sq_sq x

theorem sig_fieldAut_fieldAut (A : SL(4, F4)) :
    fieldAutSL (frobeniusEquiv F4 2) 4 (fieldAutSL (frobeniusEquiv F4 2) 4 A) = A := by
  refine Subtype.ext ?_
  rw [coe_fieldAutSL, coe_fieldAutSL, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  exact frobF4_frobF4 _

theorem sig_antiDiag_map :
    (antiDiag F4).map (frobeniusEquiv F4 2) = antiDiag F4 :=
  map_permMatrix F4 (frobeniusEquiv F4 2) Fin.revPerm

theorem sig_antiDiag_transpose : (antiDiag F4)ᵀ = antiDiag F4 := by
  rw [antiDiag, transpose_permMatrix]
  congr 1

theorem sig_conj_conj (A : SL(4, F4)) :
    conjSL (antiDiag F4) (antiDiag F4) (antiDiag_mul_self F4)
      (conjSL (antiDiag F4) (antiDiag F4) (antiDiag_mul_self F4) A) = A := by
  refine Subtype.ext ?_
  rw [coe_conjSL, coe_conjSL]
  calc antiDiag F4 * (antiDiag F4 * (A : Matrix (Fin 4) (Fin 4) F4) * antiDiag F4) * antiDiag F4
      = (antiDiag F4 * antiDiag F4) * (A : Matrix (Fin 4) (Fin 4) F4) *
          (antiDiag F4 * antiDiag F4) := by simp only [Matrix.mul_assoc]
    _ = (A : Matrix (Fin 4) (Fin 4) F4) := by
        rw [antiDiag_mul_self F4, Matrix.one_mul, Matrix.mul_one]

theorem sig_fieldAut_conj (A : SL(4, F4)) :
    fieldAutSL (frobeniusEquiv F4 2) 4
        (conjSL (antiDiag F4) (antiDiag F4) (antiDiag_mul_self F4) A) =
      conjSL (antiDiag F4) (antiDiag F4) (antiDiag_mul_self F4)
        (fieldAutSL (frobeniusEquiv F4 2) 4 A) := by
  refine Subtype.ext ?_
  rw [coe_fieldAutSL, coe_conjSL, coe_conjSL, coe_fieldAutSL, Matrix.map_mul, Matrix.map_mul,
    sig_antiDiag_map]

theorem sig_invT_conj (A : SL(4, F4)) :
    invTransposeSL 4 (conjSL (antiDiag F4) (antiDiag F4) (antiDiag_mul_self F4) A) =
      conjSL (antiDiag F4) (antiDiag F4) (antiDiag_mul_self F4) (invTransposeSL 4 A) := by
  refine Subtype.ext ?_
  rw [coe_invTransposeSL, ← map_inv (conjSL (antiDiag F4) (antiDiag F4) (antiDiag_mul_self F4)),
    coe_conjSL, coe_conjSL, coe_invTransposeSL, Matrix.transpose_mul, Matrix.transpose_mul,
    sig_antiDiag_transpose]
  simp only [Matrix.mul_assoc]

theorem sig_fieldAut_invT (A : SL(4, F4)) :
    fieldAutSL (frobeniusEquiv F4 2) 4 (invTransposeSL 4 A) =
      invTransposeSL 4 (fieldAutSL (frobeniusEquiv F4 2) 4 A) := by
  refine Subtype.ext ?_
  rw [coe_fieldAutSL, coe_invTransposeSL, coe_invTransposeSL,
    ← map_inv (fieldAutSL (frobeniusEquiv F4 2) 4), coe_fieldAutSL, Matrix.transpose_map]

theorem sig_invT_invT (A : SL(4, F4)) : invTransposeSL 4 (invTransposeSL 4 A) = A :=
  (invTransposeSL 4).left_inv A

theorem sigmaSL_sigmaSL (g : SL(4, F4)) : sigmaSL F4 (sigmaSL F4 g) = g := by
  rw [sigmaSL_apply F4 (sigmaSL F4 g), sigmaSL_apply F4 g, sig_fieldAut_conj, sig_invT_conj,
    sig_conj_conj, sig_fieldAut_invT, sig_invT_invT, sig_fieldAut_fieldAut]

theorem pstd_eq_PK : pstd F4 = PK := by
  refine Subgroup.ext fun x => ?_
  rw [mem_pstd_iff]
  constructor
  · intro hx
    exact ⟨_, _, _, _, _, _, (eq_lu_of_isLowerUni hx).trans (pSL_eq_lu _ _ _ _ _ _).symm⟩
  · rintro ⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩
    rw [pSL_eq_lu]
    exact isLowerUni_lu _ _ _ _ _ _

theorem exists_decomp_PK {x : SL(4, F4)} (hx : x ∈ PK) :
    ∃ u₁ ∈ rootSL F4 1 0, ∃ u₂ ∈ rootSL F4 3 2, ∃ y ∈ YK, x = u₁ * u₂ * y := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₈, hxe⟩ := hx
  have hy : pSL 0 0 a₃ 0 0 0 * (pSL a₁ 0 0 0 0 0 * x) =
      pSL 0 a₂ 0 a₄ (a₅ + a₃ * a₂) (a₈ + a₃ * a₄) := by
    rw [hxe, pSL_mul, pSL_mul, pSL_eq_pSL_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination a₁ * F4.two_eq_zero
    · ring
    · linear_combination a₃ * F4.two_eq_zero
    · ring
    · ring
    · ring
  have hu₁ : pSL a₁ 0 0 0 0 0 * pSL a₁ 0 0 0 0 0 = 1 :=
    pSL_mul_self_eq_one_iff.2 ⟨by ring, by ring, by ring⟩
  have hu₂ : pSL 0 0 a₃ 0 0 0 * pSL 0 0 a₃ 0 0 0 = 1 :=
    pSL_mul_self_eq_one_iff.2 ⟨by ring, by ring, by ring⟩
  refine ⟨pSL a₁ 0 0 0 0 0, mem_rootSL_pSL_one_zero a₁, pSL 0 0 a₃ 0 0 0,
    mem_rootSL_pSL_three_two a₃, pSL 0 a₂ 0 a₄ (a₅ + a₃ * a₂) (a₈ + a₃ * a₄),
    ⟨a₂, a₄, _, _, rfl⟩, ?_⟩
  rw [← hy]
  exact decomp_of_involutions x _ _ hu₁ hu₂

theorem sigmaSL_mem_PK {x : SL(4, F4)} (hx : x ∈ PK) : sigmaSL F4 x ∈ PK := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩ := hx
  rw [pSL_eq_lu, sigmaSL_lu, ← pstd_eq_PK]
  exact lu_mem_pstd _ _ _ _ _ _

theorem sigmaSL_mem_YK {x : SL(4, F4)} (hx : x ∈ YK) : sigmaSL F4 x ∈ YK := by
  obtain ⟨a₂, a₄, a₅, a₈, rfl⟩ := hx
  have h0 : (0 : F4) ^ 2 = 0 := by decide
  rw [pSL_eq_lu, sigmaSL_lu, lu_eq_pSL, h0]
  exact ⟨_, _, _, _, rfl⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
