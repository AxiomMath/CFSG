module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X1
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Frame
public import CFSG.ClassicalInvolution.Phan.Center
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm spM simM IsSim mem_spM)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def spU (M : Matrix (Fin 4) (Fin 4) K) : Subgroup (SUid σ 4) :=
  (spM M).comap (suToSL σ 4)

@[expose] def simU (M : Matrix (Fin 4) (Fin 4) K) : Subgroup (SUid σ 4) :=
  (simM M).comap (suToSL σ 4)

theorem mem_spU {M : Matrix (Fin 4) (Fin 4) K} {x : SUid σ 4} :
    x ∈ spU M ↔ suMat x * M * (suMat x)ᵀ = M :=
  mem_spM

theorem commutator_simU_le_spU (M : Matrix (Fin 4) (Fin 4) K) :
    ⁅simU (σ := σ) M, simU (σ := σ) M⁆ ≤ spU (σ := σ) M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  show suToSL σ 4 ⁅a, b⁆ ∈ spM M
  rw [map_commutatorElement]
  exact MF2L.commutator_simM_le_spM M (Subgroup.commutator_mem_commutator ha hb)

theorem map_suMat (x : SUid σ 4) : (suMat x).map σ = (suMat x⁻¹)ᵀ := by
  have h1 : conjTr σ (suMat x) * suMat x = 1 := x.2.2
  have h2 : conjTr σ (suMat x) = suMat x⁻¹ := by
    calc conjTr σ (suMat x) = conjTr σ (suMat x) * (suMat x * suMat x⁻¹) := by
          rw [suMat_mul_suMat_inv, Matrix.mul_one]
      _ = suMat x⁻¹ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [conjTr] at h2
  rw [← h2, Matrix.transpose_transpose]

@[expose] def spFormInv (m n : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0]

theorem spForm_mul_inv {m n : K} (hm : m ≠ 0) (hn : n ≠ 0) :
    spForm m n * spFormInv m n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm, spFormInv, Matrix.mul_apply, Fin.sum_univ_four,
    hm, hn]

theorem spFormInv_mul {m n : K} (hm : m ≠ 0) (hn : n ≠ 0) :
    spFormInv m n * spForm m n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm, spFormInv, Matrix.mul_apply, Fin.sum_univ_four,
    hm, hn]

theorem mem_simU_of_fix (hσ : IsUnitaryInvolution σ) {X : Type} [Group X]
    (θ : SUid σ 4 →* X) (hker : θ.ker ≤ Subgroup.center (SUid σ 4))
    (α : SUid σ 4 →* SUid σ 4) {m n : K} (hm : m ≠ 0) (hn : n ≠ 0)
    (hα : ∀ x, suMat (α x) = spForm m n * (suMat x).map σ * spFormInv m n) {x : SUid σ 4}
    (hx : θ (α x) = θ x) : x ∈ simU (spForm m n) := by
  have hk : (α x)⁻¹ * x ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) (hker hk)
  have hu' : suMat ((α x)⁻¹ * x) = (u : K) • 1 := by
    rw [show suMat ((α x)⁻¹ * x) = (((α x)⁻¹ * x : SUid σ 4) : GL (Fin 4) K) from rfl, hu,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hX : suMat x = (u : K) • suMat (α x) := by
    have e : x = α x * ((α x)⁻¹ * x) := by group
    rw [e, suMat_mul, hu', Matrix.mul_smul, Matrix.mul_one]
    congr 1
    rw [← e]
  refine ⟨u, u.ne_zero, ?_⟩
  show suMat x * spForm m n * (suMat x)ᵀ = (u : K) • spForm m n
  have hT : (suMat x⁻¹)ᵀ * (suMat x)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, suMat_mul_suMat_inv, Matrix.transpose_one]
  calc suMat x * spForm m n * (suMat x)ᵀ
      = (u : K) • (spForm m n * (suMat x⁻¹)ᵀ * (spFormInv m n * spForm m n) *
          (suMat x)ᵀ) := by
        rw [hX, hα, map_suMat, Matrix.smul_mul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = (u : K) • spForm m n := by
        rw [spFormInv_mul hm hn, Matrix.mul_one, Matrix.mul_assoc, hT, Matrix.mul_one]

theorem lift_eq_of_mem_spU (α : SUid σ 4 →* SUid σ 4) {m n : K} (hm : m ≠ 0) (hn : n ≠ 0)
    (hα : ∀ x, suMat (α x) = spForm m n * (suMat x).map σ * spFormInv m n) {x : SUid σ 4}
    (hx : x ∈ spU (spForm m n)) : α x = x := by
  apply suMat_injective
  have hx' := mem_spU.mp hx
  have h : suMat x * spForm m n = spForm m n * (suMat x⁻¹)ᵀ := by
    calc suMat x * spForm m n = suMat x * spForm m n * ((suMat x)ᵀ * (suMat x⁻¹)ᵀ) := by
          rw [← Matrix.transpose_mul, suMat_inv_mul_suMat, Matrix.transpose_one, Matrix.mul_one]
      _ = (suMat x * spForm m n * (suMat x)ᵀ) * (suMat x⁻¹)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = spForm m n * (suMat x⁻¹)ᵀ := by rw [hx']
  rw [hα, map_suMat, ← h, Matrix.mul_assoc, spForm_mul_inv hm hn, Matrix.mul_one]

end CFSG.ClassicalInvolution.Asc77.CX.MF2U
