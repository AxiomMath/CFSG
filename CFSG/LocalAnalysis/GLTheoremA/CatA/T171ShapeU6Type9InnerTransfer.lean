module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerDiagMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.StandardType.Line63.H5 CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K] {n d : ℕ}

theorem conj_mem_guSet_of_mem_primeFormUnitary [Finite K] (h : UnitaryFieldData 2 n K)
    {P : GL (Fin d) K} (hP : P ∈ primeFormUnitary h (idGram K d))
    {A : GL (Fin d) K} (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    P⁻¹ * A * P ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hA
  have hμ' : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) =
      μ • (1 : Matrix (Fin d) (Fin d) K) := by
    simpa only [map_pow_eq_map_bar h] using hμ
  have hP' : ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (P : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [mem_primeFormUnitary] at hP
    simpa [idGram] using hP
  have hQ : ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
      Units.val (P⁻¹) := by
    have h2 : ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (P : Matrix (Fin d) (Fin d) K) *
        Units.val (P⁻¹) = Units.val (P⁻¹) := by
      rw [hP', Matrix.one_mul]
    rwa [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h2
  have hQP : (P : Matrix (Fin d) (Fin d) K) *
      ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ = 1 := by
    have h1 : (P : Matrix (Fin d) (Fin d) K) * Units.val (P⁻¹) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rwa [← hQ] at h1
  have hbarbar : ((P : Matrix (Fin d) (Fin d) K).map h.bar).map h.bar =
      (P : Matrix (Fin d) (Fin d) K) := by
    ext i j
    simp [Matrix.map_apply, h.bar_bar]
  have hmapQ : ((((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ).map h.bar) =
      (P : Matrix (Fin d) (Fin d) K)ᵀ := by
    rw [show ((((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ).map h.bar) =
        ((((P : Matrix (Fin d) (Fin d) K).map h.bar).map h.bar)ᵀ) from rfl, hbarbar]
  have hNmat : (((P⁻¹ * A * P : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
      ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) *
        (P : Matrix (Fin d) (Fin d) K) := by
    rw [Units.val_mul, Units.val_mul, hQ]
  have hmapN : ((((P⁻¹ * A * P : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K).map h.bar) =
      (P : Matrix (Fin d) (Fin d) K)ᵀ * ((A : Matrix (Fin d) (Fin d) K).map h.bar) *
        ((P : Matrix (Fin d) (Fin d) K).map h.bar) := by
    rw [hNmat, Matrix.map_mul, Matrix.map_mul, hmapQ]
  refine ⟨μ, hμ0, hμq, ?_⟩
  have hmain : (((↑(P⁻¹ * A * P) : Matrix (Fin d) (Fin d) K)).map h.bar)ᵀ *
      (↑(P⁻¹ * A * P) : Matrix (Fin d) (Fin d) K) = μ • 1 := by
    rw [hmapN, Matrix.transpose_mul, Matrix.transpose_mul, hNmat]
    calc ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
          (((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (P : Matrix (Fin d) (Fin d) K)) *
          (((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) *
            (P : Matrix (Fin d) (Fin d) K))
        = ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
            ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
            ((P : Matrix (Fin d) (Fin d) K) * ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ) *
            (A : Matrix (Fin d) (Fin d) K) * (P : Matrix (Fin d) (Fin d) K) := by
          noncomm_ring
      _ = ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
            ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) *
            (P : Matrix (Fin d) (Fin d) K) := by rw [hQP, Matrix.mul_one]
      _ = ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
            (((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K)) *
            (P : Matrix (Fin d) (Fin d) K) := by noncomm_ring
      _ = ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
            (μ • (1 : Matrix (Fin d) (Fin d) K)) * (P : Matrix (Fin d) (Fin d) K) := by rw [hμ']
      _ = μ • (1 : Matrix (Fin d) (Fin d) K) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, hQ]
          congr 1
          rw [Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  simpa only [map_pow_eq_map_bar h] using hmain

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
