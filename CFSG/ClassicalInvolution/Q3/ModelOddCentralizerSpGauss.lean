module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUCommutant
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

section SU

variable {F : Type} [Field F] [Finite F] [hF3 : Fact (Nat.card F = 3)] {m : ℕ}

theorem gaussBlocks_symplectic {A : Matrix (Fin m) (Fin m) (GaussField F)}
    (h : conjTr (gaussSigma (F := F)) A * A = 1) :
    (gaussBlocks m A)ᵀ * gram F m * gaussBlocks m A = gram F m :=
  (symplectic_gaussBlocks_iff gaussSigma gaussSigma_apply A).mpr h

theorem conjTr_of_gaussBlocks_symplectic {A : Matrix (Fin m) (Fin m) (GaussField F)}
    (h : (gaussBlocks m A)ᵀ * gram F m * gaussBlocks m A = gram F m) :
    conjTr (gaussSigma (F := F)) A * A = 1 :=
  (symplectic_gaussBlocks_iff gaussSigma gaussSigma_apply A).mp h

@[expose] noncomputable def suToSp (m : ℕ) : SUid (gaussSigma (F := F)) m →* StatedSp m F where
  toFun A := ofSymplecticMat
    (gaussBlocks m (((A : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F))))
    (gaussBlocks_symplectic A.2.2)
  map_one' := mat_injective (by
    rw [mat_ofSymplecticMat, map_one]
    simp)
  map_mul' A B := mat_injective (by
    rw [mat_ofSymplecticMat, map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat, ← map_mul]
    simp)

theorem mat_suToSp (A : SUid (gaussSigma (F := F)) m) :
    mat m F (suToSp m A) =
      gaussBlocks m ((A : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) :=
  rfl

theorem suToSp_injective : Function.Injective (suToSp (F := F) m) := fun A B h =>
  Subtype.ext (Units.ext (gaussBlocks_injective (by
    rw [← mat_suToSp, ← mat_suToSp, h])))

theorem conjTr_scalar (σ : GaussField F ≃+* GaussField F) (c : GaussField F) :
    conjTr σ (Matrix.scalar (Fin m) c) = Matrix.scalar (Fin m) (σ c) := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp [conjTr, Matrix.scalar_apply]
  · simp [conjTr, Matrix.scalar_apply, h, Ne.symm h]

theorem conjTr_scalar_omega_mul :
    conjTr (gaussSigma (F := F)) (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) *
      Matrix.scalar (Fin m) QuadraticAlgebra.omega = 1 := by
  rw [conjTr_scalar, gaussSigma_omega, ← map_mul, neg_mul, ← mul_neg, omega_mul_neg_omega,
    map_one]

@[expose] noncomputable def gComplex (m : ℕ) : StatedSp m F :=
  ofSymplecticMat (Matrix.fromBlocks 0 (-1) 1 0) (by
    rw [← gaussBlocks_scalar_omega (F := F) (m := m)]
    exact gaussBlocks_symplectic conjTr_scalar_omega_mul)

theorem mat_gComplex :
    mat m F (gComplex m) =
      gaussBlocks m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) := by
  rw [gaussBlocks_scalar_omega]
  rfl

theorem gaussSigma_gaussSigma (z : GaussField F) :
    gaussSigma (F := F) (gaussSigma (F := F) z) = z := by
  rw [gaussSigma_apply, gaussSigma_apply]
  apply QuadraticAlgebra.ext <;> simp

theorem conjTr_conjTr (A : Matrix (Fin m) (Fin m) (GaussField F)) :
    conjTr (gaussSigma (F := F)) (conjTr (gaussSigma (F := F)) A) = A := by
  refine Matrix.ext fun i j => ?_
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
  exact gaussSigma_gaussSigma (A i j)

theorem exists_su_conj {A : Matrix (Fin m) (Fin m) (GaussField F)}
    (hA : conjTr (gaussSigma (F := F)) A * A = 1) (X : SUid (gaussSigma (F := F)) m) :
    ∃ X' : SUid (gaussSigma (F := F)) m,
      ((X' : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) =
        A * ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) *
          conjTr (gaussSigma (F := F)) A := by
  have hAA : A * conjTr (gaussSigma (F := F)) A = 1 := mul_eq_one_comm.mp hA
  obtain ⟨hdet, hu⟩ := X.2
  set Xm : Matrix (Fin m) (Fin m) (GaussField F) :=
    ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) with hXm
  have hdet' : (A * Xm * conjTr gaussSigma A).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdet, mul_one, ← Matrix.det_mul, hAA, Matrix.det_one]
  have hu' : conjTr gaussSigma (A * Xm * conjTr gaussSigma A) * (A * Xm * conjTr gaussSigma A) =
      1 := by
    calc conjTr gaussSigma (A * Xm * conjTr gaussSigma A) * (A * Xm * conjTr gaussSigma A)
        = A * (conjTr gaussSigma Xm * (conjTr gaussSigma A * A) * Xm) * conjTr gaussSigma A := by
          rw [conjTr_mul, conjTr_mul, conjTr_conjTr]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one, hu, Matrix.mul_one, hAA]
  exact ⟨mkSU _ hdet' hu', rfl⟩

theorem exists_unitary_of_mem_centralizer {x : StatedSp m F}
    (hx : x ∈ Subgroup.centralizer ({gComplex m} : Set (StatedSp m F))) :
    ∃ A : Matrix (Fin m) (Fin m) (GaussField F), gaussBlocks m A = mat m F x ∧
      conjTr (gaussSigma (F := F)) A * A = 1 := by
  have hc : mat m F x * Matrix.fromBlocks 0 (-1) 1 0 =
      Matrix.fromBlocks 0 (-1) 1 0 * mat m F x := by
    have := congrArg (mat m F) (Subgroup.mem_centralizer_singleton_iff.mp hx)
    rw [map_mul, map_mul] at this
    exact this
  obtain ⟨A, hA⟩ := exists_gaussBlocks_of_commute hc
  refine ⟨A, hA, conjTr_of_gaussBlocks_symplectic ?_⟩
  rw [hA]
  exact mat_transpose_mul_gram_mul x

theorem mem_centralizer_of_unitary {A : Matrix (Fin m) (Fin m) (GaussField F)}
    (hA : conjTr (gaussSigma (F := F)) A * A = 1) :
    ofSymplecticMat (gaussBlocks m A) (gaussBlocks_symplectic hA) ∈
      Subgroup.centralizer ({gComplex m} : Set (StatedSp m F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul, mat_ofSymplecticMat, mat_gComplex, ← map_mul, ← map_mul]
  congr 1
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) A).eq.symm

theorem suToSp_mem_centralizer (X : SUid (gaussSigma (F := F)) m) :
    suToSp m X ∈ Subgroup.centralizer ({gComplex m} : Set (StatedSp m F)) :=
  mem_centralizer_of_unitary X.2.2

theorem conj_mem_range_suToSp {x : StatedSp m F}
    (hx : x ∈ Subgroup.centralizer ({gComplex m} : Set (StatedSp m F)))
    {y : StatedSp m F} (hy : y ∈ (suToSp (F := F) m).range) : x * y * x⁻¹ ∈ (suToSp m).range := by
  obtain ⟨A, hA, hAu⟩ := exists_unitary_of_mem_centralizer hx
  obtain ⟨X, rfl⟩ := hy
  obtain ⟨X', hX'⟩ := exists_su_conj hAu X
  refine ⟨X', mat_injective ?_⟩
  have hAA : A * conjTr (gaussSigma (F := F)) A = 1 := mul_eq_one_comm.mp hAu
  have hinv : mat m F x⁻¹ = gaussBlocks m (conjTr (gaussSigma (F := F)) A) := by
    have h1 : mat m F x * gaussBlocks m (conjTr (gaussSigma (F := F)) A) = 1 := by
      rw [← hA, ← map_mul, hAA, map_one]
    calc mat m F x⁻¹ = mat m F x⁻¹ * (mat m F x * gaussBlocks m (conjTr gaussSigma A)) := by
          rw [h1, Matrix.mul_one]
      _ = gaussBlocks m (conjTr gaussSigma A) := by
          rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
  rw [mat_suToSp, map_mul, map_mul, hinv, ← hA, mat_suToSp, ← map_mul, ← map_mul]
  have := congrArg (gaussBlocks m) hX'
  rw [this]

theorem exists_pow_four_of_commute_range_suToSp (hm : 2 ≤ m) {x : StatedSp m F}
    (hx : x ∈ Subgroup.centralizer ({gComplex m} : Set (StatedSp m F)))
    (hc : ∀ y ∈ (suToSp (F := F) m).range, x * y = y * x) : x ^ 4 = 1 := by
  obtain ⟨A, hA, hAu⟩ := exists_unitary_of_mem_centralizer hx
  have hcomm : ∀ X : SUid (gaussSigma (F := F)) m,
      A * ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) =
        ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) * A := by
    intro X
    apply gaussBlocks_injective
    rw [map_mul, map_mul, hA, ← mat_suToSp, ← map_mul, ← map_mul, hc _ ⟨X, rfl⟩]
  obtain ⟨c, rfl⟩ := exists_scalar_of_commute_su hm hcomm
  have hc4 : c ^ 4 = 1 := by
    rw [conjTr_scalar, ← map_mul] at hAu
    have h1 := congrFun (congrFun hAu ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
    have h2 : gaussSigma (F := F) c = c ^ 3 := by
      rw [gaussSigma_apply, gauss_pow_three]
    rw [h2] at h1
    calc c ^ 4 = c ^ 3 * c := by ring
      _ = 1 := h1
  apply mat_injective
  rw [map_pow, ← hA, ← map_pow, ← map_pow, hc4, map_one, map_one, map_one]

end SU

end CFSG.ClassicalInvolution.Q3
