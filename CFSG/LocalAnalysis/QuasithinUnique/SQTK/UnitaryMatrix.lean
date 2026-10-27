module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

public section

namespace CFSG.QuasithinUnique.SQTK

open Matrix TauCeti CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section SignedReversal

variable (r : ℕ) (R : Type*) [CommRing R]

theorem typeAGraphConjugator_apply (i j : Fin (r + 1)) :
    ((typeAGraphConjugator r R : GL (Fin (r + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i j =
      if i = j.rev then (-1 : R) ^ (i : ℕ) else 0 := by
  simp [typeAGraphConjugator, typeAGraphSign]

theorem transpose_typeAGraphConjugator :
    ((typeAGraphConjugator r R : GL (Fin (r + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R)ᵀ =
      (-1 : R) ^ r • ((typeAGraphConjugator r R : GL (Fin (r + 1)) R) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) R) := by
  ext i j
  simp only [transpose_apply, typeAGraphConjugator_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : j = i.rev
  · have h' : i = j.rev := by rw [h, Fin.rev_rev]
    have hij : (i : ℕ) + (j : ℕ) = r := by
      rw [h]; simp [Fin.val_rev]; omega
    rw [ite_eq_left h, ite_eq_left h']
    have hsq : ((-1 : R) ^ (i : ℕ)) * ((-1 : R) ^ (i : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    calc (-1 : R) ^ (j : ℕ)
        = (-1 : R) ^ (j : ℕ) * (((-1 : R) ^ (i : ℕ)) * ((-1 : R) ^ (i : ℕ))) := by
          rw [hsq, mul_one]
      _ = (-1 : R) ^ ((i : ℕ) + (j : ℕ)) * (-1 : R) ^ (i : ℕ) := by rw [pow_add]; ring
      _ = _ := by rw [hij]
  · have h' : ¬ i = j.rev := by intro hh; apply h; rw [hh, Fin.rev_rev]
    rw [ite_eq_right h, ite_eq_right h']; simp

end SignedReversal

section Hermitian

variable {F : Type} [Field F] [Finite F] {p k : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_hermitianScalar (hF : Nat.card F = (p ^ k) ^ 2) (r : ℕ) :
    ∃ c : F, c ≠ 0 ∧ unitaryInvolution F p k c * (-1 : F) ^ r = c := by
  rcases Nat.even_or_odd r with h | h
  · exact ⟨1, one_ne_zero, by rw [map_one, h.neg_one_pow, mul_one]⟩
  · obtain ⟨c, hc0, hc⟩ := exists_unitaryInvolution_eq_neg hF
    exact ⟨c, hc0, by rw [hc, h.neg_one_pow]; ring⟩

theorem exists_orthonormalConjugator (hF : Nat.card F = (p ^ k) ^ 2) (r : ℕ) :
    ∃ (B : GL (Fin (r + 1)) F) (c : F), c ≠ 0 ∧
      conjTr (unitaryInvolution F p k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *
        (c • (typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) *
          (B : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 := by
  obtain ⟨c, hc0, hc⟩ := exists_hermitianScalar hF r
  set σ := unitaryInvolution F p k with hσ
  let A : GL (Fin (r + 1)) F :=
    Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (Units.mk0 c hc0) * typeAGraphConjugator r F
  have hA : (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      c • (typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
    change Matrix.scalar (Fin (r + 1)) c * _ = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hsq : σ ^ 2 = 1 := by
    ext x
    rw [pow_two]
    exact unitaryInvolution_involutive hF x
  have hne : σ ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := exists_unitaryInvolution_ne hF
    exact ha (by rw [← hσ, h]; rfl)
  have hherm : conjTr σ (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = A := by
    rw [hA]
    have hfix : (typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map σ =
        (typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
      have := congrArg (fun g : GL (Fin (r + 1)) F => (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F))
        (map_typeAGraphConjugator σ.toRingHom r)
      exact this
    ext i j
    simp only [conjTr, transpose_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    have h1 : σ ((typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F) j i) =
        (typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F) j i :=
      congrFun (congrFun hfix j) i
    have h2 := congrFun (congrFun (transpose_typeAGraphConjugator r F) i) j
    simp only [transpose_apply, Matrix.smul_apply, smul_eq_mul] at h2
    rw [h1, h2]
    linear_combination (typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F) i j * hc
  obtain ⟨B, hB⟩ := CFSG.ComponentClassification.CatalogueBHermitian.exists_orthonormal_matrix
    σ hsq hne A hherm
  exact ⟨B, c, hc0, by rw [hA] at hB; exact hB⟩

end Hermitian

end CFSG.QuasithinUnique.SQTK
