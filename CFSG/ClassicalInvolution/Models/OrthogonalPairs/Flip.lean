module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Reflection
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace Frame

@[expose] def flip (F : Frame Q) : Frame Q where
  P := ⟨F.P.f, F.P.e, F.P.Q_f, F.P.Q_e, HypPair.polar_fe F.P⟩
  P' := ⟨F.P'.f, F.P'.e, F.P'.Q_f, F.P'.Q_e, HypPair.polar_fe F.P'⟩
  orth := ⟨F.orth.ff, F.orth.fe, F.orth.ef, F.orth.ee⟩

variable (F : Frame Q)

@[expose] def invTranspose (A : SL(2, K)) : SL(2, K) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) K) 1 1, -(A : Matrix (Fin 2) (Fin 2) K) 1 0;
    -(A : Matrix (Fin 2) (Fin 2) K) 0 1, (A : Matrix (Fin 2) (Fin 2) K) 0 0], by
    have := A.2
    rw [Matrix.det_fin_two] at this
    simp only [Matrix.det_fin_two_of]
    linear_combination this⟩

theorem invTranspose_invTranspose (A : SL(2, K)) : invTranspose (invTranspose A) = A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invTranspose]

theorem La_flip (A : SL(2, K)) : F.flip.La A = F.La (invTranspose A) := by
  refine LinearEquiv.ext fun x => ?_
  rw [La_apply, La_apply]
  congr 1
  obtain ⟨p, q, r, s, hA⟩ := exists_eq_of_fin_two (A : Matrix (Fin 2) (Fin 2) K)
  simp [incl_apply, coords_apply, flip, invTranspose, hA]
  module

theorem La_range_flip : F.flip.La.range = F.La.range := by
  ext y
  rw [MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨invTranspose A, (La_flip F A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨invTranspose A, ?_⟩
    rw [La_flip, invTranspose_invTranspose]

end Frame

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
