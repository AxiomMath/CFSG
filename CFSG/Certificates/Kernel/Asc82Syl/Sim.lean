module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.KS.Asc82Syl

open Matrix

def Sim (D M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop := Mᵀ * D * M = D ∨ Mᵀ * D * M = -D

theorem Sim_iff {D M : Matrix (Fin 6) (Fin 6) (ZMod 3)} :
    Sim D M ↔ Mᵀ * D * M = D ∨ Mᵀ * D * M = -D := Iff.rfl

theorem Sim_one (D : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Sim D 1 :=
  Or.inl (by rw [transpose_one, one_mul, mul_one])

theorem Sim_mul {D M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : Sim D M) (hN : Sim D N) :
    Sim D (M * N) := by
  have e : (M * N)ᵀ * D * (M * N) = Nᵀ * (Mᵀ * D * M) * N := by
    rw [transpose_mul]
    simp only [Matrix.mul_assoc]
  unfold Sim
  rw [e]
  rcases hM with h | h <;> rw [h]
  · exact hN
  · rw [mul_neg, neg_mul]
    rcases hN with h' | h'
    · exact Or.inr (by rw [h'])
    · exact Or.inl (by rw [h', neg_neg])

theorem Sim_isUnit {D M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hD : IsUnit D.det) (h : Sim D M) :
    IsUnit M := by
  rw [isUnit_iff_isUnit_det]
  have hdet : M.det * M.det * D.det = 1 * D.det := by
    have hneg : (-D).det = D.det := by
      rw [det_neg, Fintype.card_fin]
      ring
    have e : ∀ x y : ZMod 3, x * x * y = x * y * x := fun x y => by ring
    rcases h with h | h
    · have := congrArg det h
      rw [det_mul, det_mul, det_transpose] at this
      rw [e, this, one_mul]
    · have := congrArg det h
      rw [det_mul, det_mul, det_transpose, hneg] at this
      rw [e, this, one_mul]
  exact IsUnit.of_mul_eq_one _ (hD.mul_right_cancel hdet)

end CFSG.KS.Asc82Syl

end
