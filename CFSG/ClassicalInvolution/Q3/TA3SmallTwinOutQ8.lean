module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinFrame
public import CFSG.GH74.L5U5.ModelsBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution QuaternionGroup CFSG.GH74.L5U5 Matrix

theorem frameOuterQ8Free_of_dichotomy {K : Type} [Group K] {J₂ J₄ : Subgroup K}
    (T : Set (MulAut K)) (hT : ∀ α ∈ T, ∀ β ∈ T, α * β = β * α)
    (h : ∀ α : MulAut K, (∀ j ∈ J₂, α j = j) → (∀ j ∈ J₄, α j = j) → α ∈ T ∨ α * α = 1) :
    FrameOuterQ8Free K J₂ J₄ := by
  intro ψ hψ h₂ h₄
  exfalso
  have hsq : ∀ q : QuaternionGroup 2, q * q ≠ 1 → ψ q ∈ T := fun q hq => by
    rcases h (ψ q) (h₂ q) (h₄ q) with h1 | h1
    · exact h1
    · exact absurd (hψ (by rw [map_mul, h1, map_one])) hq
  have := hT _ (hsq (a 1) (by decide)) _ (hsq (xa 0) (by decide))
  rw [← map_mul, ← map_mul] at this
  exact absurd (hψ this) (by decide)

variable {F : Type} [Field F]

@[expose] def blkScalar (c d : F) : Matrix (Fin 4) (Fin 4) F :=
  blk4 (Matrix.scalar (Fin 2) c) (Matrix.scalar (Fin 2) d)

theorem blkScalar_mul (c d c' d' : F) :
    blkScalar c d * blkScalar c' d' = blkScalar (c * c') (d * d') := by
  rw [blkScalar, blkScalar, blkScalar, blk4_mul, ← map_mul, ← map_mul]

theorem blkScalar_comm (c d c' d' : F) :
    blkScalar c d * blkScalar c' d' = blkScalar c' d' * blkScalar c d := by
  rw [blkScalar_mul, blkScalar_mul, mul_comm c, mul_comm d]

theorem blkScalar_one : blkScalar (1 : F) 1 = 1 := by
  rw [blkScalar, map_one, blk4_one]

theorem blkScalar_mul_inv {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    blkScalar c d * blkScalar c⁻¹ d⁻¹ = 1 := by
  rw [blkScalar_mul, mul_inv_cancel₀ hc, mul_inv_cancel₀ hd, blkScalar_one]

theorem blkScalar_comm_blk4 (c d : F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    blkScalar c d * blk4 X Y = blk4 X Y * blkScalar c d := by
  rw [blkScalar, blk4_mul, blk4_mul, Matrix.scalar_commute _ (fun _ => Commute.all _ _),
    Matrix.scalar_commute _ (fun _ => Commute.all _ _)]

theorem conj_blkScalar_comm {M M' : Matrix (Fin 4) (Fin 4) F} {N N' : Matrix (Fin 4) (Fin 4) F}
    (hMM : M * M' = M' * M) (hNN : N * N' = N' * N) (X : Matrix (Fin 4) (Fin 4) F) :
    M * (M' * X * N') * N = M' * (M * X * N) * N' :=
  calc M * (M' * X * N') * N = M * M' * X * (N' * N) := by simp only [Matrix.mul_assoc]
    _ = M' * M * X * (N * N') := by rw [hMM, hNN]
    _ = M' * (M * X * N) * N' := by simp only [Matrix.mul_assoc]

@[expose] def blkTorus (K : Subgroup (GL (Fin 4) F)) : Set (MulAut ↥K) :=
  {α | ∃ c d : F, c ≠ 0 ∧ d ≠ 0 ∧ ∀ x : ↥K,
    (((α x : ↥K) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkScalar c d * ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * blkScalar c⁻¹ d⁻¹}

theorem blkTorus_comm (K : Subgroup (GL (Fin 4) F)) :
    ∀ α ∈ blkTorus K, ∀ β ∈ blkTorus K, α * β = β * α := by
  rintro α ⟨c, d, -, -, hα⟩ β ⟨c', d', -, -, hβ⟩
  refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
  rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
  exact conj_blkScalar_comm (blkScalar_comm _ _ _ _) (blkScalar_comm _ _ _ _) _

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
