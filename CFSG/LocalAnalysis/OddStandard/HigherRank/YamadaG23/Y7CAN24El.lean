module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Blk

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

@[expose] def n24El (P : GL (Fin 3) (ZMod 2)) (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    GL (Fin 6) (ZMod 2) where
  val := n24Blk (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) Q 0 (P : Matrix (Fin 3) (Fin 3) (ZMod 2))
  inv := n24Blk ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Q *
      ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) 0
    ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
  val_inv := by
    have h1 : (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.mul_inv P
    have h2 : (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Q *
          ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) +
        Q * ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      exact n24_add_self _
    rw [n24Blk_mul, h1, h2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact n24Blk_one
  inv_val := by
    have h1 : ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.inv_mul P
    have h2 : ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Q +
        (((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Q *
          ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *
          (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
      rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      exact n24_add_self _
    rw [n24Blk_mul, h1, h2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact n24Blk_one

theorem coe_n24El (P : GL (Fin 3) (ZMod 2)) (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (n24El P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      n24Blk (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) Q 0 (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  rfl

theorem n24El_mul (P P' : GL (Fin 3) (ZMod 2)) (Q Q' : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    n24El P Q * n24El P' Q' =
      n24El (P * P') ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Q' +
        Q * (P' : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_n24El, coe_n24El, coe_n24El, n24Blk_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.val_mul]

theorem n24El_one : n24El 1 0 = 1 := by
  refine Units.ext ?_
  rw [coe_n24El]
  exact n24Blk_one

theorem n24El_inj {P P' : GL (Fin 3) (ZMod 2)} {Q Q' : Matrix (Fin 3) (Fin 3) (ZMod 2)} :
    n24El P Q = n24El P' Q' ↔ P = P' ∧ Q = Q' := by
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 6) (ZMod 2) => (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
    simp only [coe_n24El] at h'
    obtain ⟨h1, h2, -, -⟩ := n24Blk_inj h'
    exact ⟨Units.ext h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem n24El_inv (P : GL (Fin 3) (ZMod 2)) (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (n24El P Q)⁻¹ = n24El P⁻¹ (((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      Q * ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  refine Units.ext ?_
  rfl

theorem dg_eq_n24El (A : GL (Fin 3) (ZMod 2)) : dg A = n24El A 0 := by
  refine Units.ext ?_
  rw [coe_n24El]
  exact dg_eq_blk A

theorem z0_eq_n24El : z₀ = n24El 1 1 := by
  refine Units.ext ?_
  rw [coe_n24El]
  simpa using z0_eq_blk

theorem n24El_comm_z0 (P : GL (Fin 3) (ZMod 2)) (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    n24El P Q * z₀ = z₀ * n24El P Q := by
  rw [z0_eq_n24El, n24El_mul, n24El_mul]
  congr 1 <;> simp [Matrix.mul_one, Matrix.one_mul, add_comm]

theorem n24_blocks_of_comm (g : GL (Fin 6) (ZMod 2)) (h : g * z₀ = z₀ * g) :
    ∃ A B : Matrix (Fin 3) (Fin 3) (ZMod 2),
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = n24Blk A B 0 A := by
  obtain ⟨A, B, C, D, hABCD⟩ := exists_n24Blk (g : Matrix (Fin 6) (Fin 6) (ZMod 2))
  have h1 := congrArg (fun g : GL (Fin 6) (ZMod 2) => (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  simp only [Units.val_mul] at h1
  rw [hABCD, z0_eq_blk, n24Blk_mul, n24Blk_mul] at h1
  obtain ⟨e1, e2, -, e4⟩ := n24Blk_inj h1
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add] at e1 e2 e4
  have hC : C = 0 := (add_right_inj A).mp (by rw [add_zero]; exact e1.symm)
  have hD : A = D := (add_right_inj B).mp (by rw [add_comm B A]; exact e2)
  refine ⟨A, B, ?_⟩
  rw [hABCD, hC, ← hD]

theorem exists_n24El_of_comm (g : GL (Fin 6) (ZMod 2)) (h : g * z₀ = z₀ * g) :
    ∃ (P : GL (Fin 3) (ZMod 2)) (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)), g = n24El P Q := by
  have hinv : g⁻¹ * z₀ = z₀ * g⁻¹ := by
    simpa [mul_assoc] using congrArg (fun x => g⁻¹ * x * g⁻¹) h.symm
  obtain ⟨A, B, hg⟩ := n24_blocks_of_comm g h
  obtain ⟨A', B', hg'⟩ := n24_blocks_of_comm g⁻¹ hinv
  have h1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * ((g⁻¹ : GL (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := Units.mul_inv g
  have h2 : ((g⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := Units.inv_mul g
  rw [hg, hg', n24Blk_mul, ← n24Blk_one] at h1
  rw [hg, hg', n24Blk_mul, ← n24Blk_one] at h2
  obtain ⟨e1, -, -, -⟩ := n24Blk_inj h1
  obtain ⟨e2, -, -, -⟩ := n24Blk_inj h2
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at e1 e2
  refine ⟨⟨A, A', e1, e2⟩, B, Units.ext ?_⟩
  rw [coe_n24El]
  exact hg

end CFSG.OddStandard.HigherRank.YamadaG23
