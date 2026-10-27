module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.LiftObstruction

public section

namespace CFSG.EvenSporadicStandard.M23Std

open CFSG.EvenSporadicStandard.J4Std.LiftObstruction

@[expose] def liftA1 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 1; 1, 1, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0]

@[expose] def liftA2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 0]

section Certificate

private def Slift : Matrix (Fin 4) (Fin 4) (ZMod 4) :=
  !![0, 0, 1, 1; 1, 1, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0]

private def Tlift : Matrix (Fin 4) (Fin 4) (ZMod 4) :=
  !![0, 0, 0, 1; 0, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 0]

private def cert₁ : Matrix (Fin 4) (Fin 4) (ZMod 4) :=
  !![0, 1, 1, 1; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]

private def cert₂ : Matrix (Fin 4) (Fin 4) (ZMod 4) :=
  !![1, 1, 0, 1; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 0]

private def cert₃ : Matrix (Fin 4) (Fin 4) (ZMod 4) :=
  !![1, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0]

private theorem Slift_map :
    Slift.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = liftA1 := by decide

private theorem Tlift_map :
    Tlift.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = liftA2 := by decide

private theorem dual_X :
    (2 : ZMod 4) • (cert₁ * Slift + Slift * cert₁ +
      Tlift * (cert₃ * (Slift * Tlift) + (Slift * Tlift) * cert₃)) = 0 := by
  decide

private theorem dual_Y :
    (2 : ZMod 4) • (cert₂ * Tlift + Tlift * cert₂ +
      (cert₃ * (Slift * Tlift) + (Slift * Tlift) * cert₃) * Slift) = 0 := by
  decide

private theorem const_two :
    (cert₁ * (Slift * Slift - 1)).trace + (cert₂ * (Tlift * Tlift - 1)).trace +
      (cert₃ * ((Slift * Tlift) * (Slift * Tlift) - 1)).trace = 2 := by
  decide

end Certificate

theorem no_lift4 (A B : Matrix (Fin 4) (Fin 4) (ZMod 4))
    (hA : A.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = liftA1)
    (hB : B.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = liftA2)
    (hAA : A * A = 1) (hBB : B * B = 1) (hABAB : (A * B) * (A * B) = 1) : False := by
  obtain ⟨X, rfl⟩ := exists_eq_add_two_smul A Slift (hA.trans Slift_map.symm)
  obtain ⟨Y, rfl⟩ := exists_eq_add_two_smul B Tlift (hB.trans Tlift_map.symm)
  exact false_of_dual Slift Tlift cert₁ cert₂ cert₃ X Y dual_X dual_Y const_two hAA hBB hABAB

open scoped Matrix in
theorem no_lift4_transpose (A B : Matrix (Fin 4) (Fin 4) (ZMod 4))
    (hA : A.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = liftA1ᵀ)
    (hB : B.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = liftA2ᵀ)
    (hAA : A * A = 1) (hBB : B * B = 1) (hABAB : (A * B) * (A * B) = 1) : False := by
  have hBABA : (B * A) * (B * A) = 1 := by
    calc (B * A) * (B * A) = B * A * (B * A) * (B * B) := by rw [hBB, Matrix.mul_one]
      _ = B * ((A * B) * (A * B)) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hABAB, Matrix.mul_one, hBB]
  refine no_lift4 Aᵀ Bᵀ ?_ ?_ ?_ ?_ ?_
  · rw [Matrix.transpose_map, hA, Matrix.transpose_transpose]
  · rw [Matrix.transpose_map, hB, Matrix.transpose_transpose]
  · rw [← Matrix.transpose_mul, hAA, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hBABA, Matrix.transpose_one]

end CFSG.EvenSporadicStandard.M23Std
