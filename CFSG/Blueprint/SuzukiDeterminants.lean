module

public import CFSG.Blueprint.CatalogGenerators

public section

namespace CFSG.Blueprint

variable {K : Type} [Field K]

theorem suzukiW_eq_permMatrix :
    suzukiW K = (Fin.revPerm : Equiv.Perm (Fin 4)).permMatrix K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, Equiv.Perm.permMatrix, PEquiv.toMatrix]

theorem det_suzukiW_eq_one : (suzukiW K).det = 1 := by
  rw [suzukiW_eq_permMatrix, Matrix.det_permutation]
  have h : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin 4)) = 1 := by decide
  rw [h]
  simp

theorem suzuki_generator_determinants (a : ℕ) (K : Type) [Field K] [Finite K]
    (_hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ u v : K, (suzukiS a u v).det = 1) ∧ (∀ l : Kˣ, (suzukiD a l).det = 1) ∧
    (suzukiW K).det = 1 ∧
    (∀ u v : K, ∃ g : Matrix.SpecialLinearGroup (Fin 4) K,
      (g : Matrix (Fin 4) (Fin 4) K) = suzukiS a u v) ∧
    (∀ l : Kˣ, ∃ g : Matrix.SpecialLinearGroup (Fin 4) K,
      (g : Matrix (Fin 4) (Fin 4) K) = suzukiD a l) ∧
    ∃ g : Matrix.SpecialLinearGroup (Fin 4) K, (g : Matrix (Fin 4) (Fin 4) K) = suzukiW K :=
  ⟨det_suzukiS a, det_suzukiD a, det_suzukiW_eq_one,
    fun u v => ⟨⟨suzukiS a u v, det_suzukiS a u v⟩, rfl⟩,
    fun l => ⟨⟨suzukiD a l, det_suzukiD a l⟩, rfl⟩, ⟨⟨suzukiW K, det_suzukiW_eq_one⟩, rfl⟩⟩

end CFSG.Blueprint
