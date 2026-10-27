module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Assembly

open CFSG.Blueprint

theorem largeEvenSzD_eq (a : ℕ) {K : Type} [Field K] (l : Kˣ) :
    Matrix.diagonal ![(l : K) ^ (1 + 2 ^ a), (l : K) ^ 2 ^ a, ((l⁻¹ : Kˣ) : K) ^ 2 ^ a,
      ((l⁻¹ : Kˣ) : K) ^ (1 + 2 ^ a)] = suzukiD a l := by
  have e1 : l ^ (1 + (2 ^ a : ℤ)) = l ^ (1 + 2 ^ a) := by
    rw [show (1 + (2 ^ a : ℤ)) = ((1 + 2 ^ a : ℕ) : ℤ) by simp]
    exact zpow_natCast l _
  have e2 : l ^ (2 ^ a : ℤ) = l ^ (2 ^ a) := by
    rw [show (2 ^ a : ℤ) = ((2 ^ a : ℕ) : ℤ) by simp]
    exact zpow_natCast l _
  have e3 : l ^ (-(2 ^ a : ℤ)) = l⁻¹ ^ (2 ^ a) := by
    rw [show (-(2 ^ a : ℤ)) = -((2 ^ a : ℕ) : ℤ) by simp, zpow_neg, zpow_natCast, inv_pow]
  have e4 : l ^ (-1 - (2 ^ a : ℤ)) = l⁻¹ ^ (1 + 2 ^ a) := by
    rw [show (-1 - (2 ^ a : ℤ)) = -((1 + 2 ^ a : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, inv_pow]
  unfold suzukiD
  rw [e1, e2, e3, e4]
  simp only [Units.val_pow_eq_pow_val]

theorem largeEvenSzW_eq {K : Type} [Field K] :
    (!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) K) =
      suzukiW K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW]

theorem largeEvenSzGroup_eq_suzukiGroup (a : ℕ) (K : Type) [Field K] :
    LargeEvenSzGroup a K = suzukiGroup a K := by
  unfold LargeEvenSzGroup suzukiGroup LargeEvenSzGens
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, largeEvenSzD_eq, largeEvenSzW_eq]
  rfl

end CFSG.Assembly
