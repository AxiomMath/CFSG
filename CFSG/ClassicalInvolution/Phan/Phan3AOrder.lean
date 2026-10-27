module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

theorem card_statedSU_four_three (hK : Nat.card K = 9) :
    Nat.card (StatedSU 4 (3 ^ 1) K) = 13063680 := by
  have h : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, hK.trans (by norm_num)⟩
  have := h.finite
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 4) (Fin 4) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) (by norm_num)).2.1
  have h1 : (Nat.card (StatedSU 4 (3 ^ 1) K) : ℤ) = ((3 ^ 1 : ℕ) : ℤ) ^ (4 * (4 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 4, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [show StatedSU 4 (3 ^ 1) K = unitarySU 3 1 K 4 from rfl, unitarySU_eq_gramSU h,
      card_gramSU, hU]
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 17920 := by decide
  rw [hprod] at h1
  norm_num at h1
  exact_mod_cast h1

theorem isQuasisimple_statedSU_four_three [Finite K] (hK : Nat.card K = 9) :
    CFSG.IsQuasisimple (StatedSU 4 (3 ^ 1) K) :=
  (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 3) (f := 1) (n := 4)
    (hK.trans (by norm_num)) (by norm_num) (by norm_num)).1

theorem card_center_statedSU_four_three [Finite K] (hK : Nat.card K = 9) :
    Nat.card (Subgroup.center (StatedSU 4 (3 ^ 1) K)) = 4 := by
  rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 3) (f := 1) (n := 4)
      (hK.trans (by norm_num)) (by norm_num) (by norm_num)).2,
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_three (hK.trans (by norm_num))
      (n := 4) (by norm_num)).2.2]
  norm_num

end CFSG.ClassicalInvolution.Phan.Q3G
