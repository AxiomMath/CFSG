module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossArith
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

section Card

variable {p f : ℕ} {K : Type} [Field K]

theorem card_unitarySU_three (h : UnitaryFieldData p f K) :
    Nat.card (unitarySU p f K 3) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  have := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [unitarySU_eq_gramSU h, card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
    ring
  rw [hprod] at hSU
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq2]
  rw [hSU]
  norm_num
  ring

theorem card_statedProj_su3 (h : UnitaryFieldData p f K) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) = psu3Order (p ^ f) := by
  have := h.finite
  have hZ : Nat.card (unitaryScalars h 3) = Nat.gcd 3 (p ^ f + 1) := card_unitaryScalars h (by norm_num)
  have hSZ : Nat.card (unitarySU p f K 3) = Nat.card (unitaryPSU h 3) * Nat.gcd 3 (p ^ f + 1) := by
    rw [← hZ]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hP : Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) = Nat.card (unitaryPSU h 3) :=
    (Nat.card_congr (unitaryPSUEquiv h (by norm_num)).toEquiv).symm
  rw [hP, psu3Order, ← card_unitarySU_three h, hSZ]
  have hg : 0 < Nat.gcd 3 (p ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  exact (Nat.mul_div_cancel _ hg).symm

end Card

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
