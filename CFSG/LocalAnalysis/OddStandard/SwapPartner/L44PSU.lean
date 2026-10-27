module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

private theorem card_unitarySU_four_aux {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) :
    Nat.card (unitarySU p f K 4) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
  have := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 4) (Fin 4) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 4) (Fin 4) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [unitarySU_eq_gramSU h, card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1) := by
    rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num
    ring
  rw [hprod] at hSU
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have hq4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  zify [hq2, hq4]
  rw [hSU]
  norm_num
  ring

theorem card_unitaryPSU_four_two {K : Type} [Field K] {a : ℕ} (ha : a = 1)
    (h : UnitaryFieldData 2 a K) : Nat.card (unitaryPSU h 4) = 25920 := by
  subst ha
  have := h.finite
  have hZ : Nat.card (unitaryScalars h 4) = Nat.gcd 4 (2 ^ 1 + 1) :=
    card_unitaryScalars h (by norm_num)
  have hSZ : Nat.card (unitarySU 2 1 K 4) =
      Nat.card (unitaryPSU h 4) * Nat.gcd 4 (2 ^ 1 + 1) := by
    rw [← hZ]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_unitarySU_four_aux h] at hSZ
  norm_num at hSZ
  exact hSZ.symm

end CFSG.OddStandard.AltStdSec.SwapPartner
