module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.E2.U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

section Unitary

variable {p f : ℕ} {F : Type} [Field F]

theorem card_unitarySU_int (h : UnitaryFieldData p f F) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card ↥(unitarySU p f F n) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) F)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).2.1
  rw [unitarySU_eq_gramSU h, card_gramSU, hU]

end Unitary

end CFSG.GH74.E2.U5

