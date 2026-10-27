module

public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bOrders
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Succ

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank

theorem not_eight_of_alt {G : Type} [Group G] {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (e : G ≃* alternatingGroup (Fin n)) : (Nat.card G).factorization 2 ≠ 8 := by
  intro hv
  have hc : Nat.card G = n.factorial / 2 :=
    (Nat.card_congr e.toEquiv).trans (natCard_alternatingGroup_fin (by omega))
  interval_cases n
  all_goals exact false_of_card_eq_of_factorization hv hc (by decide +kernel)

section Small


theorem not_eight_of_small_lie {G : Type} [Group G]
    (h : LieModel G .PSL 2 2 3 ∨ LieModel G .PSL 2 2 4 ∨ LieModel G .PSL 3 2 2 ∨
      LieModel G .twistedB2 0 2 3) : (Nat.card G).factorization 2 ≠ 8 := by
  intro hv
  rcases h with h | h | h | h
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) h
    exact false_of_card_eq_of_factorization hv hc (by decide +kernel)
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) h
    exact false_of_card_eq_of_factorization hv hc (by decide +kernel)
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) h
    exact false_of_card_eq_of_factorization hv hc (by decide +kernel)
  · have hc := CFSG.GH74.card_of_lieModel_twistedB2 h
    exact false_of_card_eq_of_factorization hv hc (by decide +kernel)

end Small

section Sporadic


theorem card_nativeM23 : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem not_eight_of_sporadic {G : Type} [Group G]
    (h : IsSporadic G .M12 ∨ IsSporadic G .M22 ∨ IsSporadic G .M23 ∨ IsSporadic G .J1 ∨
      IsSporadic G .J2 ∨ IsSporadic G .J3 ∨ IsSporadic G .McL) :
    (Nat.card G).factorization 2 ≠ 8 := by
  intro hv
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact false_of_card_eq_of_factorization hv ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.Mathieu.card_M12 : Nat.card (NativeSporadic.Carrier .M12) = 95040))
      (by decide +kernel)
  · exact false_of_card_eq_of_factorization hv ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.Mathieu.card_M22 : Nat.card (NativeSporadic.Carrier .M22) = 443520))
      (by decide +kernel)
  · exact false_of_card_eq_of_factorization hv ((Nat.card_congr e.toEquiv).trans
      (card_nativeM23 : Nat.card (NativeSporadic.Carrier .M23) = 10200960))
      (by decide +kernel)
  · exact false_of_card_eq_of_factorization hv ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.J1.card_J1 : Nat.card (NativeSporadic.Carrier .J1) = 175560))
      (by decide +kernel)
  · exact false_of_card_eq_of_factorization hv ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.J2.card_J2 : Nat.card (NativeSporadic.Carrier .J2) = 604800))
      (by decide +kernel)
  · exact false_of_card_eq_of_factorization hv ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.J3.card_J3 : Nat.card (NativeSporadic.Carrier .J3) = 50232960))
      (by decide +kernel)
  · exact false_of_card_eq_of_factorization hv ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.McL.card_McL : Nat.card (NativeSporadic.Carrier .McL) = 898128000))
      (by decide +kernel)

end Sporadic

end CFSG.OddStandard.Solomon75
