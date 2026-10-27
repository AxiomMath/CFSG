module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.GH74

open Subgroup CFSG.ShultStronglyClosedTI.InvolutionCounting

theorem thompson_two_involution_class_order_formula {G : Type*} [Group G] [Finite G] {t u : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (htu : ¬ IsConj t u)
    (hcl : ∀ x : G, orderOf x = 2 → IsConj t x ∨ IsConj u x) :
    Nat.card G = Nat.card (centralizer ({u} : Set G)) * thompsonPairCount t u t +
        Nat.card (centralizer ({t} : Set G)) * thompsonPairCount t u u ∧
      ∀ v : G, (v = t ∨ v = u) → ∀ p ∈ thompsonPairs t u v,
        p.1 ∈ centralizer ({v} : Set G) ∧ p.2 ∈ centralizer ({v} : Set G) := by
  refine ⟨card_eq_of_thompsonPairCount_support ht hu htu fun w hw hnt hnu => ?_, ?_⟩
  · rcases hcl w hw with h | h
    · exact absurd h hnt
    · exact absurd h hnu
  · rintro v hv p hp
    have hvv : orderOf v = 2 := by rcases hv with rfl | rfl <;> assumption
    exact mem_centralizer_of_mem_thompsonPairs (mul_self_eq_one_of_orderOf_eq_two ht)
      (mul_self_eq_one_of_orderOf_eq_two hu) (mul_self_eq_one_of_orderOf_eq_two hvv) hp

end CFSG.GH74
