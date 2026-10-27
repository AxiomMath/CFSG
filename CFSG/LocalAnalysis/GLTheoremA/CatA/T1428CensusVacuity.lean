module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusSuzuki
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428InnDerived

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_exists_order_three_innAutDerived {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥)
    (hcomm : ∀ a b : Outer S, a * b = b * a)
    (h3 : ¬ 3 ∣ Nat.card S) :
    ¬ ∃ η : MulAut S, η ∈ innAutDerived S ∧ η ^ 3 = 1 ∧ η ≠ 1 := by
  rintro ⟨η, hη, hη3, hη1⟩
  rw [innAutDerived_eq_inner_of_commutative_outer hcomm] at hη
  exact h3 (three_dvd_card_of_mem_inner_of_pow_three hZ hη hη3 hη1)

end CFSG.LocalAnalysis.GLTheoremA
