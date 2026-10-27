module

public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms

theorem innAutDerived_eq_inner_of_commutative_outer {G : Type*} [Group G]
    (hcomm : ∀ a b : Outer G, a * b = b * a) :
    innAutDerived G = inner G := by
  apply le_antisymm
  · rw [innAutDerived]
    refine sup_le le_rfl ?_
    change ⁅(⊤ : Subgroup (MulAut G)), (⊤ : Subgroup (MulAut G))⁆ ≤ inner G
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff (N := inner G)]
    have h1 : (((⁅a, b⁆ : MulAut G) : MulAut G) : Outer G) =
        (a : Outer G) * (b : Outer G) * (a : Outer G)⁻¹ * (b : Outer G)⁻¹ := by
      rw [commutatorElement_def]
      push_cast
      rfl
    rw [h1]
    rw [hcomm (a : Outer G) (b : Outer G)]
    group
  · exact inner_le_innAutDerived G

end CFSG.LocalAnalysis.GLTheoremA
