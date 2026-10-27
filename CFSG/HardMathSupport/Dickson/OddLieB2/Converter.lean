module

public import CFSG.Yardstones.Md42047359a2a.Definitions
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB

public section

namespace CFSG.HardMathSupport.Dickson.OddLieB2

section Helper

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

private theorem commutator_glaPLayer_eq_bot_of_quasisimple {G : Type*} [Group G] [Finite G]
    {p : ℕ} {X : Subgroup G}
    (h : ∀ J : Subgroup G, GLAPComponent p X J → CFSG.IsQuasisimple ↥(J.subgroupOf X)) :
    ⁅GLAPLayer p X, GLAPPrimeCoreOf p X⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sSup_le fun J hJ => ?_
  have hJX : J ≤ X := hJ.1
  have hcomp : IsComponentOf J X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).1
      ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJX).2
        ⟨h J hJ, b3Lie_subnormal_subgroupOf_of_open hJX hJ.2.1⟩)
  obtain ⟨hK, hKN⟩ := glaPComponent_isComponent_of_le_layer hJ (le_sSup hcomp)
  rcases b3Lie_comp_le_or_comm hK (Subgroup.map_subtype_le _) (b3Lie_isSubnormal_core p X) with
    h' | h'
  · exact absurd h' hKN
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h'

end Helper

theorem simpleBp_two_of_fixedTwoComponentsQuasisimple {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (h : CFSG.ComponentClassification.CatLeaf.FixedTwoComponentsQuasisimple S) :
    CFSG.Yardstones.Md42047359a2a.SimpleBp 2 S := by
  intro β hβ
  by_cases hβ1 : β = 1
  · subst hβ1
    exact CFSG.HardMathSupport.Solomon.Coordinator.commutator_glaPLayer_eq_bot_of_perfect_le_layer
      (CFSG.HardMathSupport.Solomon.Coordinator.perfectInLayer_one hnc)
  have hββ : β * β = 1 := by rw [← sq]; exact hβ
  exact commutator_glaPLayer_eq_bot_of_quasisimple fun J hJ =>
    h β hββ hβ1 _
      ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
        Nat.prime_two).1 hJ).2

end CFSG.HardMathSupport.Dickson.OddLieB2
