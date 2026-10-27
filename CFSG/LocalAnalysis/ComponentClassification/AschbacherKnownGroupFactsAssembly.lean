module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Core
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsSD

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open

theorem knownGroupFacts_of
    (hsd4 : ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G),
      Open.IsQuasisimple L → HasSemidihedralSylowTwo L → U ≤ Subgroup.normalizer (L : Set G) →
      IsFourGroup U → ∃ u ∈ U, u ≠ 1 ∧ 2 ≤ Open.pRank 2 (L ⊓ Subgroup.centralizer ({u} : Set G)))
    (hsd7 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (a : G),
      Open.IsQuasisimple L → HasSemidihedralSylowTwo L →
      a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
      ∀ P : Sylow 2 ↥(L ⊓ Subgroup.centralizer ({a} : Set G)),
        ¬ (IsCyclic (P : Subgroup ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ∧ Nat.card P = 4)) :
    AschbacherKnownGroupFacts where
  dihedral_cover_generation := FactsL2.dihedral_cover_generation_holds
  small_aut_quaternion := FactsL2.small_aut_quaternion_holds
  dihedral_outer_involution := FactsL2.dihedral_outer_involution_holds
  semidihedral_four_group := hsd4
  semidihedral_dihedral_no_cyclic_four := fun G _ _ L a hL hS ha ha2 P => by
    rcases hS with hD | hSD
    · exact FactsL2.dihedral_no_cyclic_four_holds G L a hL hD ha ha2 P
    · exact hsd7 G L a hL hSD ha ha2 P

theorem knownGroupFacts_holds : AschbacherKnownGroupFacts :=
  knownGroupFacts_of FactsSD.semidihedral_four_group_holds FactsSD.semidihedral_no_cyclic_four_holds

end CFSG.ComponentClassification.AschbacherKnownGroup
