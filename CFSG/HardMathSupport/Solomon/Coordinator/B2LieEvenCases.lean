module

public import CFSG.HardMathSupport.Solomon.Coordinator.B2LieEvenVanish
public import CFSG.Sporadic.Schreier.LargeReeExcl

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt

open Subgroup CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedClassicalModel StatedLieTag)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.GeneralizedFitting (subgroup)
open CFSG.Sporadic.Schreier.LargeReeExcl (CTU_catalog_large_Ree_Tits_check)
open CFSG.ComponentClassification.UnbalancedGS (catalog_suzuki_almost_simple_odd_core_vanishing)

theorem evenLie_unbalanced_cases
    {X : Type} [Group X] [Finite X] [hs : IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (hE : EvenLieType (CFSG.generalizedFitting X)) {z : X} (hz2 : orderOf z = 2)
    (hne : CFSG.oddCore ↥(centralizer ({z} : Set X)) ≠ ⊥) :
    Nonempty (CFSG.generalizedFitting X ≃* alternatingGroup (Fin 5)) ∨
      StatedClassicalModel (CFSG.generalizedFitting X) .PSL 3 2 1 ∨
      StatedClassicalModel (CFSG.generalizedFitting X) .PSL 3 2 2 := by
  obtain ⟨t, n, f, hadm, hm⟩ := hE
  rcases hm with ⟨ht, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hrt⟩ | ⟨-, rfl, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      rcases Nat.lt_or_ge n 3 with hn | hn
      · have hn2 : 2 ≤ n := hcl.1.2.2.1
        obtain rfl : n = 2 := by omega
        exact .inl ((even_linear_two_almost_simple_unbalanced_outcome hnonab hcl).2.2 z hz2
          hne).2.1
      · obtain ⟨-, -, h3, -⟩ := even_linear_almost_simple_unbalanced_outcome hnonab hcl
          ⟨z, hz2, hne⟩
        rcases h3 hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inr (.inl hcl)
        · exact .inr (.inr hcl)
    · exact absurd ((even_unitary_almost_simple_odd_core_vanishing hnonab hcl).2 z hz2) hne
    · exact absurd ((even_symplectic_almost_simple_odd_core_vanishing hnonab hcl).1 z hz2) hne
    · exact absurd rfl hcl.1.2.2.2
    · exact absurd ((even_orthogonal_almost_simple_odd_core_vanishing hnonab _ (.inl rfl)
        hcl).2 z hz2) hne
    · exact absurd ((even_orthogonal_almost_simple_odd_core_vanishing hnonab _ (.inr rfl)
        hcl).2 z hz2) hne
  · exact absurd (evenExceptional_oddCore_eq_bot hnonab ht hex hz2) hne
  · have hF : CFSG.generalizedFitting X = subgroup X :=
      CFSG.generalizedFitting_eq_componentClassification X
    have hs' : IsSimpleGroup (subgroup X) := hF ▸ hs
    have hnonab' : ∃ a b : subgroup X, a * b ≠ b * a := hF ▸ hnonab
    have hrt' : ReeTitsModel (subgroup X) t 2 f := hF ▸ hrt
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact absurd ⟨z, hz2, hne⟩
        (CTU_catalog_large_Ree_Tits_check X hs' hnonab' _ f (.inl rfl) hrt')
    · exact absurd ⟨z, hz2, hne⟩
        (CTU_catalog_large_Ree_Tits_check X hs' hnonab' _ f (.inr rfl) hrt')
  · exact absurd (catalog_suzuki_almost_simple_odd_core_vanishing hs hnonab hsz z hz2).2.2 hne

end CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt
