module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4UnbChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUAlmostSimple
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Induct

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

open CFSG CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueU CFSG.GH74
  Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedClassicalModel StatedLieTag)

theorem unbalancedG4_of_checks
    (hexc : EvenExceptionalCheckG4) (hree : LargeReeTitsCheckG4) (hspor : SporadicNonJ1CheckG4) :
    UnbalancedG4 := by
  intro X _ _ hg hsimple hnonab hcat hz
  have hF : CFSG.generalizedFitting X = GeneralizedFitting.subgroup X :=
    CFSG.generalizedFitting_eq_componentClassification X
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting X) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := hF ▸ hnonab
  obtain ⟨z, hz2, hcore⟩ := hz
  rcases (Milestones.ct_catalog_nonabelian_type_partition _ hnonab).1 hcat with
    ⟨n, hn, hiso⟩ | hodd | ⟨t, n, f, hadm, hmodel⟩ | hsp
  · rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | h7
    · exact .inl (oddLieType_of_classical (by decide) (by norm_num)
        (LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _
          hiso))
    · exact .inl (oddLieType_of_classical (by decide) (by norm_num)
        (LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
          hiso))
    · obtain ⟨hodd, hmod, -⟩ :=
        AlternatingUnbalanced.alternating_generalized_fitting_unbalanced_degree hnonab h7 hiso
          hz2 hcore
      exact .inr (.inl ⟨n, hodd, h7, hiso, hmod⟩)
  · exact .inl hodd
  · rcases hmodel with ⟨ht, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hrt⟩ | ⟨-, rfl, hsz⟩
    · have hcl' : StatedClassicalModel (CFSG.generalizedFitting X) t n 2 f := hF ▸ hcl
      simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨hlt, hcase, -, -⟩ :=
          UnbalancedCatalog.even_linear_almost_simple_unbalanced_outcome hnonab' hcl'
            ⟨z, hz2, hcore⟩
        rw [hF] at hlt hcase
        rcases hcase with hodd | h322
        · exact .inl hodd
        · exact .inr (.inr ⟨.inl (.inl ⟨by decide, h322⟩), hlt⟩)
      · exact absurd ((UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing hnonab'
          hcl').2 z hz2) hcore
      · exact absurd ((UnbalancedCatalog.even_symplectic_almost_simple_odd_core_vanishing hnonab'
          hcl').1 z hz2) hcore
      · obtain ⟨-, -, -, hp2⟩ := hcl.1
        exact absurd rfl hp2
      · exact absurd ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
          _ (.inl rfl) hcl').2 z hz2) hcore
      · exact absurd ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
          _ (.inr rfl) hcl').2 z hz2) hcore
    · exact hexc X hg hsimple hnonab t f ht hex ⟨z, hz2, hcore⟩
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · obtain ⟨-, -, -, h23, -⟩ := hadm
        exact absurd h23 (by norm_num)
      · exact hree X hg hsimple hnonab _ f (.inl rfl) hrt ⟨z, hz2, hcore⟩
      · exact hree X hg hsimple hnonab _ f (.inr rfl) hrt ⟨z, hz2, hcore⟩
    · have hsz' : SuzukiModel (CFSG.generalizedFitting X) 2 f := hF ▸ hsz
      exact absurd (UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing hsimple' hnonab'
        hsz' z hz2).2.2 hcore
  · by_cases hJ1 : Nonempty (GeneralizedFitting.subgroup X ≃* NativeSporadic.J1)
    · exfalso
      obtain ⟨θ⟩ := hJ1
      let θ' : CFSG.generalizedFitting X ≃* NativeSporadic.J1 :=
        (MulEquiv.subgroupCongr hF).trans θ
      have htop := generalizedFitting_eq_top_of_J1 hsimple' hnonab' θ'
      let eX : X ≃* NativeSporadic.J1 :=
        (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans θ'
      exact hcore (Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨eX⟩ z
        hz2).2.2.2
    · exact hspor X hg hsimple hnonab hsp hJ1 ⟨z, hz2, hcore⟩

end CFSG.GH74.GLS.C3.Layer1.Bk.B2G4
