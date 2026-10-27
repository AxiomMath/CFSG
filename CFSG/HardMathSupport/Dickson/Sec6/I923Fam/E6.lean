module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.LiftAut
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Field
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Mult
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartTwo.KFacts

section


theorem y923_e6_holds : Y923_E6 := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain rfl := hF
  haveI : Group.IsPerfect Y := ⟨hq.1⟩
  have hn0 : n = 0 ∧ UntwistedChevalleyModel (Y ⧸ Subgroup.center Y) .E6 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact ⟨hn, hE.2⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨rfl, hU⟩ := hn0
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hψ3 : MulAut.congr θ (centerDescend Y α) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  by_cases hdiag : MulAut.congr θ (centerDescend Y α) ∈ e6Inndiag F
  · exfalso
    apply hnot
    have h1 := e6Inndiag_le_commutator F hdiag
    have hX : LieModel ↥(adjointGroup Tag.E6 F) .E6 0 p f := LieModel.of_mulEquiv θ hm
    have hlift : ∀ β : MulAut (adjointGroup Tag.E6 F), ∃ β' : MulAut Y,
        MulAut.congr θ (centerDescend Y β') = β := fun β =>
      exists_descend_lift hcore θ (not_nine_dvd_hopfMultiplier_e6 hX) β
    exact commutator_le_innAutDerived Y (mem_commutator_of_descend_mem_commutator θ hlift h1)
  · exact noL2_of_descent θ α rfl (noL2Layer_of_not_mem_e6Inndiag
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hadm.1 hadm.2.1 hFcard hψ3
      hdiag) hJ hr

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
