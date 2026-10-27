module

public import CFSG.Timmesfeld.Final.Simple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.LargeExtraspecial.S8CorBStatement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem outer_solvable_of_lieModel_of_not_ree {Y : Type} [Group Y] {t : StatedLieTag}
    {n p f : ℕ} (ht : t ∉ reeTitsTags) (h : LieModel Y t n p f) : Group.IsSolvable (Outer Y) := by
  rcases h with ⟨-, hcl⟩ | ⟨-, ht', hm⟩ | ⟨-, ht', -⟩ | ⟨-, -, hm⟩
  · exact ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable hcl
  · exact (LieType.Chevalley.exceptional_Chevalley_model_Schreier Y t p f ht' hm).1
  · exact absurd ht' ht
  · exact (LocalAnalysis.ComponentInitial.Suzuki_model_Schreier Y p f hm).2

theorem outer_solvable_of_corBList {Y : Type} [Group Y] (h : CorBList Y) :
    Group.IsSolvable (Outer Y) := by
  rcases h with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | ⟨f, h⟩ | h | h
  iterate 7 exact outer_solvable_of_lieModel_of_not_ree (by simp [reeTitsTags]) h
  · obtain ⟨e⟩ := h
    exact ComponentClassification.CatalogueSchreierAlternating.alternating_schreier_of_equiv 6
      (by norm_num) e
  · obtain ⟨e⟩ := h
    exact (LocalAnalysis.ComponentInitial.outer_isomorphism e).2.2
      Sporadic.Schreier.AT_J2_Schreier.2.2

theorem isSimpleGroup_of_corBList {Y : Type} [Group Y] (h : CorBList Y) : IsSimpleGroup Y := by
  rcases h with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | ⟨f, h⟩ | h | h
  iterate 7 exact Timmesfeld.isSimpleGroup_of_lieModel h
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (NativeSporadic.Carrier .J2) := Sporadic.J2.isSimpleGroup_J2
    exact e.isSimpleGroup

end CFSG.LargeExtraspecial.S8
