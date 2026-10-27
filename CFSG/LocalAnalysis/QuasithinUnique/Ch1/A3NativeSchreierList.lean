module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.PairHSPairs

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase)

theorem sporadicSchreierCase_J2 :
    SporadicSchreierCase .J2 :=
  SporadicSchreierDispatch.sporadicSchreierCase_of_outer
    CFSG.ComponentClassification.J2Cover.at_j2_schreier.2.2

theorem sporadicSchreierCase_HS
    : SporadicSchreierCase .HS :=
  SporadicSchreierDispatch.sporadicSchreierCase_of_outer
    CFSG.Sporadic.Schreier.AT_HS_Schreier.2

theorem schreier_simple_of_cases
    (hJ4 : SporadicSchreierCase .J4) (hHe : SporadicSchreierCase .He)
    (hRu : SporadicSchreierCase .Ru) (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hlist : A23ListCat S) :
    Group.IsSolvable (Outer S) := by
  have hexc : ExceptionalRep S → Group.IsSolvable (Outer S) := fun h =>
    CatalogueSchreierAssembly.exceptional_rep_outer_solvable
      (fun p f hm => (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S p f hm).2) h
  rcases hlist with ⟨n, hn5, -, ⟨e⟩⟩ | ⟨p, -, -, hcl⟩ | ⟨⟨f, hf⟩ | hT⟩ | ⟨n, -, hm⟩ |
      ⟨s, hs, ⟨e⟩⟩
  · exact CatalogueSchreierAlternating.alternating_schreier_of_equiv n hn5 e
  · rcases hcl with ⟨f, -, hm⟩ | hm | hm <;>
      exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
  · rcases hf with ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩ |
        ⟨-, -, hm⟩
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact hexc (Or.inl ⟨.G2, 2, f, by simp [chevalleyExceptionalTags], hm⟩)
    · exact hexc (Or.inl ⟨.trialityD4, 2, f, by simp [chevalleyExceptionalTags], hm⟩)
    · exact hexc (Or.inr (Or.inl ⟨.twistedF4, 2, f, by simp [reeTitsTags], hm⟩))
    · exact hexc (Or.inr (Or.inr ⟨2, f, hm⟩))
  · exact (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 hT).2
  · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact SporadicSchreierDispatch.sporadicSchreierCase_M11 S hnonab ⟨e⟩
    · exact SporadicSchreierDispatch.sporadicSchreierCase_M12 S hnonab ⟨e⟩
    · exact SporadicSchreierDispatch.sporadicSchreierCase_M22 S hnonab ⟨e⟩
    · exact SporadicSchreierDispatch.sporadicSchreierCase_M23 S hnonab ⟨e⟩
    · exact SporadicSchreierDispatch.sporadicSchreierCase_M24 S hnonab ⟨e⟩
    · exact SporadicSchreierDispatch.sporadicSchreierCase_J1 S hnonab ⟨e⟩
    · exact sporadicSchreierCase_J2 S hnonab ⟨e⟩
    · exact hJ4 S hnonab ⟨e⟩
    · exact sporadicSchreierCase_HS S hnonab ⟨e⟩
    · exact hHe S hnonab ⟨e⟩
    · exact hRu S hnonab ⟨e⟩

theorem schreierFactListCat_of_cases
    (hJ4 : SporadicSchreierCase .J4) (hHe : SporadicSchreierCase .He)
    (hRu : SporadicSchreierCase .Ru) : SchreierFactListCat :=
  schreierFactListCat_of_simple fun S _ _ _ hnonab hlist =>
    schreier_simple_of_cases hJ4 hHe hRu S hnonab hlist

end CFSG.QuasithinUnique.Vol2Native
