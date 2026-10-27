module

public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch

public section

namespace CFSG.GH74.GLS.Stage2.Local.GHSch

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.SporadicSchreierDispatch
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem lieModel_outer_solvable
    {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ≠ .twistedF4 ∧ t ≠ .Tits) (h : LieModel X t n p f) :
    Group.IsSolvable (Outer X) := by
  rcases h with ⟨-, h⟩ | ⟨-, ht', h⟩ | ⟨-, ht', h⟩ | ⟨-, -, h⟩
  · exact CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable h
  · exact (CFSG.LieType.Chevalley.exceptional_Chevalley_model_Schreier X t p f ht' h).1
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl | rfl
    · exact (CFSG.LieType.Ree.small_Ree_model_Schreier X p f h).2.1
    · exact absurd rfl ht.1
    · exact absurd rfl ht.2
  · exact (Suzuki_model_Schreier X p f h).2

structure GHSporadicCases : Prop where
  M11 : SporadicSchreierCase .M11
  M12 : SporadicSchreierCase .M12
  M22 : SporadicSchreierCase .M22
  M23 : SporadicSchreierCase .M23
  J1 : SporadicSchreierCase .J1
  J2 : SporadicSchreierCase .J2
  J3 : SporadicSchreierCase .J3
  McL : SporadicSchreierCase .McL
  Ly : SporadicSchreierCase .Ly

theorem ghSchreier_of_sporadic
    (hs : GHSporadicCases) : SchreierFor GHList := by
  intro X _ _ _ hnonab hX
  rcases hX with ⟨n, hn7, -, ⟨e⟩⟩ | hsp | ⟨p, f, -, -, h⟩
  · exact CFSG.ComponentClassification.CatalogueSchreierAlternating.alternating_schreier_of_equiv n
      (by omega) e
  · rcases hsp with h | h | h | h | h | h | h | h | h
    · exact hs.M11 X hnonab h
    · exact hs.M12 X hnonab h
    · exact hs.M22 X hnonab h
    · exact hs.M23 X hnonab h
    · exact hs.J1 X hnonab h
    · exact hs.J2 X hnonab h
    · exact hs.J3 X hnonab h
    · exact hs.McL X hnonab h
    · exact hs.Ly X hnonab h
  · rcases h with ⟨-, h | h | h | h | h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h |
        ⟨-, h | h | h | h | h⟩ <;>
      exact lieModel_outer_solvable (by decide) h

end CFSG.GH74.GLS.Stage2.Local.GHSch
