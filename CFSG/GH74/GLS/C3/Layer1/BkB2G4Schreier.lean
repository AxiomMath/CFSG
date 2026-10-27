module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Induct
public import CFSG.GH74.Filter.Statements
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public import CFSG.Sporadic.Schreier.PairMcLPairs
public import CFSG.Sporadic.Schreier.LySchreierCase
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

open CFSG CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.SporadicSchreierDispatch CFSG.GH74 CFSG.GH74.Filter

theorem sporadicRep_schreier_g4
    (hout : ∀ s ∈ sporadicOut, S_sporadic s) (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hg : Gen4 S) (hsp : NativeSporadic.SporadicRep S) :
    Group.IsSolvable (Outer S) := by
  obtain ⟨s, he⟩ := hsp
  by_cases hs : s ∈ sporadicOut
  · exact absurd hg (hout s hs S hnonab he)
  · have hM11 := sporadicSchreierCase_M11
    have hM12 := sporadicSchreierCase_M12
    have hM22 := sporadicSchreierCase_M22
    have hM23 := sporadicSchreierCase_M23
    have hJ1 := sporadicSchreierCase_J1
    have hJ2 : SporadicSchreierCase .J2 :=
      sporadicSchreierCase_of_outer Sporadic.Schreier.AT_J2_Schreier.2.2
    have hJ3 : SporadicSchreierCase .J3 :=
      sporadicSchreierCase_of_outer Sporadic.Schreier.AT_J3_Schreier.2
    have hMcL : SporadicSchreierCase .McL :=
      sporadicSchreierCase_of_outer Sporadic.Schreier.AT_McL_Schreier.2
    have hLy := Sporadic.LySchreier.sporadicSchreierCase_Ly
    cases s <;> first
      | exact absurd (by decide) hs
      | exact hM11 S hnonab he
      | exact hM12 S hnonab he
      | exact hM22 S hnonab he
      | exact hM23 S hnonab he
      | exact hJ1 S hnonab he
      | exact hJ2 S hnonab he
      | exact hJ3 S hnonab he
      | exact hMcL S hnonab he
      | exact hLy S hnonab he

theorem schreierG4_of_out
    (hout : ∀ s ∈ sporadicOut, S_sporadic s) : SchreierG4 := by
  intro X _ _ _ hnonab hX
  refine CatalogueSchreierAssembly.catalog_schreier_of_tits_sporadic hnonab (fun p f h => ?_)
    (fun hsp => ?_) hX.1
  · exact (Sporadic.Schreier.Tits.AT_Tits_model_Schreier X p f h).2
  · exact sporadicRep_schreier_g4 hout X hnonab hX.2 hsp

end CFSG.GH74.GLS.C3.Layer1.Bk.B2G4
