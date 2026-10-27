module

public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBShell
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.Co3Schreier
public import CFSG.Sporadic.Schreier.RuModel
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.ONSchreier

public section

namespace CFSG.ComponentClassification.CatalogSchreierCases

open CFSG.Blueprint
open CFSG.ComponentClassification.SporadicSchreierDispatch
open LocalAnalysis.ComponentInitial (SchreierFor)

theorem sporadicSchreierCase_J2 : SporadicSchreierCase .J2 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.AT_J2_Schreier.2.2

theorem sporadicSchreierCase_J3 : SporadicSchreierCase .J3 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.AT_J3_Schreier.2

theorem sporadicSchreierCase_HS : SporadicSchreierCase .HS :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.AT_HS_Schreier.2

theorem sporadicSchreierCase_ON : SporadicSchreierCase .ONan :=
  sporadicSchreierCase_of_outer ONSchreier.at_on_schreier

theorem sporadicSchreierCase_Co3 : SporadicSchreierCase .Co3 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.Co3.AT_Co3_Schreier

theorem sporadicSchreierCase_Ru : SporadicSchreierCase .Ru :=
  sporadicSchreierCase_of_outer Sporadic.RuSchreier.AT_Ru_model_Schreier.{0}.1

theorem tits_model_outer_solvable (S : Type) [Group S] (p f : ℕ)
    (h : ReeTitsModel S .Tits p f) : Group.IsSolvable (OuterAutomorphisms.Outer S) :=
  (Sporadic.Schreier.Tits.AT_Tits_model_Schreier S p f h).2

theorem catalogSchreier_of_remaining (hJ4 : SporadicSchreierCase .J4)
    (hCo1 : SporadicSchreierCase .Co1) (hCo2 : SporadicSchreierCase .Co2)
    (hFi22 : SporadicSchreierCase .Fi22) (hFi23 : SporadicSchreierCase .Fi23)
    (hFi24 : SporadicSchreierCase .Fi24Prime) (hMcL : SporadicSchreierCase .McL)
    (hHe : SporadicSchreierCase .He) (hSuz : SporadicSchreierCase .Suz)
    (hHN : SporadicSchreierCase .HN) (hLy : SporadicSchreierCase .Ly)
    (hTh : SporadicSchreierCase .Th) (hB : SporadicSchreierCase .B)
    (hM : SporadicSchreierCase .M) : SchreierFor Catalog :=
  KProperRelativeB.catalogueSchreier_of_native tits_model_outer_solvable
    fun S _ _ _ hnonab hS => sporadicRep_schreier_of_remaining sporadicSchreierCase_J2
      sporadicSchreierCase_J3 hJ4 hCo1 hCo2 sporadicSchreierCase_Co3 hFi22 hFi23 hFi24
      sporadicSchreierCase_HS hMcL hHe sporadicSchreierCase_Ru hSuz sporadicSchreierCase_ON hHN
      hLy hTh hB hM S hnonab hS

end CFSG.ComponentClassification.CatalogSchreierCases
