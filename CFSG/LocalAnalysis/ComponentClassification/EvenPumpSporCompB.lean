module

public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuter
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG.ComponentClassification.SolMax
open CFSG Subgroup CFSG.Blueprint

theorem evenPumpSpor_Ly :
    EvenPumpSporClauseFor .Ly :=
  evenPumpSporClauseFor_of_comps Sporadic.LySchreier.sporadicOddCoreFree_Ly
    (fun G _ _ _ _ hG t ht => by
      obtain ⟨hq, hZ, -⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple hG t ht
      refine compsSatisfy_noEvenAltBelow_of_quasisimple hq fun h => ?_
      rw [h, Subgroup.card_bot] at hZ
      omega)
    (outer_noEvenAlt_of_forall_inner fun α => by
      have h : OuterAutomorphisms.inner (NativeSporadic.Carrier .Ly) = ⊤ :=
        RestrictedStd.Spor.lyOuterTrivialInput
      rw [h]
      trivial)

theorem evenPumpSpor_Th :
    EvenPumpSporClauseFor .Th :=
  evenPumpSporClauseFor_of_comps Sporadic.ThSchreier.sporadicOddCoreFree_Th
    (fun G _ _ _ _ hG t ht => RestrictedStd.Spor.compsSatisfy_of_charP
      ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G
        hG).1 t ht).1 _)
    (outer_noEvenAlt_of_forall_inner fun α => by
      have h : OuterAutomorphisms.inner (NativeSporadic.Carrier .Th) = ⊤ :=
        Sporadic.ThSchreier.inner_Th
      rw [h]
      trivial)

theorem evenPumpSpor_J4 :
    EvenPumpSporClauseFor .J4 :=
  evenPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_J4
    (fun G _ _ _ _ hG t ht B hB =>
      absurd hB (RestrictedStd.Spor.j4NoComponentsInput G hG t ht B))
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => by
      by_cases h1 : α = 1
      · exact absurd ⟨1, by rw [h1, map_one]⟩ hα
      · exact absurd (RestrictedStd.Spor.mem_inner_of_J4 e α
          (orderOf_eq_prime (by rw [sq]; exact hα2) h1)) hα)

end CFSG.ComponentClassification.EvenPump
