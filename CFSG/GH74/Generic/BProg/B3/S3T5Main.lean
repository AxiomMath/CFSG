module

public import CFSG.GH74.Generic.BProg.B3.S3T5Typ
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.GH74.E2.FactsK

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem tab52w_of_leaves
    {G : Type} [Group G] [Finite G] (hF1 : AltLocBal2)
    (hF2 : L3OuterOddCore) (hF3 : NoTwoA11Obs52 G) : Tab52w G := by
  intro x K A B b D J hyp hnoAlt hc hSD hsrc hext hB4 h
  have h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) := by
    obtain ⟨p, f, hp, hp2, hq, hL | hU⟩ := hSD
    · exact ⟨p, f, hp, hp2, hq, Or.inl hL.1⟩
    · exact ⟨p, f, hp, hp2, hq, Or.inr hU.1⟩
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hext.2.2.2.1
  exact W.type_of_obs52 hF1 hF2
    (genericKnownFacts_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
    E2.e2ComponentFacts hyp hc h3 h hBel (by omega)
    (hF3 x K A B b D J hyp hnoAlt hc hSD hsrc hext hB4 h)

end S3T5

end CFSG.GH74.Generic.BProg.B3
