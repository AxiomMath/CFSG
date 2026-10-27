module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.SplusP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Facts3P
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Joint

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel CFSG.EvenSporadicStandard.HNRecog.Harada.S25

section Cert


theorem haradaFactsAll_P {Ep S T T' W0 F : Subgroup ↥P1408} {ι : Elem2 6 →* ↥P1408} {zv : V6}
    (h2 : HaradaFacts2 ↥P1408 Ep pA pZ pB pZ₁ S T T' W0 ι zv (wordSubgroupP nWords1) F)
    (c : Cent3Facts) (hP : Nat.card ↥P1408 = 177408000) (hlift : liftOK = true) :
    HaradaFactsAll ↥P1408 Ep pA pZ pB pZ₁ S T T' W0 ι zv (wordSubgroupP nWords1) F := by
  obtain ⟨ψ, hsurj, hker, -⟩ := exists_hom_centralizer_pZ hP
  exact
    { h2 with
      C_hom := ⟨ψ, hsurj, hker⟩
      three_conj := c.three_conj
      card_C3 := c.card_C3
      odd_normal := c.odd_normal
      card_tT := c.card_tT
      perfect60 := c.perfect60
      W_comm := c.W_comm
      splus := splusFact_P hP hlift }

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
