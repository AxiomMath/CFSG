module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
public import Certificates.Certificate22242
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Transport

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.L43

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native

theorem card_range_pi : Nat.card pi.range = 6065280 := by
  rw [range_pi, card_closure_pi]

theorem p1ModelFacts_l43 : P1ModelFacts (projectiveSL 4 (ZMod 3)) :=
  Certificates.certificate22242.1

theorem p1ModelFacts_of_lieModel_psl {S : Type} [Group S]
    (h : Blueprint.LieModel S .PSL 4 3 1) : P1ModelFacts S := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hcard, pow_one]
  exact P1ModelFacts.of_mulEquiv (e.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
      (ZMod.ringEquivOfPrime K Nat.prime_three hc).symm)) p1ModelFacts_l43

end CFSG.ComponentClassification.HarrisLit.P1.L43
