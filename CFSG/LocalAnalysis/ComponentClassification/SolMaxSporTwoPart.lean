module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporBase

public section

namespace CFSG.ComponentClassification.SolMax.SporTwo

open CFSG Subgroup

theorem card_center_dvd_twoPartBound (hCT : EvenSporadicStandard.CentralTwoBound)
    {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q) (hZ : IsPGroup 2 (center Q))
    {s : TauCeti.SporadicName} (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.Carrier s) :
    Nat.card (center Q) ∣ EvenSporadicStandard.twoPartBound s :=
  (hCT Q ⟨Group.isPerfect_def.1 hQ.1, hQ.2.1⟩ hZ s ⟨e⟩).1

end CFSG.ComponentClassification.SolMax.SporTwo

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup

theorem hsj3TwoMultiplierFact_of_centralTwoBound (hCT : EvenSporadicStandard.CentralTwoBound) :
    HSJ3TwoMultiplierFact :=
  ⟨fun _ _ _ hY h2 ⟨e⟩ => Nat.le_of_dvd two_pos
      (SolMax.SporTwo.card_center_dvd_twoPartBound hCT hY h2 (s := .HS) e),
    fun _ _ _ hY h2 ⟨e⟩ => Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp
      (SolMax.SporTwo.card_center_dvd_twoPartBound hCT hY h2 (s := .J3) e))⟩

end CFSG.ComponentClassification.HarrisLit.N36

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup CFSG.Blueprint

theorem rowFor_spor_ONan_of_centralTwoBound (hCT : EvenSporadicStandard.CentralTwoBound) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .ONan := by
  intro G _ _ p w v L K h ⟨e⟩
  exact (h.false_of_noTwoCover fun Y _ _ hY h2 ⟨eY⟩ => Subgroup.eq_bot_of_card_eq _
    (Nat.dvd_one.mp (SolMax.SporTwo.card_center_dvd_twoPartBound hCT hY h2 (eY.trans e)))).elim

end CFSG.ComponentClassification.HarrisLit.L35
