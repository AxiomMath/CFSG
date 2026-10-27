module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.KDNPForms
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.A5Aut
public import CFSG.GroupTheory.SmallFixedTwoGroup.TheoremP
public import CFSG.GroupTheory.SmallFixedTwoGroup.Displacement

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.Co3Std.CentT (centerQuotAut)

theorem kdnpSmall_holds : KDNPSmall := by
  intro E _ _ hq _hZ σ hσ _h2 h4
  haveI : IsSimpleGroup (E ⧸ center E) := hq.2.1
  obtain ⟨hcomm, _hne, hdvd⟩ :=
    CFSG.GroupTheory.SmallFixedTwoGroup.displacement_of_isQuasisimple hq hσ
  have hle : Nat.card (fixedSubgroup (centerQuotAut σ)) ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans h4
  obtain ⟨e⟩ :=
    CFSG.GroupTheory.SmallFixedTwoGroup.nonempty_mulEquiv_alt5_of_fixed_card_le_four
      hq.2.2 (centerQuotAut σ) hcomm hle
  have hα : ∀ h, centerQuotAut σ (centerQuotAut σ h) = h := by
    intro h
    have := congrArg (fun f : MulAut (E ⧸ center E) => f h) hcomm
    simpa [MulAut.mul_apply] using this
  have hFixb : Nat.card (fixedSubgroup (centerQuotAut σ)) = 4 := by
    rcases CFSG.EvenSporadicStandard.M12Std.PropA.card_fixedPoints_of_alt5 e
        (centerQuotAut σ) hα with h | h | h
    · simpa [fixedSubgroup] using h
    · exfalso
      have h6 : Nat.card (fixedSubgroup (centerQuotAut σ)) = 6 := by
        simpa [fixedSubgroup] using h
      omega
    · exfalso
      have h60 : Nat.card (fixedSubgroup (centerQuotAut σ)) = 60 := by
        simpa [fixedSubgroup] using h
      omega
  refine ⟨⟨e⟩, ?_⟩
  have hdvd4 : 4 ∣ Nat.card (fixedSubgroup σ) := by rwa [hFixb] at hdvd
  have hge : 4 ≤ Nat.card (fixedSubgroup σ) := Nat.le_of_dvd Nat.card_pos hdvd4
  omega

end CFSG.EvenSporadicStandard.M12Std.Rbc
