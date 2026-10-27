module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.J3Surj

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup

theorem hsj3TwoMultiplierFact_of_sporadicMultipliers
    (h : RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : HSJ3TwoMultiplierFact := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun Y _ _ hY _ ⟨e⟩ => ?_, fun Y _ _ hY h2 ⟨e⟩ => ?_⟩
  · obtain ⟨b⟩ := Sporadic.Bridge.HS.nonempty_mulEquiv
    have b' : Blueprint.NativeSporadic.HS ≃* RankThree.PartTwo.Sec4.Spor .HS := b
    have hd := GH74.Generic.card_center_dvd_hopfMultiplier hY (e.trans b')
    rw [h.1 .HS, show RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder .HS = 2 from rfl]
      at hd
    exact Nat.le_of_dvd (by norm_num) hd
  · obtain ⟨b⟩ := Sporadic.Bridge.J3.nonempty_mulEquiv
    have b' : Blueprint.NativeSporadic.J3 ≃* RankThree.PartTwo.Sec4.Spor .J3 := b
    have hd := GH74.Generic.card_center_dvd_hopfMultiplier hY (e.trans b')
    rw [h.1 .J3, show RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder .J3 = 3 from rfl]
      at hd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hk] at hd
    have hk0 : k = 0 := by
      by_contra hne
      have h23 : 2 ∣ 3 := (dvd_pow_self 2 hne).trans hd
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk

end CFSG.ComponentClassification.HarrisLit.N36
