module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Data

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section

variable {S : Type} [Group S] {σ : MulAut S} {J : Subgroup ↥(fixedSubgroup σ)}

private theorem card_alternatingGroup_fin_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem Z2S6ModData.card_quotient_J (hdata : Z2S6ModData S σ J) :
    Nat.card (↥J ⧸ fusionOddCore ↥J) = 360 := by
  obtain ⟨e⟩ := hdata.iso
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_six]

theorem Z2S6ModData.dvd_card_J (hdata : Z2S6ModData S σ J) : 360 ∣ Nat.card ↥J := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (fusionOddCore ↥J),
    hdata.card_quotient_J]
  exact Dvd.intro _ rfl

theorem Z2S6ModData.not_two_pow_six_J (hdata : Z2S6ModData S σ J) :
    ¬ 2 ^ 6 ∣ Nat.card ↥J := fun h =>
  hdata.not_two_pow_six (h.trans (Subgroup.card_subgroup_dvd_card J))

theorem Z2S6ModData.zStar_eq_oddCore_J (hdata : Z2S6ModData S σ J) :
    fusionZStar ↥J = fusionOddCore ↥J := by
  obtain ⟨e⟩ := hdata.iso
  have hc : Subgroup.center (↥J ⧸ fusionOddCore ↥J) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hz : e w ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨v, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw v]
    rw [alternatingGroup.center_eq_bot (α := Fin 6) (by simp), Subgroup.mem_bot,
      MulEquiv.map_eq_one_iff] at hz
    exact hz
  unfold fusionZStar
  rw [hc, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem Z2S6ModData.card_zStar_J (hdata : Z2S6ModData S σ J) :
    Nat.card (↥J ⧸ fusionZStar ↥J) = 360 := by
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hdata.zStar_eq_oddCore_J).toEquiv,
    hdata.card_quotient_J]

end

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
