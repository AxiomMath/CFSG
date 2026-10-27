module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPODefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem POmegaBlock.pPrimeCore_eq_bot {X : Type} [Group X] [Finite X] (h : POmegaBlock X) :
    pPrimeCore 2 X = ⊥ :=
  pPrimeCore_eq_bot_of_surjective_of_isQuasisimple h.quasisimple h.isPGroup_center
    (MonoidHom.id X) Function.surjective_id

theorem POmegaBlock.fusionZStar_eq {X : Type} [Group X] [Finite X] (h : POmegaBlock X) :
    Open.fusionZStar X = center X :=
  fusionZStar_eq_center_of_pPrimeCore_eq_bot h.pPrimeCore_eq_bot

theorem POmegaBlock.isMTypeSchur (hC4 : POmegaPlusNotLinUnit) {X : Type} [Group X] [Finite X]
    (h : POmegaBlock X) (hev : Even (Nat.card ↥(center X))) : IsMTypeSchur 3 X := by
  have hq : IsQuasisimple (X ⧸ pPrimeCore 2 X) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq h.pPrimeCore_eq_bot.symm)) h.quasisimple
  obtain ⟨n, hn, hm⟩ := h.shape
  have hm' : CFSG.Blueprint.LieModel (X ⧸ Open.fusionZStar X) .POmegaPlus n 3 1 :=
    ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
      (QuotientGroup.quotientMulEquivOfEq h.fusionZStar_eq).symm hm
  refine Or.inl ⟨⟨h.quasisimple.1, hq⟩, ⟨.POmegaPlus, n, 1, hm'⟩, ?_, ?_⟩
  · rw [h.fusionZStar_eq]
    exact hev
  · intro k r _ _ hmk
    obtain ⟨hPSL, hPSU⟩ := hC4 (X ⧸ Open.fusionZStar X) n (2 * k) r hn hm'
    exfalso
    rcases hmk with h1 | h1
    · exact hPSL h1
    · exact hPSU h1

theorem HasPOmegaMember.hasPOmegaClassBMember (hC4 : POmegaPlusNotLinUnit) {L : Type} [Group L]
    [Finite L] (h : HasPOmegaMember L) : HasPOmegaClassBMember L := by
  obtain ⟨J, u, hJ⟩ := h
  have hord : orderOf (⟨⟨u, hJ.mem⟩, hJ.mem_center⟩ : ↥(center ↥J)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hJ.orderOf_eq_two
  have hev : Even (Nat.card ↥(center ↥J)) := by
    have hd := orderOf_dvd_natCard (⟨⟨u, hJ.mem⟩, hJ.mem_center⟩ : ↥(center ↥J))
    rw [hord] at hd
    exact even_iff_two_dvd.mpr hd
  refine ⟨J, u, ⟨hJ.orderOf_eq_two, hJ.mem, hJ.not_mem_center, hJ.block.quasisimple.1,
    hJ.subnormal, hJ.block.isMTypeSchur hC4 hev⟩, ?_⟩
  obtain ⟨n, hn, hm⟩ := hJ.block.shape
  exact ⟨n, hn, ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
    (QuotientGroup.quotientMulEquivOfEq hJ.block.fusionZStar_eq).symm hm⟩

end CFSG.OddStandard.HigherRank.F3
