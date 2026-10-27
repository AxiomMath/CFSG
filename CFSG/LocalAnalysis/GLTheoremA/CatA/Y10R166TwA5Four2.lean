module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwA5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open TwA5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction.UnitaryPilot

theorem hasLabel_unitarySU_six_four {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 2 F) :
    HasLabel (unitarySU 2 2 F 6) (fun l : GLALabel => l = ⟨.twA, 5, 2⟩) := by
  have hq : CFSG.IsQuasisimple (unitarySU 2 2 F 6) :=
    CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_unitarySU h (m := 6)
      (by norm_num) (by norm_num)
  have hZ : Subgroup.center (unitarySU 2 2 F 6) = unitaryScalars h 6 :=
    CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars h 6
  have hSC : StatedClassicalModel
      (unitarySU 2 2 F 6 ⧸ Subgroup.center (unitarySU 2 2 F 6)) .PSU 6 2 2 := by
    refine ⟨?_, F, inferInstance, inferInstance, ?_, ⟨?e⟩⟩
    · refine ⟨Nat.prime_two, by norm_num, ?_⟩
      norm_num
    · rw [h.card]
      norm_num
    · exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
        (unitaryPSUEquiv h (n := 6) (by norm_num))
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_PSU hq hSC

theorem hasLabel_unitarySU_five_four {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 2 F) :
    HasLabel (unitarySU 2 2 F 5) (fun l : GLALabel => l = ⟨.twA, 4, 2⟩) := by
  have hq : CFSG.IsQuasisimple (unitarySU 2 2 F 5) :=
    CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_unitarySU h (m := 5)
      (by norm_num) (by norm_num)
  have hZ : Subgroup.center (unitarySU 2 2 F 5) = unitaryScalars h 5 :=
    CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars h 5
  have hSC : StatedClassicalModel
      (unitarySU 2 2 F 5 ⧸ Subgroup.center (unitarySU 2 2 F 5)) .PSU 5 2 2 := by
    refine ⟨?_, F, inferInstance, inferInstance, ?_, ⟨?e⟩⟩
    · refine ⟨Nat.prime_two, by norm_num, ?_⟩
      norm_num
    · rw [h.card]
      norm_num
    · exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
        (unitaryPSUEquiv h (n := 5) (by norm_num))
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_PSU hq hSC

theorem hasLabel_unitaryBlock_four {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 2 F) :
    HasLabel ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)))
      (fun l : GLALabel => l = ⟨.twA, 4, 2⟩) := by
  have e : unitarySU 2 2 F 5 ≃* unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) :=
    unitaryBlockEquiv h ({0, 1, 2, 3, 4} : Finset (Fin 6))
  exact (hasLabel_congr e (fun l : GLALabel => l = ⟨.twA, 4, 2⟩)).1
    (hasLabel_unitarySU_five_four h)


section Certs


theorem evenRank_unitarySU_six_four {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 2 F) :
    evenRank (unitarySU 2 2 F 6) = 4 := by
  have hlab : Rk2IsLabel (unitarySU 2 2 F 6) ⟨.twA, 5, 2⟩ :=
    hasLabel_unitarySU_six_four h
  have hc : Subgroup.center (unitarySU 2 2 F 6) = ⊥ := by
    rw [CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars h 6,
      unitaryScalars_six_four_eq_bot h]
  refine le_antisymm ?_ ?_
  · have hG : CFSG.Open.GriessAllModelsStatement :=
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    refine CFSG.LocalAnalysis.GLTheoremA.rk2_up_twa5 hlab ⟨rfl, rfl⟩ (by norm_num) hc hG ?_
    intro h9
    norm_num at h9
  · have h := CFSG.LocalAnalysis.GLTheoremA.rk2_low_twa_one (unitarySU 2 2 F 6)
      ⟨.twA, 5, 2⟩ hlab rfl (by norm_num)
    simpa using h

theorem center_eq_bot_of_hasLabel_twA5_two {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hlab : lab = ⟨.twA, 5, 2⟩)
    (hK : HasLabel K (fun l : GLALabel => l = lab)) :
    Subgroup.center K = ⊥ := by
  subst hlab
  obtain ⟨hQ, -, hM⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel (K := K)
      (lab := ⟨.twA, 5, 2⟩) hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 6 2 2 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  have hQ' : CFSG.Open.IsQuasisimple K := ⟨hQ.1.commutator_eq_top, hQ.2.1⟩
  obtain ⟨h3, h5⟩ := CFSG.LocalAnalysis.GLTheoremA.i61_card_center_dvd_psu hQ'
    (n := 2) (by norm_num) hM'
  have h1 : Nat.card (Subgroup.center K) ∣ 1 := by
    have hg : Nat.card (Subgroup.center K) ∣ Nat.gcd 3 5 := Nat.dvd_gcd h3 h5
    simpa using hg
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h1)


end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
