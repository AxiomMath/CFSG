module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace TwA5Four

theorem unitaryScalars_six_four_eq_bot {F : Type} [Field F] (h : UnitaryFieldData 2 2 F) :
    unitaryScalars h 6 = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rw [card_unitaryScalars h (by norm_num : 1 ≤ 6)]
  norm_num

noncomputable def unitaryPSUEquivUnitarySU {F : Type} [Field F]
    (h : UnitaryFieldData 2 2 F) :
    unitaryPSU h 6 ≃* unitarySU 2 2 F 6 :=
  (QuotientGroup.quotientMulEquivOfEq (unitaryScalars_six_four_eq_bot h)).trans
    (QuotientGroup.quotientBot (G := unitarySU 2 2 F 6))

end TwA5Four

open TwA5Four

theorem exists_mulEquiv_unitarySU_of_hasLabel_twA5_two {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hlab : lab = ⟨.twA, 5, 2⟩)
    (hK : HasLabel K (fun l : GLALabel => l = lab)) (hz : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF : UnitaryFieldData 2 2 F),
      Nonempty (K ≃* unitarySU 2 2 F 6) := by
  subst hlab
  obtain ⟨-, -, hM⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel (K := K)
      (lab := ⟨.twA, 5, 2⟩) hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 6 2 2 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨θ⟩⟩ :=
    hM'.statedClassicalModel (by decide : CFSG.Open.StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hcard : Nat.card F = 2 ^ (2 * 2) := by
    rw [hFcard]
    norm_num
  have hF : UnitaryFieldData 2 2 F := ⟨Nat.prime_two, by norm_num, hcard⟩
  refine ⟨F, hFld, hFin, hF, ?_⟩
  have hbot : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans
      (QuotientGroup.quotientBot (G := K))).symm
  exact ⟨hbot.trans (θ.trans
    ((unitaryPSUEquiv hF (n := 6) (by norm_num)).symm.trans
      (unitaryPSUEquivUnitarySU hF)))⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
