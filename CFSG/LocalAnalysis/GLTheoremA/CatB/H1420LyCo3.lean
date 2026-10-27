module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Dickson.I271 (co3_centShapeRk)
open CFSG.Sporadic.Schreier.Co3 (co3PermEquiv co3P)


theorem cardRow_mcl_co3 (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hb : LieOrderBridge) (hF : ∀ m : ℕ, m.factorial / 2 ≠ 898128000) :
    K14Spor.CardRow 898128000 .Co3 := by
  have e : NativeSporadic.Carrier .Co3 ≃* ↥co3P := co3PermEquiv
  have hc : Nat.card ↥co3P = 495766656000 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  haveI : IsSimpleGroup ↥co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  refine K14Spor.cardRow_of_centShapeRk (s := .Co3) (Q := ↥co3P) hOut
    (e.symm.trans (hbr .Co3).some)
    (S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num)) co3_centShapeRk ?_
  intro T _ hT hcard
  rcases hT with ⟨hC, -, -⟩ | ⟨n, hn, -, -, ⟨f⟩⟩
  · haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    exact not_isChevSimple_of_card_mcl hb hcard Nat.prime_three hC
  · refine hF n ?_
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega),
      ← Nat.card_congr f.toEquiv]
    exact hcard

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
