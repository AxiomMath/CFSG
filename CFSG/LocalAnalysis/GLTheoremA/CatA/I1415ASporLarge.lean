module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRowsA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Five
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Seven

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor
  CFSG.LocalAnalysis.GLTheoremA.I1415Rows


theorem arow_Fi24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1415Row .Fi24Prime 3 := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  have hnc : ∃ a c : ↥J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some
  have hC := centShapeRk_J_good (Good := ATypeThree) atypeThree_of_equiv
    (fun _ _ _ _ hT => atypeOK_of_card_eq hT) (fun _ _ _ _ hT => atypeOK_of_card_eq hT)
  exact @arow_of_centShape .Fi24Prime 3 ↥J _ hfin hs hOut b hnc Nat.prime_three (by norm_num) _
    (CentShape.of_centShapeRk hC) fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.TabFi24

namespace CFSG.HardMathSupport.Dickson.I271.Fi7

open CFSG.Sporadic.Fi24 (J)
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1415Rows


theorem arow_Fi24_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1415Row .Fi24Prime 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  refine @arow_of_model .Fi24Prime 7 J _ hfin hs hOut b hnc fun x hx I hI => ?_
  exact atypeOK_of_card_lt
    ((Nat.le_of_dvd (by norm_num) (card_pSimple_dvd_2520 x hx hI)).trans_lt (by norm_num))

end CFSG.HardMathSupport.Dickson.I271.Fi7

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block Timmesfeld.Co1Seven
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.I1415Rows


theorem arow_Co1_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1415Row .Co1 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model hbr
  refine @arow_of_model .Co1 7 ↥GA _ hfin hs hOut b hnc fun x hx I hI => ?_
  exact atypeOK_of_card_lt
    ((Nat.le_of_dvd (by norm_num) (card_pSimple_dvd_2520 x hx hI)).trans_lt (by norm_num))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA CFSG.Open
  CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4 CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F


theorem arow_Co1_five (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    CFSG.LocalAnalysis.GLTheoremA.I1415Rows.I1415Row .Co1 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  refine @CFSG.LocalAnalysis.GLTheoremA.I1415Rows.arow_of_model .Co1 5 ↥GA _ hfin hs hOut b hnc
    fun x hx => ?_
  exact five_good (Good := fun T _ => CFSG.LocalAnalysis.GLTheoremA.I1415Rows.ATypeOK 5 T)
    (fun _ _ _ _ e h => CFSG.LocalAnalysis.GLTheoremA.I1415Rows.ATypeOK.of_mulEquiv e h)
    (fun _ _ e => CFSG.LocalAnalysis.GLTheoremA.I1415Rows.atypeOK_of_card_eq
      (J2_facts_of_equiv e).2.1)
    (CFSG.LocalAnalysis.GLTheoremA.I1415Rows.atypeOK_A5 (Or.inr rfl) (MulEquiv.refl _)) x hx

end CFSG.HardMathSupport.Dickson.I271.TabCo1
