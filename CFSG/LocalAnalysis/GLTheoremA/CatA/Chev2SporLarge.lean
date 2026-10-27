module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRowsA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23FiveRow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporJ4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Seven

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor
  CFSG.LocalAnalysis.GLTheoremA.Chev2Rows


theorem crow_Fi24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CRow .Fi24Prime 3 := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  have hnc : ∃ a c : ↥J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some
  have hC := centShapeRk_J_good (Good := CTypeThree) ctypeThree_of_equiv
    (fun _ _ _ _ hT => ctypeOK_of_card_eq hb hT) (fun _ _ _ _ hT => ctypeOK_of_card_eq hb hT)
  exact @crow_of_centShape .Fi24Prime 3 ↥J _ hfin hs hOut b hnc Nat.prime_three (by norm_num) _
    (CentShape.of_centShapeRk hC) fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.TabFi24

namespace CFSG.HardMathSupport.Dickson.I271.Fi7

open CFSG.Sporadic.Fi24 (J)
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Chev2Rows


theorem crow_Fi24_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CRow .Fi24Prime 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  refine @crow_of_model .Fi24Prime 7 J _ hfin hs hOut b hnc fun x hx I hI => ?_
  exact ctypeOK_of_card_dvd hb (card_pSimple_dvd_2520 x hx hI) (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)

end CFSG.HardMathSupport.Dickson.I271.Fi7

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block Timmesfeld.Co1Seven
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Chev2Rows


theorem crow_Co1_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : CRow .Co1 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model hbr
  refine @crow_of_model .Co1 7 ↥GA _ hfin hs hOut b hnc fun x hx I hI => ?_
  exact ctypeOK_of_card_dvd hb (card_pSimple_dvd_2520 x hx hI) (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)

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


theorem crow_Co1_five (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.CRow .Co1 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  refine @CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_of_model .Co1 5 ↥GA _ hfin hs hOut b hnc
    fun x hx => ?_
  exact five_good (Good := fun T _ => CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.CTypeOK 5 T)
    (fun _ _ _ _ e h => CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.CTypeOK.of_mulEquiv e h)
    (fun _ _ e => by
      haveI : Finite _ := Nat.finite_of_card_ne_zero (by rw [(J2_facts_of_equiv e).2.1]; norm_num)
      exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.ctypeOK_of_card_eq hb (J2_facts_of_equiv e).2.1)
    (CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.ctypeOK_A5 (Or.inr rfl) (MulEquiv.refl _)) x hx

end CFSG.HardMathSupport.Dickson.I271.TabCo1

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.Multipliers.U43 CFSG.LocalAnalysis.GLTheoremA.Chev2Rows


theorem crow_Co1_three (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : CRow .Co1 3 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  have hC := tabCo1_centShapeRk_three_good (Good := CTypeThree) ctypeThree_of_equiv
    (fun T _ e => by
      have hc : Nat.card T = 3265920 := (Nat.card_congr e.toEquiv).trans card_X₀
      haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
      exact ctypeOK_of_card_eq hb hc)
    (ctypeOK_of_card_eq hb card_alt_nine)
    (fun T _ hc _ => by
      haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
      exact ctypeOK_of_card_eq hb hc) (hbr .Suz)
  exact @crow_of_centShape .Co1 3 ↥GA _ hfin hs hOut b hnc Nat.prime_three (by norm_num) _
    (CentShape.of_centShapeRk hC) fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.TabCo1

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem crow_J4_three (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : CRow .J4 3 := by
  obtain ⟨hfin, hJs, hnc, ⟨b⟩⟩ := CFSG.Sporadic.J4.j4_model hbr
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  refine @crow_of_model .J4 3 J _ hfin hJs hOut b hnc fun x hx I hI => ?_
  obtain ⟨e⟩ := pSimple_of_glaPComponent_three Nat.prime_three hx hI
  haveI : Finite (PSimple 3 I) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_congr e.toEquiv, hM]; norm_num)
  exact ctypeOK_of_card_eq hb ((Nat.card_congr e.toEquiv).trans hM)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem crow_Fi23_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : CRow .Fi23 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi23_model hbr
  refine @crow_of_model .Fi23 5 J _ hfin hs hOut b hnc fun x hx I hI => ?_
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_five hI
  haveI := hsI
  obtain ⟨hd, hle⟩ := card_pSimple_five x hx hI
  intro hC
  rcases chev_card_dvd_241920_cases hb hnab hC hd hle with h | h | ⟨h, -⟩ | ⟨h, -⟩
  · exact (ctypeOK_of_card_eq (p := 5) hb h) hC
  · exact (ctypeOK_of_card_168 (p := 5) hb h) hC
  · exact (ctypeOK_of_card_eq (p := 5) hb h) hC
  · exact (ctypeOK_of_card_eq (p := 5) hb h) hC

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
