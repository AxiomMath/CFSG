module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRowsA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporJ4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.SporAltRows

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem srow_J4_three (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : SRow .J4 3 := by
  obtain ⟨hfin, hJs, hnc, ⟨b⟩⟩ := CFSG.Sporadic.J4.j4_model hbr
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  refine @srow_of_model .J4 3 J _ hfin hJs hOut b hnc fun x hx I hI => ?_
  obtain ⟨e⟩ := pSimple_of_glaPComponent_three Nat.prime_three hx hI
  exact stypeOK_of_card_eq ((Nat.card_congr e.toEquiv).trans hM)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor
  CFSG.LocalAnalysis.GLTheoremA.SporAltRows


theorem srow_Fi24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SRow .Fi24Prime 3 := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  have hnc : ∃ a c : ↥J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some
  have hC := centShapeRk_J_good (Good := STypeThree) stypeThree_of_equiv
    (fun _ _ _ _ hT => stypeOK_of_card_eq hT) (fun _ _ _ _ hT => stypeOK_of_card_eq hT)
  exact @srow_of_centShape .Fi24Prime 3 ↥J _ hfin hs hOut b hnc Nat.prime_three (by norm_num) _
    (CentShape.of_centShapeRk hC) fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.TabFi24
