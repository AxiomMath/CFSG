module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRowsA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24D4
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeE
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeTw
public import Certificates.Certificate17565
public import Certificates.Certificate17566
public import Certificates.Certificate17567

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor


section Good

variable {Good : ∀ (T : Type) [Group T], Prop}
  (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
  (hN : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → Nat.card T = 4952179814400 → Good T)
  (hG2 : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → Nat.card T = 4245696 → Good T)

include hGood hN in
theorem shapeRkAt_s0_good : ShapeRkAt 3 Good (fun _ _ => True) s0 := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨hcard, hsimple, hnab, -⟩ := fiN_facts
  haveI : Finite ↥fiN := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine shapeRkAt_of_simple_pindex Nat.prime_three hGood (fun _ _ _ _ _ h => h) fiN
    (fiN_le_lvl_two.trans lvl_two_le_cent0) hsimple hnab (k := 2) ?_ ?_ ?_
    (hN _ hsimple hcard) trivial
  · rw [hcard]
    norm_num
  · rw [card_cent0, hcard]
    norm_num
  · rw [card_cent0]
    decide

include hGood hG2 in
theorem shapeRkAt_xJ_good : ShapeRkAt 3 Good (fun _ _ => True) xJ := by
  haveI : Finite ↥J := finite_J
  have hF := frame_facts
  obtain ⟨-, hsimp, hnab, hcard⟩ := leaf_closure_of_six_some epsJ hF.eps_rel hF.eps_ne
  haveI : Finite ↥(Subgroup.closure (Set.range epsJ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hLS : Subgroup.closure (Set.range epsJ) ≤ stab4 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨h0, h1, hA, hB⟩ := hF.eps_fix i
    exact mem_stab4.2 ⟨mem_lvl_two_of_fix h0 h1, hA, hB⟩
  have hS : Nat.card stab4 = 4245696 :=
    le_antisymm card_stab4_le (hcard ▸ Subgroup.card_le_of_le hLS)
  have hC : Nat.card centX = Nat.card (Subgroup.closure (Set.range epsJ)) * 3 ^ 2 := by
    rw [card_centX, hS, hcard]
    norm_num
  refine shapeRkAt_of_simple_pindex Nat.prime_three hGood (fun _ _ _ _ _ h => h)
    (Subgroup.closure (Set.range epsJ)) (hLS.trans stab4_le_centX) hsimp hnab (k := 2) ?_ hC ?_
    (hG2 _ hsimp hcard) trivial
  · rw [hcard]
    norm_num
  · rw [hC, hcard]
    decide

include hGood hN hG2 in
theorem shapeRkAt_fi24Rep3_good (i : Fin 5) :
    ShapeRkAt 3 Good (fun _ _ => True) (fi24Rep3 i) := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  fin_cases i
  · obtain ⟨c, hc⟩ := isConj_iff.1 isConj_rep0_s0
    have h := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj c⁻¹)
      (shapeRkAt_s0_good hGood hN)
    have hk : (MulAut.conj c⁻¹) s0 = fi24Rep3 0 := by
      rw [← hc, MulAut.conj_apply]
      show c⁻¹ * (c * wordElt [18] * c⁻¹) * c⁻¹⁻¹ = wordElt [18]
      group
    rw [hk] at h
    exact h
  · obtain ⟨-, h1, -, -, -, -⟩ := fi24Three_facts
    exact Or.inl (pConstrainedShape_of_twinFacts h1 bound_base3 Certificates.certificate17566)
  · obtain ⟨-, -, h2, h3, -, -⟩ := fi24Three_facts
    exact Or.inl (pConstrainedShape_of_twinFacts h2 (bound_14069 h3)
      Certificates.certificate17565)
  · obtain ⟨-, -, -, -, h4, -⟩ := fi24Three_facts
    exact Or.inl (pConstrainedShape_of_twinFacts h4 bound_base3 Certificates.certificate17567)
  · obtain ⟨c, hc⟩ := isConj_iff.1 isConj_rep4_xJ
    have h := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj c⁻¹)
      (shapeRkAt_xJ_good hGood hG2)
    have hk : (MulAut.conj c⁻¹) xJ = fi24Rep3 4 := by
      rw [← hc, MulAut.conj_apply]
      show c⁻¹ * (c * wordElt [2] * c⁻¹) * c⁻¹⁻¹ = wordElt [2]
      group
    rw [hk] at h
    exact h

include hGood hN hG2 in
theorem centShapeRk_J_good : CentShapeRk 3 Good (fun _ _ => True) ↥J := by
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hkp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hord : orderOf k = 3 := orderOf_eq_prime hkp hk1
  obtain ⟨i, hconj⟩ := Fi24Sylow.fi24ThreeClasses_holds k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj c⁻¹)
    (shapeRkAt_fi24Rep3_good hGood hN hG2 i)
  have hk : (MulAut.conj c⁻¹) (fi24Rep3 i) = k := by
    rw [← hc, MulAut.conj_apply]
    group
  rw [hk] at h
  exact h

end Good

theorem row_Fi24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416Rows.I1416SporRow .Fi24Prime 3 := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  have hnc : ∃ a c : ↥J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some
  have hC := centShapeRk_J_good (Good := CFSG.LocalAnalysis.GLTheoremA.I1416Rows.TypeThree)
    CFSG.LocalAnalysis.GLTheoremA.I1416Rows.typeThree_of_equiv
    (fun T _ _ _ hT => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.typeOK_of_not_chev
      (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_isChevSimple_two_of_card hb (a := 12)
        (m := 1209028275) (by rw [hT]; norm_num) (by decide) (by norm_num) (by norm_num)))
    (fun T _ _ _ hT => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.typeOK_of_not_chev
      (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_isChevSimple_two_of_card hb (a := 6)
        (m := 66339) (by rw [hT]; norm_num) (by decide) (by norm_num) (by norm_num)))
  exact @CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_of_centShape .Fi24Prime 3 ↥J _ hfin hs hOut
    b hnc Nat.prime_three (by norm_num) _ (CentShape.of_centShapeRk hC) fun _ _ h => h

theorem qrow_Fi24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.I1416QRow .Fi24Prime 3 := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  have hnc : ∃ a c : ↥J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some
  have hC := centShapeRk_J_good (Good := CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QTypeThree)
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeThree_of_equiv
    (fun T _ _ _ hT => CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeOK_of_card hb hT
      (by norm_num) (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)
      (by decide) (by decide))
    (fun T _ _ _ hT => CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeOK_of_card hb hT
      (by norm_num) (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)
      (by decide) (by decide))
  exact @CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qrow_of_centShape .Fi24Prime 3 ↥J _ hfin hs
    hOut b hnc Nat.prime_three (by norm_num) _ (CentShape.of_centShapeRk hC) fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.TabFi24
