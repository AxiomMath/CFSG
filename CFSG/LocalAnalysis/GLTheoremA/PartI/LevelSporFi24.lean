module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporCo
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeE
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeTw
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Classes
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
public import Certificates.Certificate17565
public import Certificates.Certificate17566
public import Certificates.Certificate17567

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.HardMathSupport.Dickson.I271.KDLevelCo3 (LevelTwo levelTwo_of_equiv)
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor

theorem lv_s0 : ShapeRkAt 3 LevelTwo (fun _ _ => True) s0 := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  refine CFSG.HardMathSupport.Dickson.I271.KDLevelFi23.shapeRkAt_levelTwo_of_card shapeRkAt_s0 ?_
  show ¬ 239500800 ∣ Nat.card cent0
  rw [card_cent0]
  norm_num

theorem lv_xJ : ShapeRkAt 3 LevelTwo (fun _ _ => True) xJ := by
  haveI : Finite ↥J := finite_J
  refine CFSG.HardMathSupport.Dickson.I271.KDLevelFi23.shapeRkAt_levelTwo_of_card shapeRkAt_xJ ?_
  show ¬ 239500800 ∣ Nat.card centX
  intro h
  have hpos : 0 < Nat.card centX := Nat.card_pos
  have hle := Nat.le_of_dvd hpos h
  have := card_stab4_le
  rw [card_centX] at hle hpos
  omega

theorem lv_fi24Rep3 (i : Fin 5) : ShapeRkAt 3 LevelTwo (fun _ _ => True) (fi24Rep3 i) := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  fin_cases i
  · obtain ⟨c, hc⟩ := isConj_iff.1 isConj_rep0_s0
    have h := ShapeRkAt.of_equiv Nat.prime_three levelTwo_of_equiv hRk (MulAut.conj c⁻¹) lv_s0
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
    have h := ShapeRkAt.of_equiv Nat.prime_three levelTwo_of_equiv hRk (MulAut.conj c⁻¹) lv_xJ
    have hk : (MulAut.conj c⁻¹) xJ = fi24Rep3 4 := by
      rw [← hc, MulAut.conj_apply]
      show c⁻¹ * (c * wordElt [2] * c⁻¹) * c⁻¹⁻¹ = wordElt [2]
      group
    rw [hk] at h
    exact h

theorem lv_centShapeRk_J : CentShapeRk 3 LevelTwo (fun _ _ => True) ↥J := by
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hkp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hord : orderOf k = 3 := orderOf_eq_prime hkp hk1
  obtain ⟨i, hconj⟩ := Fi24Sylow.fi24ThreeClasses_holds k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := ShapeRkAt.of_equiv Nat.prime_three levelTwo_of_equiv hRk (MulAut.conj c⁻¹)
    (lv_fi24Rep3 i)
  have hk : (MulAut.conj c⁻¹) (fi24Rep3 i) = k := by
    rw [← hc, MulAut.conj_apply]
    group
  rw [hk] at h
  exact h

theorem kdSporRow_Fi24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .Fi24Prime 3 := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  have hnc : ∃ a c : ↥J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some
  exact @kdSporRow_of_centShape .Fi24Prime 3 ↥J _ hfin hs hOut b hnc Nat.prime_three
    (by norm_num) LevelTwo (CentShape.of_centShapeRk lv_centShapeRk_J) fun _ _ h _ => h

end CFSG.HardMathSupport.Dickson.I271.TabFi24

