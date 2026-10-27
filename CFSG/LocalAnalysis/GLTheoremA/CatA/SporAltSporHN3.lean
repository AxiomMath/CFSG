module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHN3
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.SporAltHN3

open CFSG.HardMathSupport.Dickson.I271
open CFSG.Open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.SporAltRows
open scoped commutatorElement


set_option maxRecDepth 4000 in
theorem compGood_s1 :
    CFSG.HardMathSupport.Dickson.I271.TabCo1.CompGood (Good := fun T _ => Nat.card T = 181440) 3
      (sJ 0) := by
  obtain ⟨-, -, hcomm⟩ := CJ_s1_structure
  have hder := commutator_CJ_s1
  haveI hsimple : IsSimpleGroup ↥L1J := by
    have := alt3_simple
    exact MulEquiv.isSimpleGroup (alt3.equivMapOfInjective iotaA iotaA_injective).symm
  have hcard : Nat.card ↥L1J = 181440 := by
    rw [show (L1J : Subgroup JH) = alt3.map iotaA from rfl,
      Subgroup.card_map_of_injective iotaA_injective, card_alt3]
  haveI : Finite ↥L1J := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hLC : L1J ≤ Subgroup.centralizer ({sJ 0} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)
  have hnp : ¬ (Nat.card ↥L1J).Prime := by
    rw [hcard]
    norm_num
  have hnab : ∃ a b : ↥L1J, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥L1J) hnp
  have h3 : 3 ∣ Nat.card ↥L1J := by
    rw [hcard]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({sJ 0} : Set ↥JH)) = Nat.card ↥L1J * 3 ^ 1 := by
    rw [show Subgroup.centralizer ({sJ 0} : Set ↥JH) = CJ (sJ 0) from rfl, card_CJ_s1, hcard]
    norm_num
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  refine compGood_of_shapeRkAt (Rk := fun _ _ => True) Nat.prime_three ?_
  refine shapeRkAt_of_data Nat.prime_three
    (fun _ _ _ _ e h => (Nat.card_congr e.toEquiv).symm.trans h)
    (fun _ _ _ _ _ h => h) (sJ 0) L1J hLC ?_ hsimple hnab h3 hk hcard trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈ ⁅CJ (sJ 0), CJ (sJ 0)⁆ := Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact L1J.mul_mem h1 hl

theorem compGood_three_JH (k : ↥JH) (hk3 : orderOf k = 3) :
    CFSG.HardMathSupport.Dickson.I271.TabCo1.CompGood (Good := fun T _ => Nat.card T = 181440) 3
      k := by
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  have hs3 : CFSG.HardMathSupport.Dickson.I271.TabCo1.CompGood
      (Good := fun T _ => Nat.card T = 181440) 3 (sJ 2) := fun I hI =>
    (CFSG.LocalAnalysis.GLTheoremA.KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three
      (pConstrainedShape_of_hn3bRChecks hn3bR_checks) hI).elim
  rcases (order_three_classes k).1 hk3 with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    have := CFSG.HardMathSupport.Dickson.I271.TabCo1.CompGood.of_mulEquiv
      (fun _ _ _ _ e h => (Nat.card_congr e.toEquiv).symm.trans h) Nat.prime_three (MulAut.conj g)
      compGood_s1
    rw [MulAut.conj_apply, hg] at this
    exact this
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    have := CFSG.HardMathSupport.Dickson.I271.TabCo1.CompGood.of_mulEquiv
      (fun _ _ _ _ e h => (Nat.card_congr e.toEquiv).symm.trans h) Nat.prime_three (MulAut.conj g) hs3
    rw [MulAut.conj_apply, hg] at this
    exact this

set_option maxRecDepth 20000 in
theorem grow_HN_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    GRow (fun T _ => Nat.card T = 181440) .HN 3 := by
  have hfin : Finite ↥JH := by
    have : Nat.card ↥JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  have e : CFSG.Blueprint.NativeSporadic.HN ≃* ↥JH := CFSG.Sporadic.HNSchreier.hnEquivJ
  have hs : IsSimpleGroup ↥JH :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HNSchreier.fam_hn_certified_simplicity.2 e.symm
  have hpr : ¬ (Nat.card ↥JH).Prime := by rw [card_JH]; norm_num
  have hnc : ∃ a c : ↥JH, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥JH _ hfin hs hpr
  have b : ↥JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := e.symm.trans (hbr .HN).some
  exact @grow_of_model (fun T _ => Nat.card T = 181440)
    (fun _ _ _ _ e h => (Nat.card_congr e.toEquiv).symm.trans h) .HN 3 ↥JH _ hfin hs hOut b hnc
    compGood_three_JH

end CFSG.HardMathSupport.Dickson.I271.SporAltHN3
