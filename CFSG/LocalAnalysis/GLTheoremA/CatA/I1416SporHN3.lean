module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder181440
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNThreeShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem not_isChevSimple_two_of_card_181440
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] (hc : Nat.card T = 181440) : ¬ IsChevSimple 2 T := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d => exact Order181440.lieOrderFormula_ne_181440 d.2 ((hb d T ⟨e⟩).symm.trans hc)
    | _ => exact hi.elim
  · cases i with
    | lie d => exact Order181440.lieOrderFormula_ne_181440 d.2 ((hb d T ⟨e⟩).symm.trans hc)
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hcn : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      rw [hc] at hcn
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num [Nat.factorial] at hcn
    | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

namespace CFSG.HardMathSupport.Dickson.I271.I1416HN3

open CFSG.HardMathSupport.Dickson.I271
open CFSG.Open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows
open scoped commutatorElement


set_option maxRecDepth 4000 in
theorem compOK_s1 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CompOK 3 (sJ 0) := by
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
  refine compOK_of_shapeRkAt (Good := fun T _ => TypeOK 3 T) (Rk := fun _ _ => True)
    Nat.prime_three ?_ fun _ _ h => h
  refine shapeRkAt_of_data Nat.prime_three (fun _ _ _ _ e h => TypeOK.of_mulEquiv e h)
    (fun _ _ _ _ _ h => h) (sJ 0) L1J hLC ?_ hsimple hnab h3 hk
    (typeOK_of_not_chev (not_isChevSimple_two_of_card_181440 hb hcard)) trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈ ⁅CJ (sJ 0), CJ (sJ 0)⁆ := Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact L1J.mul_mem h1 hl

theorem compOK_three_JH (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (k : ↥JH)
    (hk3 : orderOf k = 3) : CompOK 3 k := by
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  have hs3 : CompOK 3 (sJ 2) :=
    compOK_of_pConstrained Nat.prime_three (pConstrainedShape_of_hn3bRChecks hn3bR_checks)
  rcases (order_three_classes k).1 hk3 with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    have := CompOK.of_mulEquiv Nat.prime_three (MulAut.conj g) (compOK_s1 hb)
    rw [MulAut.conj_apply, hg] at this
    exact this
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    have := CompOK.of_mulEquiv Nat.prime_three (MulAut.conj g) hs3
    rw [MulAut.conj_apply, hg] at this
    exact this

set_option maxRecDepth 20000 in
theorem row_HN_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416SporRow .HN 3 := by
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
  exact @row_of_model .HN 3 ↥JH _ hfin hs hOut b hnc (compOK_three_JH hb)

end CFSG.HardMathSupport.Dickson.I271.I1416HN3
