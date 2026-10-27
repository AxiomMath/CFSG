module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.I1415AHN

open CFSG.HardMathSupport.Dickson.I271
open CFSG.Open CFSG.Blueprint CFSG.Sporadic.HNSchreier
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.I1415Rows
open scoped commutatorElement


theorem acompOK_f (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    ACompOK 5 fJ := by
  obtain ⟨hcomm, -, -, -, hC, hcardI, -, hder, -⟩ := CFSG.Sporadic.HNOddCore.ctuc_hn_five_centralizer_perfect_factor
  haveI hsimple : IsSimpleGroup ↥IJ :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity IJ 3 5 1 CFSG.RankThree.PartOne.HNB.model_IJ).2
  haveI : Finite ↥IJ := Nat.finite_of_card_ne_zero (by rw [hcardI]; norm_num)
  have hLC : IJ ≤ Subgroup.centralizer ({fJ} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm fJ (Subgroup.mem_zpowers _) x hx).symm
  have hnp : ¬ (Nat.card ↥IJ).Prime := by
    rw [hcardI]
    norm_num
  have hnab : ∃ a b : ↥IJ, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥IJ) hnp
  have h5 : 5 ∣ Nat.card ↥IJ := by
    rw [hcardI]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({fJ} : Set ↥JH)) = Nat.card ↥IJ * 5 ^ 1 := by
    rw [hC, hcardI]
    norm_num
  have hT : ATypeOK 5 ↥IJ :=
    atypeOK_of_card hb hcardI (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
  haveI : Finite ↥JH := by
    have : Nat.card ↥JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  refine acompOK_of_shapeRkAt (Good := fun T _ => ATypeOK 5 T) (Rk := fun _ _ => True)
    Nat.prime_five ?_ fun _ _ h => h
  refine shapeRkAt_of_data Nat.prime_five (fun _ _ _ _ e h => ATypeOK.of_mulEquiv e h)
    (fun _ _ _ _ _ h => h) fJ IJ hLC ?_ hsimple hnab h5 hk hT trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈
      ⁅Subgroup.centralizer ({fJ} : Set ↥JH), Subgroup.centralizer ({fJ} : Set ↥JH)⁆ :=
    Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact IJ.mul_mem h1 hl

theorem acompOK_JH (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (k : ↥JH)
    (hk5 : orderOf k = 5) : ACompOK 5 k := by
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  by_cases h5A : ∃ e : ℕ, IsConj k (fJ ^ e)
  · obtain ⟨e, he⟩ := h5A
    obtain ⟨c, hc⟩ := isConj_iff.1 he
    have hko : orderOf (fJ ^ e) = 5 := by
      rw [← hc]
      exact (orderOf_conj_eq c k).trans hk5
    have hcent : Subgroup.centralizer ({fJ ^ e} : Set JH) = Subgroup.centralizer ({fJ} : Set JH) :=
      centralizer_pow_eq (by rw [hko, orderOf_fJ]) (by rw [orderOf_fJ]; norm_num)
    have hok : ACompOK 5 (fJ ^ e) := by
      intro I hI
      rw [hcent] at hI
      exact acompOK_f hb I hI
    have := ACompOK.of_mulEquiv Nat.prime_five (MulAut.conj c⁻¹) hok
    rw [MulAut.conj_apply, ← hc, show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at this
    exact this
  · push Not at h5A
    have hord : Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6 :=
      hnFiveOrders_holds k hk5 h5A
    have hO := hnFiveRest_of_orders hnFiveOrders_holds k hk5 h5A
    by_cases h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({k} : Set JH))
    · have h9 : ¬ 3 ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) := fun h => by
        have := h.trans hord
        norm_num at this
      obtain ⟨Q, hQC, hQn, hQs, s, hsC, hso, hq⟩ := hnFiveMoved_holds k hk5 h5A h3
      exact acompOK_of_no_comp (hnNoComp_of_normal_solvable hQC hQn hQs hO hord
        (hnMoved_of_sylow hQC hQn h9 hsC hso hq))
    · have hcop : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({k} : Set JH))) 3 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3 |>.symm
      have hd : Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) ∣ 2 ^ 14 * 5 ^ 6 := by
        have e : 2 ^ 14 * 3 * 5 ^ 6 = 3 * (2 ^ 14 * 5 ^ 6) := by ring
        rw [e] at hord
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop hord
      exact acompOK_of_pConstrained Nat.prime_five
        (pConstrainedShape_of_solvable Nat.prime_five (isSolvable_of_card_dvd_two_five hd) hO)

set_option maxRecDepth 20000 in
theorem arow_HN_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1415Row .HN 5 := by
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
  exact @arow_of_model .HN 5 ↥JH _ hfin hs hOut b hnc (acompOK_JH hb)

end CFSG.HardMathSupport.Dickson.I271.I1415AHN
