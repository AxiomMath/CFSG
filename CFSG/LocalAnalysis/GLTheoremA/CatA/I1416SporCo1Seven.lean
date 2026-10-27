module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporSevenType
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block Timmesfeld.Co1Seven
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.I1416Rows


theorem card_centralizer_seven (s : ↥GA) (hs : orderOf s = 7) :
    Nat.card (Subgroup.centralizer ({s} : Set ↥GA)) = 17640 ∨
      Nat.card (Subgroup.centralizer ({s} : Set ↥GA)) = 1176 := by
  have hS : sylowOK Native.aR Native.bR = true := Certificates.certificate13696
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : ∀ (x g : ↥GA), Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set ↥GA)) =
      Nat.card (Subgroup.centralizer ({x} : Set ↥GA)) := fun x g =>
    @card_centralizer_conj' ↥GA (Subgroup.toGroup GA) inferInstance g x
  have hQ : Nat.card P0 = 7 ^ (Nat.card (⊤ : Subgroup ↥GA)).factorization 7 := by
    rw [card_P0 hS, Subgroup.card_top, factorization_card_GA_seven]
    norm_num
  obtain ⟨g, -, hg⟩ := Co3T.exists_conj_mem_of_full (le_top : P0 ≤ ⊤) hQ (Subgroup.mem_top s) hs
  have hy : orderOf (g⁻¹ * s * g) = 7 := by
    have := orderOf_conj_eq g⁻¹ s
    rw [inv_inv] at this
    rw [this, hs]
  have hsy : Nat.card (Subgroup.centralizer ({s} : Set ↥GA)) =
      Nat.card (Subgroup.centralizer ({g⁻¹ * s * g} : Set ↥GA)) := by
    have h := hcard s g⁻¹
    rw [inv_inv] at h
    exact h.symm
  rw [hsy]
  rcases mem_P0 hS hg with h1 | ⟨k, hk, b, hb, hyk⟩
  · rw [h1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  · have hconj := conj_to_target hS hk
    have hc : cE k * (g⁻¹ * s * g) * (cE k)⁻¹ = tgtE k ^ (b + 1) := by
      rw [hyk]
      exact @conj_pow_of_conj ↥GA (Subgroup.toGroup GA) _ _ _ hconj _
    have hC : Subgroup.centralizer ({tgtE k ^ (b + 1)} : Set ↥GA) =
        Subgroup.centralizer ({tgtE k} : Set ↥GA) :=
      @centralizer_pow_eq_of_not_dvd 7 ↥GA (Subgroup.toGroup GA) _ (by norm_num)
        (orderOf_tgtE hS k) _ (by omega)
    rw [← hcard (g⁻¹ * s * g) (cE k), hc, hC]
    unfold tgtE
    split_ifs
    · exact Or.inl CFSG.HardMathSupport.Solomon.Coordinator.Co1Spor.card_centralizer_sE
    · exact Or.inr CFSG.HardMathSupport.Solomon.Coordinator.Co1Spor.card_centralizer_tE

theorem card_pSimple_dvd_2520 (s : ↥GA) (hs : orderOf s = 7) {I : Subgroup ↥GA}
    (hI : GLAPComponent 7 (Subgroup.centralizer ({s} : Set ↥GA)) I) :
    Nat.card (PSimple 7 I) ∣ 2520 := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have hd := prime_mul_card_pSimple_dvd_cent (by norm_num) hs hI.1
  rcases card_centralizer_seven s hs with h | h <;> rw [h] at hd
  · exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (by norm_num))
  · exact (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (by norm_num))).trans
      (by norm_num : 168 ∣ 2520)

theorem co1_model (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    Finite ↥GA ∧ IsSimpleGroup ↥GA ∧ (∃ a c : ↥GA, a * c ≠ c * a) ∧
      Nonempty (↥GA ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) := by
  have hfin : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have e : CFSG.Blueprint.NativeSporadic.Co1 ≃* ↥GA := co1MatEquiv
  have hs : IsSimpleGroup ↥GA :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co1.isSimpleGroup_Co1 e.symm
  have hpr : ¬ (Nat.card ↥GA).Prime := by rw [card_GA_eq]; norm_num
  exact ⟨hfin, hs,
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥GA _ hfin hs hpr,
    ⟨e.symm.trans (hbr .Co1).some⟩⟩

theorem row_Co1_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : I1416SporRow .Co1 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model hbr
  refine @row_of_model .Co1 7 ↥GA _ hfin hs hOut b hnc fun x hx I hI => ?_
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num) hI
  haveI := hsI
  exact typeOK_seven_of_card_dvd_2520 hb hnab (card_pSimple_dvd_2520 x hx hI)

theorem qrow_Co1_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.I1416QRow .Co1 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model hbr
  refine @CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qrow_of_model .Co1 7 ↥GA _ hfin hs hOut b hnc
    fun x hx I hI => ?_
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num) hI
  haveI := hsI
  exact qtypeOK_seven_of_card_dvd_2520 hb hnab (card_pSimple_dvd_2520 x hx hI)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S
