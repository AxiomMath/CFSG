module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.I1416QRows
  CFSG.LocalAnalysis.GLTheoremB
  CFSG.Yardstones.Md0ec50421ce4


set_option maxRecDepth 100000 in
theorem qcompOK_z7 : QCompOK 7 (slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6) := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  intro I hI
  obtain ⟨hs, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab hp7 hI
  haveI := hs
  have hd : 7 * Nat.card (PSimple 7 I) ∣ 1176 :=
    card_centralizer_z7 ▸ prime_mul_card_pSimple_dvd_cent hp7 orderOf_z7 hI.1
  have hd168 : Nat.card (PSimple 7 I) ∣ 168 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (by norm_num))
  have hc := card_eq_168_of_dvd hnab hd168
  exact qtypeOK_of_not_sq_dvd_aut hp7 (not_sq_seven_dvd_card_mulAut_of_card_168 hc)

set_option maxRecDepth 100000 in
theorem qcompOK_seven_J (k : J) (hk : orderOf k = 7) : QCompOK 7 k := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  obtain ⟨c, hc⟩ := exists_conj_eq_of_pair (z := slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6)
    (matJ_injective (by simp only [matJ_mul]; exact hcomm)) h7x h7y hx1 hpow
    (by rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
      factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)])
    (fun i j hi hj hij => by
      obtain ⟨m, hm⟩ := thSeven_conj hi hj hij
      refine ⟨m, matJ_injective ?_⟩
      simp only [matJ_mul, matJ_pow] at hm ⊢
      exact hm) hk
  have := QCompOK.of_mulEquiv hp7 (MulAut.conj c⁻¹) qcompOK_z7
  rw [MulAut.conj_apply, ← hc, show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at this
  exact this

set_option maxRecDepth 20000 in
theorem qrow_Th_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416QRow .Th 7 := by
  have hfin : Finite ↥CFSG.Sporadic.Th.J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  have e : CFSG.Blueprint.NativeSporadic.Th ≃* ↥CFSG.Sporadic.Th.J := CFSG.Sporadic.Th.thEquivJ
  have hs : IsSimpleGroup ↥CFSG.Sporadic.Th.J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts
  have hnc : ∃ a c : ↥CFSG.Sporadic.Th.J, a * c ≠ c * a := by
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
        CFSG.Sporadic.Th.th_kernel_facts
    have hcC : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Th) = 90745943887872000 :=
      CFSG.RankThree.OddKernel.card_Th_eq
    obtain ⟨a, c, hac⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (S := CFSG.Blueprint.NativeSporadic.Carrier .Th) (by rw [hcC]; norm_num)
    refine ⟨e a, e c, fun h => hac ?_⟩
    exact e.injective ((e.map_mul a c).trans (h.trans (e.map_mul c a).symm))
  have b : ↥CFSG.Sporadic.Th.J ≃* (TauCeti.CFSGIndex.sporadic .Th).Group :=
    e.symm.trans (hbr .Th).some
  exact @qrow_of_model .Th 7 ↥CFSG.Sporadic.Th.J _ hfin hs hOut b hnc qcompOK_seven_J

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
