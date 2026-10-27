module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporThreeSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416QRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows


theorem qtypeOK_three_of_card_dvd_720
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 720) :
    QTypeOK 3 T := by
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcases : Nat.card T = 60 ∨ Nat.card T = 72 ∨ Nat.card T = 80 ∨ Nat.card T = 144 ∨
      Nat.card T = 90 ∨ Nat.card T = 120 ∨ Nat.card T = 180 ∨ Nat.card T = 240 ∨
      Nat.card T = 360 ∨ Nat.card T = 720 := by
    obtain ⟨c, hc⟩ := hd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hc12 : c ≤ 12 := by
      by_contra h
      have : Nat.card T * 13 ≤ Nat.card T * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c <;> omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h
  · exact qtypeOK_three_of_card_dvd_360 hb hnab (by rw [h]; norm_num)
  · exact qtypeOK_three_of_card_dvd_360 hb hnab (by rw [h]; norm_num)
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_five (by norm_num) (a := 4) (b := 1) (by rw [h]; norm_num))).elim
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_three (by norm_num) (a := 4) (b := 2) (by rw [h]; norm_num))).elim
  · exact qtypeOK_three_of_card_dvd_360 hb hnab (by rw [h]; norm_num)
  · exact qtypeOK_three_of_card_dvd_360 hb hnab (by rw [h]; norm_num)
  · exact qtypeOK_three_of_card_dvd_360 hb hnab (by rw [h]; norm_num)
  · exact qtypeOK_of_card hb h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
  · exact qtypeOK_three_of_card_dvd_360 hb hnab (by rw [h])
  · exact qtypeOK_of_card hb h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)

theorem qcompOK_three_of_card_dvd_2160
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 2160) : QCompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 2160 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact qtypeOK_three_of_card_dvd_720 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

section Ru

open CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd.S2


theorem qrow_Ru_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416QRow .Ru 3 := by
  have e : CFSG.Blueprint.NativeSporadic.Ru ≃* ↥ruP := ruEquivP
  have hfin : Finite ↥ruP := Finite.of_equiv _ e.toEquiv
  have hs : IsSimpleGroup ↥ruP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ru.isSimpleGroup_Ru e.symm
  have hc : Nat.card ↥ruP = 145926144000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hpr : ¬ (Nat.card ↥ruP).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥ruP, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥ruP _ hfin hs hpr
  have b : ↥ruP ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group := e.symm.trans (hbr .Ru).some
  obtain ⟨hC0eq, hC0card⟩ := ruThreeC0_spec
  have hcard0 : Nat.card (Subgroup.centralizer ({ruThreeX0} : Set ↥ruP)) = 2160 := by
    have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype ruP ruThreeX0
    rw [← Subgroup.card_map_of_injective ruP.subtype_injective, hmapc, ← hC0card, hC0eq]
    rfl
  refine @qrow_of_model .Ru 3 ↥ruP _ hfin hs hOut b hnc fun k hk => ?_
  obtain ⟨c, hcz⟩ := exists_conj_ruThree k hk
  have hk' : orderOf (c * ruThreeX0 * c⁻¹) = 3 := by
    rw [← Nat.card_zpowers, hcz, Nat.card_zpowers, hk]
  have hcent : Subgroup.centralizer ({k} : Set ↥ruP) =
      Subgroup.centralizer ({c * ruThreeX0 * c⁻¹} : Set ↥ruP) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers hcz).symm
  refine QCompOK.of_centralizer_eq hcent.symm ?_
  refine qcompOK_three_of_card_dvd_2160 hb hk' ?_
  rw [CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.centralizer_conj c ruThreeX0,
    Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard0]

end Ru

end CFSG.LocalAnalysis.GLTheoremA.I1416QRows

