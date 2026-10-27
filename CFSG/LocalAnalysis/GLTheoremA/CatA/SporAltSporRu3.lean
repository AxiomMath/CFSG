module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows


theorem scompOK_three_of_card_dvd_2160
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 2160) : SCompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 2160 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact stypeOK_three_of_card_dvd_720 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

section Ru

open CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd.S2


theorem srow_Ru_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .Ru 3 := by
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
  refine @srow_of_model .Ru 3 ↥ruP _ hfin hs hOut b hnc fun k hk => ?_
  obtain ⟨c, hcz⟩ := exists_conj_ruThree k hk
  have hk' : orderOf (c * ruThreeX0 * c⁻¹) = 3 := by
    rw [← Nat.card_zpowers, hcz, Nat.card_zpowers, hk]
  have hcent : Subgroup.centralizer ({k} : Set ↥ruP) =
      Subgroup.centralizer ({c * ruThreeX0 * c⁻¹} : Set ↥ruP) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers hcz).symm
  refine SCompOK.of_centralizer_eq hcent.symm ?_
  refine scompOK_three_of_card_dvd_2160 hb hk' ?_
  rw [CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.centralizer_conj c ruThreeX0,
    Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard0]

end Ru

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows

