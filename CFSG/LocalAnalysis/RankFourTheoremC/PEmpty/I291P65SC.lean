module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Mult
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29InnerHolds

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup I291
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.AGLEmbedding (CatalogSimpleSections)

theorem scCaseTwo_of_kdata (hMult : KDMultP5) (hFld : KDFieldP5) (h29 : KD29Inner) :
    I291P65.SCCaseTwo := by
  intro p X _ _ P x z hpl L hL hLu hlu W hWcop hBW
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp5 := hpl.five_le
  have hp2 : p ≠ 2 := by omega
  have hYD := yData_of_plane63 hpl
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp (primeComplementCore_coprime p)
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup X) := hpl.plane.isIsolatedPlane.1
  have hB : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup X) :=
    IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hBmap : (zpowers x ⊔ zpowers z : Subgroup X).map π =
      zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hcfg := hYD.cfg
  have hcat : CatalogSimpleSections (X ⧸ D) := hcfg.catalog
  have hcore : primeComplementCore (G := X ⧸ D) p = ⊥ := hcfg.core
  have hLn : L.Normal := normal_of_unique hL hLu
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hcatQ : IsCatalogGroup (↥L ⧸ center ↥L) := hcat.isCatalogGroup_center_quotient hL
  have hZ : center ↥L = ⊥ := by
    by_contra hZne
    exact hlu (hMult p hprime hp5 ↥L hq hcatQ hZne (isPGroup_center hcore hL))
  obtain ⟨hsimp, hnonab, hcatL⟩ := hcat.isSimpleGroup_of_center_eq_bot hL hZ
  have hpc := pCore_eq_bot hcfg hL hLn hZ
  have hC := centralizer_eq_bot hcore hpc hL hLu hZ
  have hnlu : ¬ IsLinearOrUnitaryAt p ↥L := fun h => hlu (isLinearOrUnitaryAt_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm h)
  have hx1 : (x : X ⧸ D) ≠ 1 := by
    intro h1
    have h2 := hYD.rank_cent
    rw [h1] at h2
    have h3 : centralizer ({(1 : X ⧸ D)} : Set (X ⧸ D)) = ⊤ := by simp
    rw [h3] at h2
    have := hYD.four_le
    omega
  have hxord : orderOf (x : X ⧸ D) = p := orderOf_eq_prime hcfg.x_pow hx1
  have hxL : (x : X ⧸ D) ∈ L := by
    by_contra hxL
    rcases hFld p hprime hp5 (X ⧸ D) hcat hcore L hLn hsimp hnonab hnlu hC hYD.four_le _ hxL
        hxord with h | ⟨N, hNn, hNidx⟩
    · have := hYD.rank_cent
      omega
    · haveI := hNn
      have hN : N = ⊤ := hYD.perf N (IsPGroup.of_card (n := 1)
        ((Subgroup.index_eq_card N).symm.trans (hNidx.trans (pow_one p).symm)))
      rw [hN, Subgroup.index_top] at hNidx
      exact hprime.one_lt.ne hNidx
  have hzL : (z : X ⧸ D) ∈ L :=
    hcfg.z_mem_comp_of_fixed (C := ⟨L, (CFSG.isComponent_iff_open L).2 hL⟩) (fun g _ => by
      rw [normalizer_eq_top_iff.mpr hLn]
      exact mem_top g)
  have hBL : (zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) : Subgroup (X ⧸ D)) ≤ L :=
    sup_le (zpowers_le.2 hxL) (zpowers_le.2 hzL)
  have hXe : IsElemAbelian p (zpowers (x : X ⧸ D)) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hcfg.x_pow)
  have hZe : IsElemAbelian p (zpowers (z : X ⧸ D)) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hcfg.z_pow)
  have hBe : IsElemAbelian p (zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) : Subgroup (X ⧸ D)) :=
    K62B.isElemAbelian_sup hXe hZe (fun a ha b hb =>
      hcfg.zpowers_central hb (zpowers_le.2 hcfg.x_mem ha))
  have hC29 : ∀ d ∈ (zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) : Subgroup (X ⧸ D)), d ≠ 1 →
      GLAPLayer p (centralizer ({d} : Set (X ⧸ D))) = ⊥ ∧
        GLAPPrimeCoreOf p (centralizer ({d} : Set (X ⧸ D))) = ⊥ := by
    intro d hd hd1
    haveI := hLn
    exact h29 p hprime hp5 (X ⧸ D) L hsimp hnonab hcatL hnlu hC (by have := hYD.four_le; omega)
      ⟨(x : X ⧸ D), hxL, hxord, hYD.rank_cent⟩ d (hBL hd) hd1 (hBe.2 d hd)
  have hsig := signalizer_eq_bot_of_sc hprime hp2 hBe hYD.plane_card hYD.sc hC29
  have hWbar : (W.map π) = ⊥ := by
    refine hsig _ (hWcop.of_dvd_right (W.card_map_dvd π)) ?_
    rw [← hBmap]
    exact (Subgroup.map_mono hBW).trans (Subgroup.le_normalizer_map π)
  have := (Subgroup.map_eq_bot_iff _).1 hWbar
  rwa [hπ, QuotientGroup.ker_mk'] at this

section CertificateInstances


theorem kFactP65Single_of_field (hFld : KDFieldP5) (hLin : I291P65.KD29LinUni)
    (h309 : I291P65.KD309) : KFactP65Single :=
  kFactP65Single_of_kdata
    (scCaseTwo_of_kdata
      (kdMultP5_of_tables CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
      hFld kd29Inner_holds)
    hLin h309

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
