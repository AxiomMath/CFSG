module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4L63
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291GammaP
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Beta
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCY
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCSig
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29InnerHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291
open CFSG.AGLEmbedding (CatalogSimpleSections)
section Holds



theorem kFactSingleW_of_gamma (hγ : N3.GammaStructureP) : KFactSingleW := by
  intro p X _ _ P x z hpl hperf hU W hWcop hBW
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp5 := hpl.five_le
  have hp2 : p ≠ 2 := by omega
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp (primeComplementCore_coprime p)
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : ¬ p ∣ Nat.card π.ker := by rw [QuotientGroup.ker_mk']; exact hD3
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup X) := hpl.plane.isIsolatedPlane.1
  have hxP : x ∈ (P : Subgroup X) := hBP (Subgroup.mem_sup_left (mem_zpowers x))
  have hB : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup X) :=
    IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hxpow : x ^ p = 1 := hpl.plane.isElemAbelian.2 x (Subgroup.mem_sup_left (mem_zpowers x))
  have hzpow : z ^ p = 1 := hpl.plane.isElemAbelian.2 z (Subgroup.mem_sup_right (mem_zpowers z))
  have hzP : z ∈ (P : Subgroup X) := hBP (Subgroup.mem_sup_right (mem_zpowers z))
  have hx1 : x ≠ 1 := by
    intro h1
    have hc := hpl.plane.card_eq
    rw [h1, Subgroup.zpowers_one_eq_bot, bot_sup_eq, Nat.card_zpowers] at hc
    have hd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzpow
    have hle := Nat.le_of_dvd hprime.pos hd
    have : p ^ 2 ≤ p := hc ▸ hle
    nlinarith [hprime.two_le]
  have hBC : zpowers x ⊔ zpowers z ≤ centralizer ({x} : Set X) := by
    intro g hg
    rw [mem_centralizer_singleton_iff]
    have hab := hpl.plane.isElemAbelian.1.is_comm.comm
    exact congrArg Subtype.val
      (hab ⟨g, hg⟩ ⟨x, Subgroup.mem_sup_left (mem_zpowers x)⟩)
  have hC2 : Open.pRank p (centralizer ({x} : Set X)) = 2 := by
    refine le_antisymm hpl.rank_centralizer ?_
    have h1 := CFSG.SectionRank.pRank_mono hprime.one_lt hBC
    have h2 : Open.pRank p (zpowers x ⊔ zpowers z : Subgroup X) = 2 :=
      CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isElemAbelian hprime
        hpl.plane.isElemAbelian hpl.plane.card_eq
    omega
  obtain ⟨L, hLn, hLs, hLnab, hLcat, hnlu, hLC, hxL, hzL'⟩ :=
    hγ p hprime hp5 X P x hpl.catalog hxP hx1 hxpow hpl.pRank_eq hC2 hperf hU
  have hzL : (z : X ⧸ D) ∈ L := hzL' z hpl.z_central hzP hzpow
  have hcfg := N3.cfg_of_plane63E3 hpl
  have hBmap : (zpowers x ⊔ zpowers z : Subgroup X).map π =
      zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hx1b : (x : X ⧸ D) ≠ 1 := fun h =>
    hx1 (K62B.eq_one_of_mk_eq_one hprime (P.isPGroup'.to_le (zpowers_le.mpr hxP))
      (Subgroup.mem_zpowers x) h)
  have hxord : orderOf (x : X ⧸ D) = p := orderOf_eq_prime hcfg.x_pow hx1b
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
  have hrankc : Open.pRank p (centralizer ({(x : X ⧸ D)} : Set (X ⧸ D))) ≤ 2 := by
    have hxp : IsPGroup p (zpowers x) := P.isPGroup'.to_le (zpowers_le.mpr hxP)
    have hmap :=
      CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
        p hprime π hπs hker (zpowers x) hxp
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hmap
    have hxπ : π x = (x : X ⧸ D) := rfl
    rw [hxπ] at hmap
    rw [← hmap]
    exact (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hprime π hker _).trans
      hpl.rank_centralizer
  have hY3 : 3 ≤ Open.pRank p (⊤ : Subgroup (X ⧸ D)) := by
    have h1 := CFSG.SectionRank.pRank_quotient_eq (G := X) (p := p) D hD3
    have h2 : Open.pRank p (P : Subgroup X) ≤ Open.pRank p (⊤ : Subgroup X) :=
      CFSG.SectionRank.pRank_mono hprime.one_lt le_top
    have := hpl.pRank_eq
    omega
  have hC29 : ∀ d ∈ (zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) : Subgroup (X ⧸ D)), d ≠ 1 →
      GLAPLayer p (centralizer ({d} : Set (X ⧸ D))) = ⊥ ∧
        GLAPPrimeCoreOf p (centralizer ({d} : Set (X ⧸ D))) = ⊥ := by
    intro d hd hd1
    haveI := hLn
    exact CFSG.LocalAnalysis.RankFourTheoremC.kd29Inner_holds p hprime hp5 (X ⧸ D) L hLs hLnab
      hLcat hnlu hLC hY3 ⟨(x : X ⧸ D), hxL, hxord, hrankc⟩ d (hBL hd) hd1 (hBe.2 d hd)
  have hcard : Nat.card (zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) : Subgroup (X ⧸ D)) = p ^ 2 := by
    rw [← hBmap]
    exact (K62B.card_map_mk_eq hprime hB).trans hpl.plane.card_eq
  have hsc : ∀ y ∈ centralizer ((zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) :
      Subgroup (X ⧸ D)) : Set (X ⧸ D)), y ^ p = 1 →
      y ∈ (zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) : Subgroup (X ⧸ D)) := by
    rw [← hBmap]
    exact sc_map hprime hB (fun y hy hyp => hpl.plane.mem_of_mem_centralizer y hy hyp)
  have hsig := signalizer_eq_bot_of_sc hprime hp2 hBe hcard hsc hC29
  have hWbar : (W.map π) = ⊥ := by
    refine hsig _ (hWcop.of_dvd_right (W.card_map_dvd π)) ?_
    rw [← hBmap]
    exact (Subgroup.map_mono hBW).trans (Subgroup.le_normalizer_map π)
  have := (Subgroup.map_eq_bot_iff _).1 hWbar
  rwa [hπ, QuotientGroup.ker_mk'] at this


end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
