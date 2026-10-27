module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree

import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
import CFSG.LargeExtraspecial.S12Seven

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2 (NoXBlockFor)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


private theorem blockHasThree_of_mem_weakBlockSet
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    BlockHasThree M (pCoreOf 2 H) L := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hphase : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hMtop : M ≠ ⊤ := twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper hMtop
  have hBHS : CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar :=
    CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have h85 : CFSG.AGLEmbedding.Asc81bEightFive :=
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs hBHS)
  have h86 : CFSG.AGLEmbedding.Asc81bEightSix :=
    CFSG.AGLEmbedding.asc81bEightSix_of_bhs hBHS
  have h93 : CFSG.AGLEmbedding.Asc81bNineThree :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.asc81bNineThree_holds
  have hD2 : NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hK2 : CFSG.AGLEmbedding.KFactParabolicThree :=
    CFSG.AGLEmbedding.kFactParabolicThree
  have hInv : CFSG.AGLEmbedding.KFactBlockInvertedThree :=
    CFSG.AGLEmbedding.kFactBlockInvertedThree_holds h93
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
  exact hphase.blockHasThree hK h85 h86 h93 hD2 hK2
    (CFSG.AGLEmbedding.citedBlockThreeTransvection_of_inverted hInv)
    (CFSG.AGLEmbedding.kFactBlockThreeAltSeven_of_inverted hInv) hL

private theorem exists_pow_three_not_mem_center_barM {M S L : Subgroup G}
    (hLM : L ≤ M) (h : BlockHasThree M S L) :
    ∃ k : ↥(barM M L), k ∉ Subgroup.center ↥(barM M L) ∧
      ∃ n : ℕ, k ^ 3 ^ n = 1 := by
  obtain ⟨y, hyNL, hy3, l, hl, hlQ⟩ := h
  have hyL : y ∈ L := hyNL.2
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let yM : ↥M := ⟨y, hLM hyL⟩
  let lM : ↥M := ⟨l, hLM hl⟩
  let ybar : ↥M ⧸ CFSG.pCore 2 ↥M := q yM
  let lbar : ↥M ⧸ CFSG.pCore 2 ↥M := q lM
  let ybK : ↥(barM M L) :=
    ⟨ybar, Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hyL)⟩
  let lbK : ↥(barM M L) :=
    ⟨lbar, Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hl)⟩
  have hybK_not_center : ybK ∉ Subgroup.center ↥(barM M L) := by
    intro hyZ
    have hcomm : ybar * lbar = lbar * ybar := by
      have h := Subgroup.mem_center_iff.mp hyZ lbK
      simpa [ybK, lbK] using (congrArg Subtype.val h).symm
    have hq : q (yM * lM * yM⁻¹ * lM⁻¹) = 1 := by
      have h2 : ybar * lbar * ybar⁻¹ * lbar⁻¹ = 1 := by
        rw [hcomm]
        group
      simpa [ybar, lbar, map_mul, map_inv] using h2
    refine hlQ ?_
    simpa [yM, lM] using (mk_eq_one_iff_coe_mem_pCoreOf
      (yM * lM * yM⁻¹ * lM⁻¹)).mp hq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hy3) ⟨y, Subgroup.mem_zpowers y⟩
  have hy_ord : orderOf y = 3 ^ n := by simpa [Subgroup.orderOf_mk] using hn
  have hy_pow : y ^ 3 ^ n = 1 := by
    rw [← hy_ord]
    exact pow_orderOf_eq_one y
  have hyM_pow : yM ^ 3 ^ n = 1 := by
    apply Subtype.ext
    simpa [yM] using hy_pow
  refine ⟨ybK, hybK_not_center, n, ?_⟩
  apply Subtype.ext
  simpa [ybK, ybar] using congrArg q hyM_pow

theorem three_dvd_card_barM_quot_center
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    3 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
  have hB : BlockHasThree M (pCoreOf 2 H) L :=
    blockHasThree_of_mem_weakBlockSet h1 h2 h25 h hL
  obtain ⟨k, hk, n, hkpow⟩ := exists_pow_three_not_mem_center_barM hL.le hB
  let qZ := QuotientGroup.mk' (Subgroup.center ↥(barM M L))
  have hqZ_ne : qZ k ≠ 1 := by
    intro h1
    exact hk (by simpa [qZ, QuotientGroup.mk'_apply] using h1)
  have hqZ_pow : (qZ k) ^ 3 ^ n = 1 := by
    rw [← map_pow, hkpow, map_one]
  have hdiv : orderOf (qZ k) ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hqZ_pow
  have hne_ord : orderOf (qZ k) ≠ 1 := by
    intro h1
    exact hqZ_ne (orderOf_eq_one_iff.mp h1)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne_ord
  have hr3 : r = 3 :=
    (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow (hrdvd.trans hdiv))
  exact (hr3 ▸ hrdvd).trans (orderOf_dvd_natCard (qZ k))

theorem exists_orderOf_three_not_mem_centralizer_barM
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    ∃ t : ↥M ⧸ CFSG.pCore 2 ↥M, t ∈ barM M L ∧ orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨tK, htK3, htKZ⟩ :=
    exists_orderOf_eq_not_mem_center Nat.prime_three (by decide)
      hL.toIsTwoPrimeComponent.component.2.2
      (three_dvd_card_barM_quot_center h1 h2 h25 h hL)
  refine ⟨(tK : ↥M ⧸ CFSG.pCore 2 ↥M), tK.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, htK3]
  · intro hcent
    exact htKZ (by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_iff.mp hcent (g : ↥M ⧸ CFSG.pCore 2 ↥M) g.2
      simpa using h)

theorem one_le_pRank_three_barM
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    1 ≤ CFSG.Open.pRank 3 (barM M L) := by
  obtain ⟨t, htmem, htord, -⟩ :=
    exists_orderOf_three_not_mem_centralizer_barM h1 h2 h25 h hL
  have ht3 : t ^ 3 = 1 := by
    rw [← htord]
    exact pow_orderOf_eq_one t
  refine CFSG.SectionRank.le_pRank (p := 3) (k := 1) (by norm_num)
    (H := barM M L) (E := Subgroup.zpowers t)
    (Subgroup.zpowers_le.mpr htmem) (CFSG.Open.isElemAbelian_zpowers ht3) ?_
  rw [Nat.card_zpowers, htord, pow_one]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
