module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieBuild
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndexResidue
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Aux

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem mk_mem_normalizers_of_normalizer {A : Subgroup G} {P : Sylow 3 G}
    (hctx : PairStrongCtx P M A H R) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    {n : G} (hn : n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) (hnM : n ∈ M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ ∈
        Subgroup.normalizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ ∈
        Subgroup.normalizer
          (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) :
            Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ ∈
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hpr := hctx.pair
  have hnS : n ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [hpr.normalizer_twoCore_H]
    exact hn.1.1
  have hb := mk_mem_normalizer_blocks hL hk1 hnM hnS
  refine ⟨?_, hb.2, hb.1⟩
  have hRn : R.map (MulAut.conj n).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
  have := barM_map_conj hnM R
  rw [hRn] at this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm

theorem not_three_dvd_relIndex_barM {A : Subgroup G} {P : Sylow 3 G}
    (hctx : PairStrongCtx P M A H R) :
    ¬ 3 ∣ (barM M R).relIndex (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G))) := by
  have hpr := hctx.pair
  have hN : Subgroup.normalizer (pCoreOf 2 H : Set G) = H := hpr.normalizer_twoCore_H
  rw [hN]
  set f := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hf
  have hR1 : barM M R = (R.subgroupOf M).map f := rfl
  have hK1 : barM M H = ((H ⊓ M).subgroupOf M).map f := by
    rw [Subgroup.inf_subgroupOf_right]; rfl
  rw [hR1, hK1, Subgroup.relIndex_map_map, QuotientGroup.ker_mk']
  have hker : CFSG.pCore 2 ↥M ≤ (H ⊓ M).subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have : (x : G) ∈ pCoreOf 2 M := by
      unfold pCoreOf
      exact Subgroup.mem_map_of_mem M.subtype hx
    rw [← hpr.normalizer_twoCore_H]
    exact Subgroup.le_normalizer (hpr.twoCore_M_le this)
  rw [sup_eq_left.mpr hker]
  have hR1K : R.subgroupOf M ≤ (H ⊓ M).subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨hpr.le_H (Subgroup.mem_subgroupOf.mp hx), x.2⟩
  have hmul := Subgroup.relIndex_mul_relIndex (R.subgroupOf M) (R.subgroupOf M ⊔ CFSG.pCore 2 ↥M)
    ((H ⊓ M).subgroupOf M) le_sup_left (sup_le hR1K hker)
  have hbase : (R.subgroupOf M).relIndex ((H ⊓ M).subgroupOf M) = R.relIndex (H ⊓ M) :=
    Subgroup.relIndex_subgroupOf inf_le_right
  intro hd
  apply hctx.not_three_dvd_relIndex_inf
  rw [← hbase, ← hmul]
  exact hd.mul_left _

theorem exists_threeElement_pow_of_barM {X : Subgroup G} {y₀ : ↥M} (hy₀ : (y₀ : G) ∈ X)
    (hy3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) y₀) ^ 3 = 1)
    (hy1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) y₀ ≠ 1) :
    ∃ z : ↥M, (z : G) ∈ X ∧ IsPGroup 3 (Subgroup.zpowers (z : G)) ∧
      ∃ m : ℕ, QuotientGroup.mk' (CFSG.pCore 2 ↥M) z =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) y₀) ^ m ∧
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) z ≠ 1 := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have ho : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
  obtain ⟨e, m, hm3, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hom
    exact ho hom
  refine ⟨y₀ ^ m, X.pow_mem hy₀ m, ?_, m, by rw [map_pow], ?_⟩
  · have hord : orderOf ((y₀ : G) ^ m) = 3 ^ e := by
      rw [orderOf_pow' _ hm0, Subgroup.orderOf_coe, hom]
      have : Nat.gcd (3 ^ e * m) m = m := Nat.gcd_eq_right (Dvd.intro_left _ rfl)
      rw [this, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    refine IsPGroup.of_card (n := e) ?_
    rw [Nat.card_zpowers]
    push_cast
    exact hord
  · rw [map_pow]
    intro h
    have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) y₀) = 3 :=
      orderOf_eq_prime hy3 hy1
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    exact hm3 hdvd

end Aux


theorem false_of_oneImage_centre (hD2 : D1NoXBlock) {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hirr : IrreducibleOn (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))) (barM M R))
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hZ : 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) : False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hpr := hctx.pair
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hfact
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hH := hctx.esc.pRank_H
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  set Rb := barM M R with hRb
  have hCB : Cb ≤ Bb := fun c hc =>
    hpr.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hX fun L' hL' =>
      (hk1 L' hL').symm ▸ hc
  have hBH : Open.pRank 3 Bb ≤ 2 := (hpr.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hRB : Rb ≤ Bb := barM_mono fun r hr => by
    rw [hpr.normalizer_twoCore_H]
    exact hpr.le_H hr
  have hR2 : Open.pRank 3 Rb = 2 := by
    rw [pRank_barM_eq h3 (by decide) M R hpr.le_M]
    exact hctx.esc.pRank_eq
  have hnS : ∀ n ∈ H ⊓ M, n ∈ Subgroup.normalizer (S : Set G) := fun n hn => by
    rw [hpr.normalizer_twoCore_H]
    exact hn.1
  obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' 3 hZ
  rw [Subgroup.orderOf_mk] at hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  obtain ⟨z₀, hz₀X, rfl⟩ := mem_barM_iff.mp (hCB hzZ.2)
  obtain ⟨w, hwX, hw3, m, hwm, hw1⟩ := exists_threeElement_pow_of_barM hz₀X hz3 hz1
  have hwHM : (w : G) ∈ H ⊓ M := ⟨by rw [← hpr.normalizer_twoCore_H]; exact hwX, w.2⟩
  have hZ₀ : mk w ∈ Lb ⊓ Cb := by
    rw [hwm]
    exact (Lb ⊓ Cb).pow_mem hzZ m
  obtain ⟨h, hhHM, hhw⟩ := exists_conj_mem_of_sylow hpr.isPGroup_R
    hctx.not_three_dvd_relIndex_inf hwHM hw3
  have hhb := mk_mem_normalizer_blocks hL hk1 hhHM.2 (hnS h hhHM)
  set w' : ↥M := ⟨h⁻¹ * w * h, M.mul_mem (M.mul_mem (M.inv_mem hhHM.2) w.2) hhHM.2⟩ with hw'
  have hw'e : mk w' = (mk ⟨h, hhHM.2⟩)⁻¹ * mk w * ((mk ⟨h, hhHM.2⟩)⁻¹)⁻¹ := by
    rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hinvL : (mk ⟨h, hhHM.2⟩)⁻¹ ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.inv_mem _ hhb.1
  have hw'R : mk w' ∈ Rb := mem_barM_iff.mpr ⟨w', hhw, rfl⟩
  have hw'L : mk w' ∈ Lb := by
    rw [hw'e]
    exact (Subgroup.mem_normalizer_iff.mp hinvL _).mp hZ₀.1
  have hw'C : mk w' ∈ Cb := by
    rw [hw'e]
    exact mem_centralizer_conj_of_mem_normalizer hinvL hZ₀.2
  have hw'1 : mk w' ≠ 1 := by
    intro h1
    apply hw1
    have hwe : mk w = mk ⟨h, hhHM.2⟩ * mk w' * (mk ⟨h, hhHM.2⟩)⁻¹ := by
      rw [hw'e]
      group
    rw [hwe, h1, mul_one, mul_inv_cancel]
  have hinv : barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) ≤
      Subgroup.normalizer ((Rb ⊓ (Lb ⊓ Cb) : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro ν hν
    obtain ⟨n₀, hn₀, rfl⟩ := mem_barM_iff.mp hν
    obtain ⟨hnR, -, hnL⟩ := mk_mem_normalizers_of_normalizer hctx hL hk1 hn₀ n₀.2
    have hnC : ∀ x, x ∈ Cb ↔ mk n₀ * x * (mk n₀)⁻¹ ∈ Cb := by
      intro x
      constructor
      · exact fun hx => mem_centralizer_conj_of_mem_normalizer hnL hx
      · intro hx
        have := mem_centralizer_conj_of_mem_normalizer (Subgroup.inv_mem _ hnL) hx
        have e : (mk n₀)⁻¹ * (mk n₀ * x * (mk n₀)⁻¹) * ((mk n₀)⁻¹)⁻¹ = x := by group
        rwa [e] at this
    rw [Subgroup.mem_normalizer_iff] at hnR hnL ⊢
    intro x
    constructor
    · rintro ⟨hxR, hxL, hxC⟩
      exact ⟨(hnR x).mp hxR, (hnL x).mp hxL, (hnC x).mp hxC⟩
    · rintro ⟨hxR, hxL, hxC⟩
      exact ⟨(hnR x).mpr hxR, (hnL x).mpr hxL, (hnC x).mpr hxC⟩
  rcases hirr _ inf_le_left hinv with hbot | htop
  · exfalso
    have hmem : mk w' ∈ (Rb ⊓ (Lb ⊓ Cb) : Subgroup _) := ⟨hw'R, hw'L, hw'C⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw'1 hmem
  · have hRC : Rb ≤ Cb := fun x hx => by
      have : x ∈ (Rb ⊓ (Lb ⊓ Cb) : Subgroup _) := by rw [htop]; exact hx
      exact this.2.2
    obtain ⟨y, hyP, hy3, hyC⟩ := hy
    have hyB : y ∈ Bb := barM_mono inf_le_left hyP
    have hyL : y ∈ Lb := barM_mono inf_le_right hyP
    have hyR : y ∈ Subgroup.centralizer (Rb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (hRC hb) y hyL).symm
    have hsucc := succ_pRank_le_of_commute (q := 3) hRB hRC hyB hy3 hyC hyR
    omega


theorem false_of_oneImage_oddIndex (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    (hK3 : KFactNineThreeThreeBig) (hAut : KFactStrongThreeAutomizer)
    (hE9 : KFactParabolicE9NotTransitive) (hcen : PairBlockCentreThree) {G : Type} [Group G]
    [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hodd : ¬ PairEvenIndex M H) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) :
    False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hpr := hctx.pair
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hH := hctx.esc.pRank_H
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPL
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  set Rb := barM M R with hRb
  have hBH : Open.pRank 3 Bb ≤ 2 := (hpr.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hPLB : PL ≤ Bb := barM_mono inf_le_left
  have hR2 : Open.pRank 3 Rb = 2 := by
    rw [pRank_barM_eq h3 (by decide) M R hpr.le_M]
    exact hctx.esc.pRank_eq
  by_cases h4 : NineThreeFour M S L
  · exact false_of_oneImage_nineThreeFour h93 hD2 hΛ hctx hL hk1 h4
  by_cases halt : IsAltTwelveOrSixteen ↥Lb
  · obtain ⟨x, hxV, hx1, hrank⟩ := pairOneImagePure_of_alt hnat hctx hL halt
    exact hctx.esc.false_of_pureVector hctx.d1 hctx.beta hctx.strong hxV hx1 hrank
      (fun y hy _ => pairOneImageFix_of_alt hJ hnat hctx hL halt hy)
  by_cases hrk2 : Open.pRank 3 L = 2 ∧ ¬ 3 ∣ Nat.card (Lb ⊓
      Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
  · exact not_rankTwo_of_oneImage hLF h418 hL27 h93 hD2 hΛ hU hL5 hctx hL hk1 hrk2
  have hyex : ∃ y ∈ PL, y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    by_cases hZ : 3 ∣ Nat.card (Lb ⊓
        Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
    · exact hcen G P M A H R hctx L hL hZ
    · exact exists_order_three_noncentral hL.le (hthree L hL) hZ
  have hy' : ∃ y ∈ PL, y ^ 3 = 1 ∧ y ≠ 1 := by
    obtain ⟨y, hyP, hy3, hyC⟩ := hyex
    exact ⟨y, hyP, hy3, fun h => hyC (h ▸ Subgroup.one_mem _)⟩
  obtain ⟨hel, h9, htr⟩ := hctx.transitive_of_oddIndex hAut hodd
  have htrb := transitive_barM htr
  have hirrb := irreducibleOn_of_transitiveOnNonidentity htrb
  have hRP : Rb ≤ PL := hctx.barM_le_of_oneImage hL hk1 hy' hirrb
  by_cases hZ : 3 ∣ Nat.card (Lb ⊓
      Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
  · exact false_of_oneImage_centre hD2 hctx hL hk1 hirrb hyex hZ
  have hnot := hpr.nineThree_not_one h85 hX hL
  rcases pairBlockCensus hLF h418 hL27 h93 hD2 G P M A H R hctx L hL with h | h | h | h | h | h
  · exact h4 h
  · exact hrk2 ⟨h.1, h.2.1⟩
  · exact halt h.2
  ·
    have h1 : Open.pRank 3 Rb ≤ Open.pRank 3 Lb :=
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hRP).trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 (barM_mono inf_le_right))
    have h2 : Open.pRank 3 Lb = Open.pRank 3 L := pRank_barM_eq h3 (by decide) M L hL.le
    omega
  · obtain ⟨h23, hr3⟩ := h
    rcases h23 with h2 | h3'
    ·
      have hSolv : BlockPLThreeSolv M S L :=
        d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
          hctx.strong hctx.perf L hL
      have hnsyl : ¬ IsSylowTwoOf (pCoreOf 2 PL) Lb := by
        rw [← h2.2.2]
        exact hnot.2 h2
      have hel' : IsElemAbelian 3 Rb := CFSG.AGLEmbeddingD2.isElemAbelian_barM hel
      have hc9 : Nat.card Rb = 9 :=
        (card_barM_of_isPGroup_three hpr.isPGroup_R hpr.le_M).trans h9
      have hidx : ¬ 3 ∣ Rb.relIndex PL := by
        intro hd
        have hmul := Subgroup.relIndex_mul_relIndex Rb PL Bb hRP hPLB
        apply not_three_dvd_relIndex_barM hctx
        rw [← hmul]
        exact hd.mul_right _
      have hN : ∀ x ∈ barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)),
          x ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
          x ∈ Subgroup.normalizer (Rb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
          x ∈ Subgroup.normalizer (PL : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        intro x hx
        obtain ⟨n₀, hn₀, rfl⟩ := mem_barM_iff.mp hx
        obtain ⟨h1, h2', h3''⟩ := mk_mem_normalizers_of_normalizer hctx hL hk1 hn₀ n₀.2
        exact ⟨h3'', h1, h2'⟩
      exact hE9 (↥M ⧸ CFSG.pCore 2 ↥M) Lb PL Rb
        (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))) hL.component.2.2 h2.1 h2.2.1 hnsyl
        hSolv hRP hel' hc9 hidx (fun x hx => (hN x hx).1) (fun x hx => (hN x hx).2.1)
        (fun x hx => (hN x hx).2.2) htrb
    · exact hK3 G M S L hpr.isKGroup.1 hpr.asc81bHyp hL hnot.1
        (hpr.not_isSylowTwoOf_inf h85 hX hL) h3' hr3
        (d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
          hctx.strong hctx.perf L hL)
  · exact hZ h.1

theorem oddOneImageKill_of_cited (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    (hK3 : KFactNineThreeThreeBig) (hAut : KFactStrongThreeAutomizer)
    (hE9 : KFactParabolicE9NotTransitive) (hcen : PairBlockCentreThree) : OddOneImageKill := by
  intro G _ _ P M A H R hctx hodd _ _ _ L hL hk1 _
  exact false_of_oneImage_oddIndex hLF h418 hL27 h93 hD2 hΛ hU hL5 hJ hnat hK3 hAut hE9 hcen
    hctx hodd hL hk1

end CFSG.AGLEmbeddingD2.McLaughlin
