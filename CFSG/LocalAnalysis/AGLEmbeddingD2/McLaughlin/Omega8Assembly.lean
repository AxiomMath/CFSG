module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Kill
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.AtlasOrders
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Omega8Small
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Step3
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem PairStrongCtx.omega8_step0 (hOut : KFactOmega8Out) {P : Sylow 3 G}
    {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hr3 : 3 ≤ Open.pRank 3 L)
    (hom : IsOmegaEightPlus (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    (barM M L).Normal ∧ Subgroup.center ↥(barM M L) = ⊥ ∧ IsOmegaEightPlus ↥(barM M L) := by
  have hLn : (barM M L).Normal := barM_normal_of_oneImage hctx.pair hctx.esc.pRank_H hL hk1 hr3
  have hZ2 : IsPGroup 2 (Subgroup.center ↥(barM M L)) :=
    hOut.2 ↥(barM M L) hL.component.2.2 hom
  have hZ1 : Subgroup.center ↥(barM M L) = ⊥ :=
    OrdinaryProofs.centre_eq_bot_of_normal_of_pCore_eq_bot
      (OrdinaryProofs.normal_twoGroup_eq_bot_barM M) hLn hZ2
  exact ⟨hLn, hZ1, OrdinaryProofs.isOmegaEightPlus_of_center_eq_bot hZ1 hom⟩

theorem PairStrongCtx.irreducible_of_comm (hK : KFactStrongThreeAutomizer)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) :
    IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
      IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R := by
  have hpr := hctx.pair
  have hesc := hctx.esc
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hRHM : R ≤ H ⊓ M := le_inf hpr.le_H hpr.le_M
  have hR9 : 9 ∣ Nat.card R := by
    obtain ⟨E, hER, -, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 h3 R
    rw [hesc.pRank_eq] at hEc
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← hEc]
    exact Subgroup.card_dvd_of_le hER
  have h3HM : 3 ∣ Nat.card (H ⊓ M : Subgroup G) :=
    (show (3 : ℕ) ∣ 9 by norm_num).trans (hR9.trans (Subgroup.card_dvd_of_le hRHM))
  set N₀ : Subgroup ↥H := (H ⊓ M).subgroupOf H with hN₀
  have hstr : GLBStronglyEmbedded 3 N₀ :=
    glbStronglyEmbedded_subgroupOf_inf hctx.strong hesc.not_le h3HM
  have hrk : Open.pRank 3 N₀ = 2 := by
    rw [hN₀, CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 h3 _ _ inf_le_left]
    apply le_antisymm
    · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 inf_le_left).trans
        hesc.pRank_H.le
    · exact hesc.pRank_eq.symm.le.trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hRHM)
  obtain ⟨T, hT⟩ := hesc.isSylow
  set R' : Subgroup ↥H := R.subgroupOf H with hR'
  have hR'T : R' = (T : Subgroup ↥H) := by
    rw [hR', ← hT]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hR'N₀ : R' ≤ N₀ := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRHM (Subgroup.mem_subgroupOf.mp hx))
  have hR'p : IsPGroup 3 R' := hR'T ▸ T.isPGroup'
  have hR'syl : ¬ 3 ∣ R'.relIndex N₀ := by
    intro hd
    apply T.not_dvd_index
    rw [← hR'T, ← Subgroup.relIndex_mul_index hR'N₀]
    exact hd.mul_right _
  have hRc' : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a := fun a ha b hb =>
    Subtype.ext (hRc (a : G) (Subgroup.mem_subgroupOf.mp ha) (b : G)
      (Subgroup.mem_subgroupOf.mp hb))
  obtain ⟨hel, hc9, hirr⟩ := (hK ↥H hpr.isKGroup.2 N₀ hstr hrk R' hR'N₀ hR'p hR'syl).1 hRc'
  refine ⟨?_, ?_, irreducibleOn_of_subgroupOf hpr.le_H hirr⟩
  · have := elementary_map_injective 3 R' H.subtype H.subtype_injective hel
    rwa [hR', Subgroup.map_subgroupOf_eq_of_le hpr.le_H] at this
  · rw [← hc9]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hpr.le_H).toEquiv).symm


theorem PairStrongCtx.isSylowTwoOf_M_of_omega8 (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hAut : KFactStrongThreeAutomizer) (hOut : KFactOmega8Out)
    (hTri : KFactOmega8Triality) (hPar : KFactOmega8Parabolic)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) (hr3 : 3 ≤ Open.pRank 3 L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hom : IsOmegaEightPlus (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hQT : pCoreOf 2 M ≤ T) :
    IsSylowTwoOf T M := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hpr := hctx.pair
  have hfact := aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hfact
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have h86 : Asc81bEightSix := asc81bEightSix_of_bhs bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hH := hctx.esc.pRank_H
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  obtain ⟨hLn, hZ1, hΩ⟩ := hctx.omega8_step0 hOut hL hk1 hr3 hom
  set S := pCoreOf 2 H with hS
  set Q := ↥M ⧸ CFSG.pCore 2 ↥M
  set Lb := barM M L with hLb
  set C := Subgroup.centralizer (Lb : Set Q) with hC
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPL
  have hsolv : BlockPLThreeSolv M S L :=
    d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair hctx.strong
      hctx.perf L hL
  have hnot2 : ¬ IsSylowTwoOf (barM M (S ⊓ L)) Lb := (hpr.nineThree_not_one h85 hX hL).2 h2
  have hLp : ⁅Lb, Lb⁆ = Lb :=
    Subgroup.isPerfect_iff.mp (⟨hL.component.2.2.1⟩ : Group.IsPerfect ↥Lb)
  have h3L : 3 ∣ Nat.card Lb :=
    OrdinaryProofs.three_dvd_card_barM_of_two_le_pRank hL.le (by omega)
  have hRM : R ≤ M := hpr.le_M
  have hRH : R ≤ H := hpr.le_H
  by_cases hRL : barM M R ≤ Lb ⊔ C
  swap
  ·
    obtain ⟨u, huR, huC⟩ := Set.not_subset.mp hRL
    have hRS : R ≤ Subgroup.normalizer (S : Set G) := by
      rw [hS, hpr.normalizer_twoCore_H]
      exact hRH
    have hR3 : IsPGroup 3 (barM M R) := hpr.isPGroup_R.comap_subtype.map _
    exact hctx.isSylowTwoOf_M_of_outer h84 h86 hD2 hOut hTri hL hk1 h2 hZ1 hΩ hsolv hnot2 hLp
      h3L (barM_mono hRS huR) (hR3.to_le (Subgroup.zpowers_le.mpr huR)) huC hT hQT
  obtain ⟨y, hyP, hy3, hyC⟩ := exists_order_three_noncentral hL.le (hthree L hL) hZ
  have hPL2 : Open.pRank 3 PL ≤ 2 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 (barM_mono inf_le_left)).trans
      ((hpr.pRank_barM_normalizer_le h3 (by decide)).trans hH.le)
  have hnotSyl : ¬ IsSylowTwoOf (pCoreOf 2 PL) Lb := by
    rw [← h2.2.2]
    exact hnot2
  obtain ⟨-, hPel, -, -⟩ := hPar Q Lb PL hΩ h2.2.1
  have hcommbar := hpr.commutative_barM_of_le_sup h84 h86 hX hH hthree hL hk1 hRL
    ⟨y, hyP, hy3, hyC⟩ (fun E hE hE3 => (hPel hnotSyl hsolv hPL2 E hE hE3).1)
  obtain ⟨hRel, hR9, hirr⟩ :=
    hctx.irreducible_of_comm hAut (comm_of_barM_comm hpr.isPGroup_R hRM hcommbar)
  have hy1 : y ≠ 1 := fun h => hyC (h ▸ Subgroup.one_mem _)
  have hRPL : barM M R ≤ PL := barM_le_PL_of_irreducible hpr hL hk1 hirr ⟨y, hyP, hy1, hy3⟩
  have hirrb : IrreducibleOn (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))) (barM M R) :=
    irreducibleOn_barM hirr hRM _ (fun n hn hnM => mem_barM_iff'.mpr ⟨⟨n, hnM⟩, hn, rfl⟩)
  exact hctx.isSylowTwoOf_M_of_swap h84 h86 hD2 hOut hTri hPar hL hk1 h2 hZ1 hΩ hsolv hnot2 hLp
    h3L (CFSG.AGLEmbeddingD2.isElemAbelian_barM hRel)
    ((card_barM_of_isPGroup_three hpr.isPGroup_R hRM).trans hR9) hRPL hirrb hT hQT

theorem pairOmega8S6Residue_of_cited (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hAut : KFactStrongThreeAutomizer) (hOut : KFactOmega8Out)
    (hTri : KFactOmega8Triality) (hPar : KFactOmega8Parabolic) (hGN : GlaubermanNilesInput)
    (hCov : KFactParabolicCoverOmega8) (hK : KFactStrongThreeSolv) (hBor : KFactOmega8Borel)
    (hOdd : KFactLThreeTwoOddIndex) : PairOmega8S6Residue := by
  intro G _ _ P M A H R hctx hev L hL hk1 h2 hr3 hZ hom
  obtain ⟨-, hZ1, hΩ⟩ := hctx.omega8_step0 hOut hL hk1 hr3 hom
  obtain ⟨T, -, hQT, hNT, hT⟩ := hctx.exists_twoGroup_of_evenIndex hev
  exact false_of_omega8_of_sylowM hD2 hGN hCov hK hPar hBor hOdd hctx hev hL hk1 h2 hr3 hZ hZ1 hΩ
    hQT hNT hT
    (hctx.isSylowTwoOf_M_of_omega8 h93 hD2 hΛ hAut hOut hTri hPar hL hk1 h2 hr3 hZ hom hT hQT)

end CFSG.AGLEmbeddingD2.McLaughlin
