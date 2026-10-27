module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Six
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Rank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521W1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

theorem pRank_normalizer_lift_le_one_gen (hT : LieOddRankTable) (hKSML3 : KSML3) {G : Type}
    [Group G] [Finite G] {M T : Subgroup G} (hO1211 : O1211At G M) (hO1217 : O1217At G M)
    (hO1521 : O1521At G M) {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (hR : LiftRankBound G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {Ti : Subgroup ↥M} (hTi : Ti = T₁ ∨ Ti = T₂) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set ↥M) ⊓ L) ≤ 1 := by
  by_contra hcon
  have h2 : 2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set ↥M) ⊓ L) := by omega
  obtain ⟨E, hEle, hEa, hEc⟩ := exists_elemAbelian_sq hr h2
  have hEN : E ≤ Subgroup.normalizer (Ti : Set ↥M) := hEle.trans inf_le_left
  have hEL : E ≤ L := hEle.trans inf_le_right
  have hne : Ti ≠ ⊥ := by
    rcases hTi with rfl | rfl
    · exact ctx.pair.ne_bot₁
    · exact ctx.pair.ne_bot₂
  have hle : Ti ≤ T.subgroupOf M := by
    rcases hTi with rfl | rfl
    · exact ctx.pair.le_center.trans (omegaOneCenterOf_le_subgroup _)
    · exact ctx.pair.le₂
  have hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic := by
    rcases hTi with rfl | rfl
    · exact ctx.pair.char₁
    · exact ctx.pair.char₂
  have hΓ := gamma_le_of_le_lift_gen hO1217 ctx h11 h20 hLs hL hr hr2 hEL hEa hEc
  obtain ⟨H₀, hH₀max, hH₀le, hH₀ne⟩ :=
    exists_maxTwoLocal_normalizer_gen ctx.sylow.le ctx.sylow.isPGroup ctx.notLe hne hle hchar
  have hEH : E.map M.subtype ≤ H₀ :=
    (Subgroup.map_mono hEN).trans ((map_subtype_normalizer_le Ti).trans hH₀le)
  have hEM : E.map M.subtype ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hEab : IsElemAbelian r (E.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hEa M.subtype
  have hEcard : Nat.card (E.map M.subtype) = r ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (E.equivMapOfInjective M.subtype M.subtype_injective).toEquiv.symm
  by_cases hrσ : r ∈ sigmaM G M
  · have hb : CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set ↥M)) ≤ 1 := by
      rcases hTi with rfl | rfl
      · exact ctx.rank_N₁ r hrσ
      · exact ctx.rank_N₂ r hrσ
    have := CFSG.SectionRank.pRank_mono hr.one_lt (inf_le_left :
      Subgroup.normalizer (Ti : Set ↥M) ⊓ L ≤ Subgroup.normalizer (Ti : Set ↥M))
    omega
  · by_cases hr3 : r = 3
    · subst hr3
      obtain ⟨A₀, T₀, R₀, H', hcfg⟩ :=
        hO1521 h11 (E.map M.subtype) hEM hEab (by simpa using hEcard) hΓ H₀ hH₀max hEH hH₀ne
      obtain ⟨A₁, R₁, H₁, hcfg'⟩ := exists_L34Config_of_sylow ctx.sylow hcfg
      obtain ⟨-, h3, -⟩ := h21 A₁ R₁ H₁ hcfg' Ls L hLs hL
      have h1 := pRank_lift_eq_one_of_isLThreeOdd_gen hT hKSML3
        (hR.liftCtxGen ctx.gn ctx.good hLs hL) h3
      have := CFSG.SectionRank.pRank_mono hr.one_lt (inf_le_right :
        Subgroup.normalizer (Ti : Set ↥M) ⊓ L ≤ L)
      omega
    · have h5 : 5 ≤ r := by
        by_contra hlt
        have : r < 5 := by omega
        interval_cases r <;> simp_all <;> exact absurd hr (by decide)
      have := hO1211 r hr h5 hrσ (E.map M.subtype) hEM hEab hEcard hΓ H₀ hH₀max.1 hEH
      exact hH₀ne (hH₀max.2 M ctx.maxLocal.1 this).symm

theorem pRank_normalizer_lift_le_one (o1211 : O1211) (o1217 : O1217) (o1521 : O1521)
    (hT : LieOddRankTable) (hKSML3 : KSML3) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {Ti : Subgroup ↥M} (hTi : Ti = T₁ ∨ Ti = T₂) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set ↥M) ⊓ L) ≤ 1 :=
  pRank_normalizer_lift_le_one_gen hT hKSML3 (O1211At.of_ctx2 o1211 ctx)
    (O1217At.of_ctx2 o1217 ctx) (O1521At.of_ctx2 o1521 ctx) (S15CtxGen.of_ctx2 ctx)
    (liftRankBound_of_ctx2 ctx) h11 h20 h21 hLs hL hTi hr hr2

section Row1522

open KFactsSmall
open scoped commutatorElement

theorem isCentralProdA6Z3_gnImg_gen (hT : LieOddRankTable) (hKSML3 : KSML3) {G : Type}
    [Group G] [Finite G] {M T : Subgroup G} (hO1211 : O1211At G M) (hO1217 : O1217At G M)
    (hO1521 : O1521At G M) {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (hR : LiftRankBound G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M)))) :
    IsCentralProdA6Z3 ↥(gnImg (T.subgroupOf M) (Subgroup.normalClosure (L : Set ↥M))) :=
  isCentralProdA6Z3_gnImg_of_Q_gen hR ctx.gn ctx.good hLs hL hcp
    (pRank_normalizer_lift_le_one_gen hT hKSML3 hO1211 hO1217 hO1521 ctx hR h11 h20 h21 hLs hL
      (Or.inl rfl) Nat.prime_three (by norm_num))

theorem isCentralProdA6Z3_gnImg (o1211 : O1211) (o1217 : O1217) (o1521 : O1521)
    (hT : LieOddRankTable) (hKSML3 : KSML3) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M)))) :
    IsCentralProdA6Z3 ↥(gnImg (T.subgroupOf M) (Subgroup.normalClosure (L : Set ↥M))) :=
  isCentralProdA6Z3_gnImg_gen hT hKSML3 (O1211At.of_ctx2 o1211 ctx) (O1217At.of_ctx2 o1217 ctx)
    (O1521At.of_ctx2 o1521 ctx) (S15CtxGen.of_ctx2 ctx) (liftRankBound_of_ctx2 ctx) h11 h20 h21
    hLs hL hcp

theorem small_of_normal_gen (hT : LieOddRankTable)
    (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k517_4b : K517_4b)
    (hSix : GNSixAll) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hO1211 : O1211At G M) (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (hR : LiftRankBound G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h21 : Row1521 G M T T₁ T₂) {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) : Small1522 ↥Ls := by
  by_contra hbad
  obtain ⟨p, hp⟩ := ctx.p_mem
  have h3 : CFSG.Open.pRank 3 L < 3 := (h20 p hp Ls L hLs hL).2.2.1
  obtain ⟨Ti, r, hTi, hr, hr2, h2⟩ := exists_rank_two_of_bad_of_gnSixAll hT hKSMAlt hKSMOdd
    hKSMU4 hKSML3 k517_4b hSix (hR.liftCtxGen ctx.gn ctx.good hLs hL) hLn h3 hbad
  have := pRank_normalizer_lift_le_one_gen hT hKSML3 hO1211 hO1217 hO1521 ctx hR h11 h20 h21 hLs
    hL hTi hr hr2
  omega

theorem small_of_normal (o1211 : O1211) (o1217 : O1217) (o1521 : O1521) (hT : LieOddRankTable)
    (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k517_4b : K517_4b)
    (hSix : GNSixAll) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h21 : Row1521 G M T T₁ T₂) {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) : Small1522 ↥Ls :=
  small_of_normal_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k517_4b hSix
    (O1211At.of_ctx2 o1211 ctx) (O1217At.of_ctx2 o1217 ctx) (O1521At.of_ctx2 o1521 ctx)
    (S15CtxGen.of_ctx2 ctx) (liftRankBound_of_ctx2 ctx) h11 h20 h21 hLs hL hLn

theorem row1522_gen (hT : LieOddRankTable)
    (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k517_4b : K517_4b)
    (hSix : GNSixAll) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hO1211 : O1211At G M) (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (hR : LiftRankBound G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h15 : Row1515 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂) : Row1522 G M T T₁ T₂ := by
  intro Ls L hLs hL J hJ Js hJs
  subst hJ
  by_cases hLJ : L = Subgroup.normalClosure (L : Set ↥M)
  · have hLn : L.Normal := by
      have : (Subgroup.normalClosure (L : Set ↥M)).Normal := Subgroup.normalClosure_normal
      rwa [← hLJ] at this
    have hJsLs : Js = Ls := by rw [hJs, ← hLJ]; exact hL.2
    subst hJsLs
    rcases small_of_normal_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k517_4b hSix
      hO1211 hO1217 hO1521 ctx hR h11 h20 h21 hLs hL hLn with h1 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h3))
  · rcases h15 Ls L hLs hL _ rfl with h | hcp | ⟨hL3, hk⟩
    · exact absurd h hLJ
    · refine Or.inr (Or.inr (Or.inr ⟨?_,
        sigmaM_eq_five_gen hO1217 hO1521 ctx hR h11 h20 h21 hLs hL hLJ hcp⟩))
      rw [hJs]
      exact isCentralProdA6Z3_gnImg_gen hT hKSML3 hO1211 hO1217 hO1521 ctx hR h11 h20 h21 hLs
        hL hcp
    · refine Or.inr (Or.inl ⟨?_,
        sigmaM_eq_seven_gen hO1217 hO1521 ctx hR h11 h20 h21 hLs hL hLJ hL3 hk⟩)
      rw [hJs]
      exact isLThreeTwoSq_or_cube_of_prod
        (isLThreeTwoProd_gnImg_gen hKSML3 (hR.liftCtxGen ctx.gn ctx.good hLs hL) hLJ hL3 hk)

theorem row1522 (o1211 : O1211) (o1217 : O1217) (o1521 : O1521) (hT : LieOddRankTable)
    (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k517_4b : K517_4b)
    (hSix : GNSixAll) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) (h15 : Row1515 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂) : Row1522 G M T T₁ T₂ :=
  row1522_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k517_4b hSix
    (O1211At.of_ctx2 o1211 ctx) (O1217At.of_ctx2 o1217 ctx) (O1521At.of_ctx2 o1521 ctx)
    (S15CtxGen.of_ctx2 ctx) (liftRankBound_of_ctx2 ctx) h11 h15 h20 h21

end Row1522

end CFSG.LocalAnalysis.RankThreeUC.S15
