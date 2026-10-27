module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PA
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PB
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PC
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PD
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521W1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section Row1523

theorem row1523_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (k58 : K58)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂) :
    Row1523 G M T T₁ T₂ := by
  intro Ls L hLs hL hchev hnl hbig
  obtain ⟨S₀, P, h1, h2, h3, -⟩ := k58 ↥M (T.subgroupOf M) ctx.gn Ls hLs.1
    (ctx.good.shape Ls hLs).1 hchev hnl hbig
  refine ⟨S₀, P, h1, h2, ?_⟩
  rw [normalizer_lift_eq_comap ctx.gn hLs.1 hL]
  exact h3

theorem row1523 {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (k58 : K58) (ctx : S15Ctx2 G M T T₁ T₂) : Row1523 G M T T₁ T₂ :=
  row1523_gen k58 (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx)

end Row1523

section Row1521X

open KFactsSmall
variable {X : Type} [Group X] [Finite X]

theorem false_of_k21d_group (k21d : K21d) (k420 : K420) {T R A L : Subgroup X} (hA : AConfig T R A)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hL : IsC2 L) (hLn : L.Normal)
    (hS : IsK21dGroup ↥(barO2 L)) (hZ : Subgroup.center ↥(barO2 L) = ⊥)
    (hm3 : 2 ≤ CFSG.Open.pRank 3 L) (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    (hnc : ⁅barO2 L, barO2 A⁆ ≠ ⊥) : False := by
  haveI hN : (barO2 L).Normal := hLn.map _ (QuotientGroup.mk'_surjective _)
  rcases hA.inf_eq_bot_or_le (K := L) Subgroup.le_normalizer_of_normal with hAL | hAL
  ·
    have hker := ker_conjNormal_comp (QuotientGroup.mk' (CFSG.pCore 2 X)) (K := barO2 L)
    haveI : (L ⊔ ((MulAut.conjNormal : (X ⧸ CFSG.pCore 2 X) →* MulAut ↥(barO2 L)).comp
        (QuotientGroup.mk' (CFSG.pCore 2 X))).ker).Normal := by
      haveI : L.Normal := hLn
      infer_instance
    rcases hA.inf_eq_bot_or_le (K := L ⊔ ((MulAut.conjNormal : (X ⧸ CFSG.pCore 2 X) →*
        MulAut ↥(barO2 L)).comp (QuotientGroup.mk' (CFSG.pCore 2 X))).ker)
      Subgroup.le_normalizer_of_normal with h | h
    · have hd := autData_conjNormal (QuotientGroup.mk' (CFSG.pCore 2 X)) hLn hA hT hnc
      have hbot := map_inf_innAut_eq_bot (QuotientGroup.mk' (CFSG.pCore 2 X)) (Jn := L) (A := A) h
      exact false_of_autData_outer k420 hL.component.2.2
        (isClassicalTwoOrG2_quot_of_isK21dGroup hS hZ) hd hbot
    · refine false_of_A_le_sup_cMHat hA hL hLn hZ hm3 hr3 hAL ?_
      rw [hker] at h
      exact h
  · obtain ⟨N, T', R', E, hd⟩ := exists_k21dData hA hT hL hLn hZ hAL hnc
    exact false_of_k21dData k21d hS hd

theorem xlevel_1521_S2_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k21b : K21b) (k21d : K21d) (k420 : K420)
    {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) (hA : AConfig T R A) (h15 : Shape1515 L)
    (h20 : CFSG.Open.pRank 3 L < 3)
    (hnc : ⁅gnImg T (Subgroup.normalClosure (L : Set X)), gnImg T A⁆ ≠ ⊥) : False := by
  have hTs := hl.gn.sylow
  have hr3 := hl.rank_three
  have hJn : (Subgroup.normalClosure (L : Set X)).Normal := Subgroup.normalClosure_normal
  rcases case_table_1521_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl h15 h20 with
    ⟨hLn, hty⟩ | hcp | hb | ⟨hLn, hS, hZ, hm3⟩
  · have hJL : Subgroup.normalClosure (L : Set X) = L := Subgroup.normalClosure_eq_self L
    rw [hJL] at hnc
    have hnc' : ⁅barO2 L, barO2 A⁆ ≠ ⊥ := fun h =>
      hnc (commute_star_of_commute_barO2 hl.gn h)
    haveI hN : (barO2 L).Normal := hLn.map _ (QuotientGroup.mk'_surjective _)
    exact false_of_autData_k21ab k21b hl.lift.1.component.2.2 hty
      (autData_conjNormal (QuotientGroup.mk' (CFSG.pCore 2 X)) hLn hA hTs hnc')
  · have hnc' : ⁅barO2 (Subgroup.normalClosure (L : Set X)), barO2 A⁆ ≠ ⊥ := fun h =>
      hnc (commute_star_of_commute_barO2 hl.gn h)
    exact false_of_centralProd hA hTs hJn hcp hnc'
  · haveI hN : (gnImg T (Subgroup.normalClosure (L : Set X))).Normal :=
      hJn.map _ (QuotientGroup.mk'_surjective _)
    exact false_of_autData_k21c hb (autData_conjNormal (toStar T) hJn hA hTs hnc)
  · have hnc' : ⁅barO2 L, barO2 A⁆ ≠ ⊥ := fun h => by
      have hJL : Subgroup.normalClosure (L : Set X) = L := Subgroup.normalClosure_eq_self L
      rw [hJL] at hnc
      exact hnc (commute_star_of_commute_barO2 hl.gn h)
    exact false_of_k21d_group k21d k420 hA hTs hl.lift.1 hLn hS hZ hm3 hr3 hnc'

theorem xlevel_1521_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k21b : K21b) (k21d : K21d) (k420 : K420)
    {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) (hA : AConfig T R A) (h15 : Shape1515 L)
    (h20 : CFSG.Open.pRank 3 L < 3) :
    L.Normal ∧ IsLThreeOdd ↥Ls ∧ ⁅Ls, gnImg T A⁆ = ⊥ := by
  by_cases hcomm : ⁅gnImg T (Subgroup.normalClosure (L : Set X)), gnImg T A⁆ = ⊥
  · obtain ⟨hn, h3⟩ := xlevel_1521_S1_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl hA h15 hcomm
    refine ⟨hn, h3, ?_⟩
    have hLJ : Ls ≤ gnImg T (Subgroup.normalClosure (L : Set X)) := by
      rw [← hl.lift.2]
      exact Subgroup.map_mono Subgroup.le_normalClosure
    exact le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hLJ le_rfl)
  · exact (xlevel_1521_S2_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k21b k21d k420 hl hA h15 h20
      hcomm).elim

theorem row1521_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k21b : K21b) (k21d : K21d) (k420 : K420) {G : Type}
    [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hR : LiftRankBound G M T T₁ T₂) (h15 : Row1515 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) : Row1521 G M T T₁ T₂ := by
  intro A R H' hcfg Ls L hLs hL
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact xlevel_1521_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k21b k21d k420
    (hR.liftCtxGen ctx.gn ctx.good hLs hL)
    hcfg.toAConfig (h15 Ls L hLs hL _ rfl) (h20 p hp Ls L hLs hL).2.2.1

theorem row1521 (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hKSML3 : KSML3) (k21b : K21b) (k21d : K21d) (k420 : K420) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂)
    (h15 : Row1515 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂) : Row1521 G M T T₁ T₂ :=
  row1521_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k21b k21d k420
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx)
    (liftRankBound_of_ctx2 ctx) h15 h20

end Row1521X

end CFSG.LocalAnalysis.RankThreeUC.S15
