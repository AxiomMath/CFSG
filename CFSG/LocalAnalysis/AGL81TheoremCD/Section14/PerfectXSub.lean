module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTenBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStar
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.PerfectComponent
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCent
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenOneIGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenTwoOneHolds
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
import CFSG.GH74.GLS.Stage2.Local.P34Perf
import CFSG.CGT.PushingUpLit.CGT6.Diag.ReduceComp

public section

open CFSG.RankThreeCoreUniqueness.Helpers

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

private theorem starImg_isPerfect {N Y : Subgroup G} (hYN : Y ≤ N)
    (hY : Group.IsPerfect ↥Y) : Group.IsPerfect ↥(starImg 3 N Y) := by
  have hYsubperf : Group.IsPerfect ↥(Y.subgroupOf N) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hYN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYN).symm.surjective
  haveI : Group.IsPerfect ↥(Y.subgroupOf N) := hYsubperf
  exact Group.IsPerfect.map (QuotientGroup.mk' (primeComplementCore (G := ↥N) 3))

private theorem starImg_le_layer_of_isPerfect {M E N : Subgroup G}
    (h711 : SevenOneOne) (h : HypCGen G M 3 E N)
    (hLN : ¬ pLayerIn 3 N ≤ M) {Y : Subgroup G} (hY : Group.IsPerfect ↥Y)
    (hYX : Y ≤ xSub 3 M N) :
    starImg 3 N Y ≤ CFSG.layer (StarGroup 3 N) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := StarGroup 3 N
  let Ys : Subgroup X := starImg 3 N Y
  have hxSubN : xSub 3 M N ≤ N := by
    unfold xSub CFSG.AGLEmbedding.d1PlusCore
    exact Subgroup.map_subtype_le _
  have hYN : Y ≤ N := hYX.trans hxSubN
  have hYsperfect : Group.IsPerfect ↥Ys := starImg_isPerfect hYN hY
  have hKX : CFSG.Open.IsKGroup X := by
    change CFSG.Open.IsKGroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)
    exact h.toNineSettingGen.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 X = ⊥ := by
    change CFSG.pPrimeCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) = ⊥
    exact CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet
  have hr' : CFSG.pRank 3 ↥(⊤ : Subgroup X) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    simpa [X] using NineSettingGen.openPRank_starGroup_le_three h.toNineSettingGen
      h.mem_H2Fam h3
  have hcomp_exists : ∃ L : Subgroup X, CFSG.IsComponent L := by
    by_contra hno
    push Not at hno
    have hlayer : CFSG.layer X = ⊥ := by
      rw [CFSG.layer.eq_sSup]
      exact le_antisymm (sSup_le fun C hC => absurd hC (hno C)) bot_le
    have hbot : pLayerIn 3 N = ⊥ :=
      (CFSG.LocalAnalysis.RankThreeUC.AGL81C.pLayerIn_eq_bot_iff Nat.prime_three N).mpr
        (by simpa [X] using hlayer)
    exact hLN (by rw [hbot]; exact bot_le)
  obtain ⟨L, hLcomp⟩ := hcomp_exists
  have hcard4 : Nat.card {C : Subgroup X // CFSG.IsComponent C} ≤ 4 := by
    have h3le : Nat.card {C : Subgroup X // CFSG.IsComponent C} ≤ 3 := by
      have h := CFSG.LocalAnalysis.RankThreeUC.AGL81C.ncard_isComponent_le_three
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactOmegaNotCentral_holds hKX hO hr'
      change Nat.card ↥({C : Subgroup X | CFSG.IsComponent C} : Set (Subgroup X)) ≤ 3
      rwa [Nat.card_coe_set_eq]
    omega
  have hnorm_comp : ∀ C : Subgroup X, CFSG.IsComponent C →
      Ys ≤ Subgroup.normalizer (C : Set X) := by
    intro C hC
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    exact CFSG.GH74.GLS.Stage2.Local.P34.perfect_normalizes_component hcard4
      (Subgroup.isPerfect_iff.mp hYsperfect) hC y hy x hx
  have hcomp_sup : ∀ C : Subgroup X, CFSG.IsComponent C →
      Ys ≤ C ⊔ Subgroup.centralizer (C : Set X) :=
    fun C hC => perfect_le_sup_centralizer_of_isComponent h711 hKX
      (Subgroup.isPerfect_iff.mp hYsperfect) hC (hnorm_comp C hC)
  have hYlayer : Ys ≤ CFSG.layer X ⊔
      Subgroup.centralizer (CFSG.layer X : Set X) :=
    perfect_le_layer_sup_centralizer (Subgroup.isPerfect_iff.mp hYsperfect) hcomp_sup
  have hR : CFSG.Open.pRank 3 (CFSG.pCore 3 X) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.pRank_pCore_le_two
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactOmegaNotCentral_holds hKX hO hr'
      (L := L) hLcomp
  haveI hSolv : Group.IsSolvable
      ↥(Subgroup.centralizer (CFSG.layer X : Set X)) :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.isSolvable_centralizer_layer_three N hR
  haveI : Group.IsPerfect ↥Ys := hYsperfect
  haveI hLn : (CFSG.layer X).Normal := by
    haveI := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  exact CFSG.ClassicalInvolution.LBalanceProof.perfect_le_of_le_sup_solvable Ys
    (CFSG.layer X) (Subgroup.centralizer (CFSG.layer X : Set X)) hYlayer

theorem HypCGen.le_of_isPerfect_of_le_xSub {M E N : Subgroup G}
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) (h : HypCGen G M 3 E N)
    (hLN : ¬ pLayerIn 3 N ≤ M) {Y : Subgroup G} (hY : Group.IsPerfect ↥Y)
    (hYX : Y ≤ xSub 3 M N) : Y ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := StarGroup 3 N
  let A : Subgroup X := starImg 3 N M
  let K : Subgroup X := kStar 3 M N
  let Ys : Subgroup X := starImg 3 N Y
  have hxSubN : xSub 3 M N ≤ N := by
    unfold xSub CFSG.AGLEmbedding.d1PlusCore
    exact Subgroup.map_subtype_le _
  have hYN : Y ≤ N := hYX.trans hxSubN
  have hYsperfect : Group.IsPerfect ↥Ys := starImg_isPerfect hYN hY
  have hYs_le_layer : Ys ≤ CFSG.layer X :=
    starImg_le_layer_of_isPerfect h711 h hLN hY hYX
  have hYs_le_C : Ys ≤ Subgroup.centralizer (K : Set X) := by
    have hstar_le : Ys ≤ starImg 3 N (xSub 3 M N) := by
      simpa [Ys, starImg] using
        Subgroup.map_mono (f := QuotientGroup.mk' (primeComplementCore (G := ↥N) 3))
          (Subgroup.subgroupOf_mono N hYX)
    rwa [starImg_xSub] at hstar_le
  have hKdecomp : K = sSup {C : Subgroup X | CFSG.IsComponent C ∧ ¬ C ≤ A} :=
    NineSettingGen.kStar_eq_sSup_of_not_le h.toNineSettingGen hLN
  let LA : Subgroup X := sSup {C : Subgroup X | CFSG.IsComponent C ∧ C ≤ A}
  have hLA_le_A : LA ≤ A := sSup_le fun C hC => hC.2
  have hLA_le_C : LA ≤ Subgroup.centralizer (K : Set X) := by
    have h := sSup_le_centralizer_sSup (X := X) A
    rwa [← hKdecomp] at h
  have hEeq : CFSG.layer X = K ⊔ LA := by
    rw [NineSettingGen.layer_eq_kStar_sup_of_not_le h.toNineSettingGen hLN]
  have hYleKLA : Ys ≤ K ⊔ LA := by
    rw [← hEeq]
    exact hYs_le_layer
  have hYs_le_LA : Ys ≤ LA :=
    CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce.le_of_centralizes hYsperfect
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLA_le_C)
      (by simpa only [sup_comm] using hYleKLA)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYs_le_C)
  exact (h.toNineSettingGen.le_iff_starImg_le hYN).mpr (hYs_le_LA.trans hLA_le_A)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
