module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicSetting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicBender
public import CFSG.Assembly.LowTwoRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.BenderCoverStatement

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

namespace CyclicCase.Setting

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)} (hs : Setting G S H z J)
include hs

theorem isBenderGroup_or_jOne
    (IH : CanonicalBelow (Nat.card G))
    (hrank2 : RankTwoCoverStatement) :
    CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Subgroup.center J) ∨
      Nonempty ((J ⧸ Subgroup.center J) ≃* properTwoGenCoreJ1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hperf, hsimple, hnonab⟩, -⟩ := hs.component
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := hsimple
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center J)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center J)).ker = Subgroup.center J :=
    QuotientGroup.ker_mk' _
  obtain ⟨Q, hQB⟩ := hs.exists_sylow_le
  have hkerB : (QuotientGroup.mk' (Subgroup.center J)).ker ≤
      (escapingImage H z).subgroupOf J := by
    rw [hker]
    exact (hs.center_isPGroup.le_sylow_of_normal Q).trans hQB
  have hker2 : IsPGroup 2 (QuotientGroup.mk' (Subgroup.center J)).ker := by
    rw [hker]
    exact hs.center_isPGroup
  let Qs : Sylow 2 (J ⧸ Subgroup.center J) := Q.mapSurjective hπ
  have hQsB : (Qs : Subgroup (J ⧸ Subgroup.center J)) ≤
      ((escapingImage H z).subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hQB
  have hΓ2 : properTwoGenCoreGamma (Qs : Subgroup (J ⧸ Subgroup.center J)) 2 ≠ ⊤ := fun h =>
    CyclicCase.map_ne_top_of_ker_le _ hkerB hs.subgroupOf_ne_top (top_le_iff.mp
      (h ▸ CyclicCase.gamma_two_le_map_of_cyclic _ hπ hkerB hker2
        hs.isCyclic_of_twoPoint Qs hQsB))
  have h2 : 2 ≤ CFSG.Open.twoRank (J ⧸ Subgroup.center J) :=
    CFSG.Assembly.LowTwoRank.two_le_twoRank _ hnonab hs.even_card_quotient
  have hne2 : CFSG.Open.twoRank (J ⧸ Subgroup.center J) ≠ 2 := fun h => by
    obtain ⟨x, hxJ, hx2, hxz⟩ := hs.rank
    have heq := hrank2 J hperf.commutator_eq_top hs.center_isPGroup hs.center_ne_bot
      hs.center_isCyclic hsimple h ⟨x, hxJ⟩ ⟨escapingBar z, hs.bar_mem⟩
      (by rwa [Subgroup.orderOf_mk]) (by rw [Subgroup.orderOf_mk]; exact hs.quotientData.bar_order)
    exact hxz (congrArg Subtype.val heq)
  have h3 : 3 ≤ CFSG.Open.pRank 2 (Qs : Subgroup (J ⧸ Subgroup.center J)) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq]
    omega
  rcases IH _ hs.card_quotient_lt hsimple hnonab Qs h3 hΓ2 with hΓ1 | hJ1
  · exact Or.inl (CyclicCase.isBenderGroup_of_gamma_one_ne_top Qs h2 hΓ1)
  · exact Or.inr hJ1

end CyclicCase.Setting

theorem squareCaseCyclicImpossibleBelow_of
    (hcov : SquareCaseCoverExcluded)
    (hrank2 : RankTwoCoverStatement) : SquareCaseCyclicImpossibleBelow := by
  intro G _ _ S H z IH hS J hJ hJH hrank hK hcyc
  exact hcov G S H z hS J hJ hJH hrank hK
    (CyclicCase.Setting.isBenderGroup_or_jOne ⟨hS, hJ, hJH, hrank, hcyc⟩ IH hrank2)

end CFSG.ProperTwoGeneratedCore.Lemma37
