module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.General
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar2
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.StdBareStandard
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Finkelstein77
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H}

private theorem le_of_perfect_of_index_le_two_fin [N.Normal] (hidx : N.index ≤ 2)
    (hL : Group.IsPerfect ↥L) : L ≤ N := by
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h | h
  · rw [Subgroup.index_eq_one] at h
    rw [h]
    exact le_top
  · have hcard : Nat.card (H ⧸ N) = 2 := by rwa [← Subgroup.index_eq_card]
    have : IsCyclic (H ⧸ N) := isCyclic_of_prime_card hcard
    have : IsMulCommutative (H ⧸ N) := IsCyclic.isMulCommutative
    let f : L →* H ⧸ N := (QuotientGroup.mk' N).comp L.subtype
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    have : Subsingleton f.range := inferInstance
    intro x hx
    have hfx : f ⟨x, hx⟩ = 1 :=
      congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨x, hx⟩) 1)
    exact (QuotientGroup.eq_one_iff (N := N) x).mp hfx

private theorem le_of_normal_of_ne_bot (hN : FStarSimple N) {M : Subgroup H} (hM : M.Normal)
    (hne : M ≠ ⊥) : N ≤ M := by
  have := hN.isSimpleGroup
  have := hN.normal
  have := hM
  have : (M.subgroupOf N).Normal := hM.subgroupOf N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf N) with h | h
  · exfalso
    have hdis : Disjoint M N := Subgroup.subgroupOf_eq_bot.1 h
    have hcomm : ⁅M, N⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_le_inf M N).trans (disjoint_iff.1 hdis).le)
    have hMC : M ≤ centralizer (N : Set H) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hMN : M ≤ N := hMC.trans hN.centralizer_le
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ M ⊓ N := ⟨hx, hMN hx⟩
    rwa [disjoint_iff.1 hdis] at this
  · exact Subgroup.subgroupOf_eq_top.1 h

private theorem not_normal_of_centralizes_involution (hN : FStarSimple N)
    (hq : CFSG.IsQuasisimple ↥L) {t : H} (htC : t ∈ centralizer (L : Set H))
    (ht2 : orderOf t = 2) : ¬ L.Normal := by
  intro hLn
  have hLN : L = N := hN.eq_of_isComponent hq hLn.isSubnormal
  subst hLN
  have htN : t ∈ L := hN.centralizer_le htC
  have := hN.isSimpleGroup
  have hz : (⟨t, htN⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 htC g g.2)
  rcases (center ↥L).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.mem_bot] at hz
    have h1 : t = 1 := congrArg Subtype.val hz
    rw [h1, orderOf_one] at ht2
    omega
  · obtain ⟨a, b, hab⟩ := hN.nonabelian
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

theorem three_le_twoRank_quotient_center_of_odd {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card (center X))) (h : 3 ≤ CFSG.pRank 2 X) :
    3 ≤ CFSG.Open.twoRank (X ⧸ center X) := by
  have h1 := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
    (center X) (by rintro ⟨k, hk⟩; rw [hk] at hodd; exact absurd hodd (by simp))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  unfold CFSG.Open.twoRank
  rw [h1]
  exact h

theorem card_sylow_eq_two_of_finkelstein_of_lemma25 (h25 : Asc76Lemma25)
    (hN : FStarSimple N) (hidx : N.index ≤ 2) (hstd : SolStd L) (hq : CFSG.IsQuasisimple ↥L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S)
    (hI : HypothesisOne (↥L ⧸ center ↥L)) (hr : 3 ≤ CFSG.Open.twoRank (↥L ⧸ center ↥L))
    {t : H} (htC : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) :
    ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2 := by
  intro S
  have hO : CFSG.Assembly.oddCore H = ⊥ := hN.oddCore_eq_bot
  have hev : Even (Nat.card (centralizer (L : Set H))) :=
    CFSG.StandardSubgroupAPI.even_card_of_mem_of_orderOf_eq_two htC ht2
  have hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L :=
    (standardComponentIsStandard_iff_stdBare).2 ⟨⟨hq.1.commutator_eq_top, hq.2.1⟩, hev, hstd.1⟩
  have hS : IsCyclic ↥S := by
    obtain ⟨S₀, hS₀⟩ := hcyc
    exact (MulEquiv.isCyclic (Sylow.equiv S S₀)).mpr hS₀
  have hnot : ¬ L.Normal := not_normal_of_centralizes_involution hN hq htC ht2
  have hLX : ¬ L.Normal → ∀ y ∈ centralizer (L : Set H), orderOf y = 2 →
      L ≤ normalClosure {y} := by
    intro _ y _ hy2
    have hy1 : y ≠ 1 := fun h => by
      rw [h, orderOf_one] at hy2
      omega
    have hNn : N.Normal := hN.normal
    refine (le_of_perfect_of_index_le_two_fin hidx hq.1).trans (le_of_normal_of_ne_bot hN
      (normalClosure_normal) fun h => hy1 ?_)
    have : y ∈ normalClosure ({y} : Set H) := subset_normalClosure rfl
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  exact card_sylow_eq_two_of_not_normal_of_lemma25 hO hL S hS hI hr h25 hLX hnot

theorem card_sylow_eq_two_of_finkelstein_of_lemma25_of_pRank (h25 : Asc76Lemma25)
    (hN : FStarSimple N) (hidx : N.index ≤ 2) (hstd : SolStd L) (hq : CFSG.IsQuasisimple ↥L)
    (hodd : Odd (Nat.card (center ↥L)))
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S)
    (hI : HypothesisOne (↥L ⧸ center ↥L)) (hr : 3 ≤ CFSG.pRank 2 ↥L)
    {t : H} (htC : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) :
    ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2 :=
  card_sylow_eq_two_of_finkelstein_of_lemma25 h25 hN hidx hstd hq hcyc hI
    (three_le_twoRank_quotient_center_of_odd hodd hr) htC ht2

end CFSG.EvenSporadicStandard.Induction
