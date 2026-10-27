module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3BenderParab
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ParabolicGlue
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Aux
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KCRMain
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open scoped MatrixGroups
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection KxSection IsParabolicTwo)

section Certificates


theorem kFactParabolicSectionThree_holds : KFactParabolicSectionThree := by
  intro A _ _ K K₀ z hK hrk hL3 hz3 hzK₀ hpar hne hSyl
  obtain ⟨hK₀K, U, hUsyl, hUN⟩ := hpar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : z ∈ K := hK₀K hzK₀
  set zK : ↥K := ⟨z, hzK⟩ with hzKdef
  have hzKord : orderOf zK = 3 := by
    rw [hzKdef, Subgroup.orderOf_mk]
    exact hz3
  have hsimple : IsSimpleGroup ↥K := isSimpleGroup_of_isChevSimple_two hK
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hnc'
    have hcomm : ∀ a b : ↥K, a * b = b * a := fun a b => by_contra fun h => hnc' ⟨a, b, h⟩
    letI : CommGroup ↥K := { (inferInstance : Group ↥K) with mul_comm := hcomm }
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers zK) with h | h
    · rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hzKord
      omega
    · apply hne
      refine le_antisymm hK₀K fun x hx => ?_
      have hx' : (⟨x, hx⟩ : ↥K) ∈ zpowers zK := h ▸ mem_top _
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx'
      have hxk : x = z ^ k := (congrArg Subtype.val hk).symm
      rw [hxk]
      exact zpow_mem hzK₀ k
  have hchev := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.isChevTwo_of_isChevSimple_two hK
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 1 := by
    have h1 : CFSG.Open.pRank 3 K = CFSG.pRank 3 ↥K :=
      (CFSG.SectionRank.pRank_coe_eq_openPRank 3 K).symm
    have h2 : CFSG.pRank 3 ↥K = CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
      CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥K
    rw [← h2, ← h1]
    exact hrk
  have hrk1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 1 :=
    le_antisymm hrk' (one_le_pRank_of_orderOf_eq_prime zK hzKord)
  by_cases hB : CFSG.Open.fusionIsBenderGroup ↥K
  · exact (false_of_bender_parabolic K K₀ U hB hUsyl hUN hK₀K hne hSyl).elim
  obtain ⟨n, hnodd, ⟨φ⟩⟩ :=
    Parrott.P614.kFactChevTwoRankOneThree_holds ↥K hsimple hnc hchev hrk1 hB
  have hn1 : n ≠ 1 := by
    rintro rfl
    obtain ⟨ψ⟩ := nonempty_psl_three_galoisField_two_one_equiv
    exact hL3 ⟨φ.trans ψ⟩
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hnodd
    omega
  obtain ⟨Q, hQ⟩ := hUsyl.exists_sylow_eq_subgroupOf
  have hQN : normalizer ((Q : Subgroup ↥K) : Set ↥K) ≤ K₀.subgroupOf K := by
    rw [hQ, ← subgroupOf_normalizer_eq hUsyl.le]
    intro x hx
    exact hUN ⟨hx, x.2⟩
  have hne' : K₀.subgroupOf K ≠ ⊤ := by
    intro h
    apply hne
    rw [subgroupOf_eq_top] at h
    exact le_antisymm hK₀K h
  obtain ⟨H, N, hHK₀, hsec, hzH, hzN, h3⟩ :=
    parabolic_section_of_psl3 hnodd hn3 φ Q (K₀.subgroupOf K) hQN hne' hzKord hzK₀
  refine ⟨H.map K.subtype, N.map K.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact hHK₀ hy
  · exact isSimpleSection_map_injective K.subtype K.subtype_injective hsec
  · exact ⟨zK, hzH, rfl⟩
  · intro hzmem
    obtain ⟨y, hy, hyz⟩ := mem_map.mp hzmem
    exact hzN ((Subtype.ext hyz : y = zK) ▸ hy)
  · rw [relIndex_map_map_of_injective N H K.subtype_injective]
    exact h3

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
