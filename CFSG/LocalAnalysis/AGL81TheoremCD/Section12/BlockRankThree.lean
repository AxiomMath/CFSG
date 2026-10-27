module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockOrderThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BarBlocks
import CFSG.LocalAnalysis.SectionRank.CommutingRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


theorem pRank_three_barM_add_ncard_le
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h : TwelveCtx G M p Q H) {L₀ : Subgroup G} (hL₀ : L₀ ∈ weakBlockSet M H) :
    CFSG.Open.pRank 3 (barM M L₀) + (weakBlockSet M H).ncard ≤ CFSG.Open.pRank 3 M + 1 := by
  classical
  let ι := ↥(weakBlockSet M H \ {L₀})
  let L : ι → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := fun i => barM M (i.1 : Subgroup G)
  have h₀ : ∀ i, L i ≤
      Subgroup.centralizer (barM M L₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun i => barM_le_centralizer_barM_of_ne i.2.1 hL₀ (by simpa using i.2.2)
  have hcomm : ∀ i j, i ≠ j →
      L i ≤ Subgroup.centralizer (L j : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun i j hij => barM_le_centralizer_barM_of_ne i.2.1 j.2.1
      (fun hval => hij (Subtype.ext hval))
  obtain ⟨E, hEL₀, hE, hk⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (barM M L₀)
  choose t ht using fun i : ι =>
    exists_orderOf_three_not_mem_centralizer_barM h1 h2 h25 h i.2.1
  have htL : ∀ i, t i ∈ L i := fun i => (ht i).1
  have hto : ∀ i, orderOf (t i) = 3 := fun i => (ht i).2.1
  have htZ : ∀ i, t i ∉ Subgroup.centralizer (L i : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun i => (ht i).2.2
  have hmain := CFSG.SectionRank.pRank_add_card_le_of_commuting
    (q := 3) Nat.prime_three (barM M L₀) L h₀ hcomm E hE hEL₀ hk t htL hto htZ
  have hι : Nat.card ι = (weakBlockSet M H).ncard - 1 := by
    change Nat.card ↥(weakBlockSet M H \ {L₀}) = _
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hL₀]
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) =
      CFSG.Open.pRank 3 M := by
    have hM : barM M M = ⊤ := by
      rw [barM, Subgroup.subgroupOf_self]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [← hM]
    exact CFSG.AGLEmbedding.pRank_barM_eq Nat.prime_three (by norm_num) M M le_rfl
  have hsub : CFSG.Open.pRank 3 (barM M L₀) + ((weakBlockSet M H).ncard - 1) ≤
      CFSG.Open.pRank 3 M := by
    rw [← hι, ← htop]
    exact hmain
  have hn : 1 ≤ (weakBlockSet M H).ncard := by
    have hpos : 0 < (weakBlockSet M H).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨L₀, hL₀⟩
    omega
  have := Nat.add_le_add_right hsub 1
  rwa [Nat.add_assoc, Nat.sub_add_cancel hn] at this

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
