module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627NotCaseOne

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem not_smallRankCaseOne (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (h614 : GL83SmallRankProp614 G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x : G}
    (hx : SmallRankPoint P M x) {T : Subgroup G} (hT : SmallRankSylowTwo P M T) :
    ¬ SmallRankCaseOne x T := by
  intro h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hbot
    have hx1 : x ∈ (P : Subgroup G) := hx.mem
    rw [hbot, Subgroup.mem_bot] at hx1
    exact hx.ne_one hx1
  obtain ⟨z, hzP, hzc, hzord⟩ := exists_mem_centralizer_orderOf_eq P.isPGroup' hPne
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzord
    exact absurd hzord.symm (by norm_num)
  have hzp : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hz : SmallRankCentral P z := ⟨hzP, hzc, hz1, hzp⟩
  obtain ⟨U, hU⟩ := exists_smallRankFourGroup_of_caseOne hS hU0 h614 hsit hx hz hT h1
  exact false_of_smallRankFourGroup hS hU0 hD2 h614 hsit hsolv e hx hz hU

theorem smallRankCaseTwo_of_prop627 (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) (h627 : GL83SmallRankProp627 G) (h614 : GL83SmallRankProp614 G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x : G}
    (hx : SmallRankPoint P M x) {T : Subgroup G} (hT : SmallRankSylowTwo P M T) :
    SmallRankCaseTwo M x T :=
  ((h627 3 P M hsit).2 x hx T hT).resolve_left
    (not_smallRankCaseOne hS hU0 hD2 h614 hsit hsolv e hx hT)

end CFSG.LocalAnalysis.RankThreeTheoremC
