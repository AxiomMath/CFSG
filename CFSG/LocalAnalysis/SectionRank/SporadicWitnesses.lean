module

public import CFSG.LocalAnalysis.SectionRank.SimpleList
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Suz
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi23
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi24prime
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Ly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HN
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Th
public import CFSG.LocalAnalysis.SectionRank.Sporadic.B

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint

theorem exists_rank_ge_three_of_four {T : Type} [Group T]
    (h : ∃ E : Subgroup T, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) :
    ∃ E : Subgroup T, IsElemAbelian 3 E ∧ ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k :=
  let ⟨E, hE, hc⟩ := h
  ⟨E, hE, 4, by norm_num, hc⟩

theorem sporadicThreeRankWitnesses :
    SporadicThreeRankWitnesses := by
  intro s hs hM
  cases s with
  | M11 | M12 | M22 | M23 | M24 | J1 | J2 | J4 | HS | He | Ru =>
    exact absurd (by simp [sqtkSporadicNames]) hs
  | M => exact absurd rfl hM
  | J3 =>
    obtain ⟨E, hE, hc⟩ := J3_elementary_three_rank_three
    exact ⟨E, hE, 3, le_rfl, hc⟩
  | McL => exact exists_rank_ge_three_of_four McL_elementary_three_rank_four
  | Suz => exact exists_rank_ge_three_of_four Suz_elementary_three_rank_four
  | ONan => exact exists_rank_ge_three_of_four ON_elementary_three_rank_four
  | Co1 => exact exists_rank_ge_three_of_four Co1_elementary_three_rank_four
  | Co2 => exact exists_rank_ge_three_of_four Co2_elementary_three_rank_four
  | Co3 => exact exists_rank_ge_three_of_four Co3_elementary_three_rank_four
  | Fi22 => exact exists_rank_ge_three_of_four Fi22_elementary_three_rank_four
  | Fi23 => exact exists_rank_ge_three_of_four Fi23_elementary_three_rank_four
  | Fi24Prime => exact exists_rank_ge_three_of_four Fi24prime_elementary_three_rank_four
  | HN => exact exists_rank_ge_three_of_four HN_elementary_three_rank_four
  | Ly => exact exists_rank_ge_three_of_four Ly_elementary_three_rank_four
  | Th => exact exists_rank_ge_three_of_four Th_elementary_three_rank_four
  | B => exact exists_rank_ge_three_of_four B_elementary_three_rank_four

end CFSG.SectionRank
