module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem dConnected_of_hasLieType {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hconj : ConjInvariant Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z) (hne : Ω.Nonempty)
    {t : StatedLieTag} {n : ℕ} (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hsm : ¬ SmallModel t n)
    (h : HasLieType p f Ω t n) : DConnected Ω := by
  obtain ⟨D, hcard, i, hi, hn⟩ := h
  have M := D.toIh8Model hcard i hconj hcl hne
  rw [hi, hn] at M
  have hq' : 5 ≤ p ^ (D.exp i) := by rw [M.exp_eq_f hD4]; exact hq
  rcases ih8_tag_cases hp hq' M.isFundTag M.admissible hG2 hD4 with hconn | hsm'
  · exact M.dConnected_of_connected hp hq hne hG2 hD4 hconn
  · exact absurd hsm' hsm

theorem c26_L5_proved : C26_L5 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hL5
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hne : Ω.Nonempty := ⟨K, hs.stand.mem⟩
  unfold LFiveType at hL5
  split_ifs at hL5
  · exact dConnected_of_hasLieType hp hq hΩ.conjInvariant hΩ.classical hne (by simp) (by simp)
      (by simp [SmallModel]) hL5
  · exact dConnected_of_hasLieType hp hq hΩ.conjInvariant hΩ.classical hne (by simp) (by simp)
      (by simp [SmallModel]) hL5

end CFSG.ClassicalInvolution.Asc77
