module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem quasisimple_of_inFStar_w12 {Y : Subgroup G} (h : InFStar Y) : IsQuasisimple Y :=
  h.elim (fun h => h.1) (fun h => h.1)

theorem ctrQ_mem_of_inF [Finite G] {Y : Subgroup G} (h : InF Y) :
    ctrQ Y = 25920 ∨ ctrQ Y = 6065280 ∨ ctrQ Y = 3265920 ∨ ctrQ Y = 4585351680 ∨
      ctrQ Y = 4952179814400 ∨ ctrQ Y = 10151968619520 := by
  unfold InF IsFGroup at h
  obtain ⟨hY, hQ⟩ := h
  rcases hQ with hO | hT
  · unfold SmallF3OmegaQuotient at hO
    rcases hO with h | h | h | h | h | h
    · exact Or.inl (ctrQ_of_psp4 hY h)
    · exact Or.inr (Or.inl (ctrQ_of_l43 hY h))
    · exact Or.inr (Or.inr (Or.inl (ctrQ_of_u43 hY h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ctrQ_of_omega7 hY h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ctrQ_of_omega8plus hY h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ctrQ_of_omega8minus hY h)))))
  · exact Or.inr (Or.inr (Or.inl (ctrQ_of_twoU43 hY hT)))

theorem ctrQ_mem_of_isL3Eps3 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : IsL3Eps3 Y) : ctrQ Y = 5616 ∨ ctrQ Y = 6048 := by
  rcases h with h | h
  · exact Or.inl (ctrQ_of_l33 hY h)
  · exact Or.inr (ctrQ_of_u33 hY h)

theorem ctrQ_mem_of_pocketed [Finite G] {Y : Subgroup G} (hY : InFStar Y)
    (hpk : InF Y ∨ IsL3Eps3 Y) :
    ctrQ Y = 25920 ∨ ctrQ Y = 6065280 ∨ ctrQ Y = 3265920 ∨ ctrQ Y = 4585351680 ∨
      ctrQ Y = 4952179814400 ∨ ctrQ Y = 10151968619520 ∨ ctrQ Y = 5616 ∨ ctrQ Y = 6048 := by
  rcases hpk with h | h
  · rcases ctrQ_mem_of_inF h with h | h | h | h | h | h <;> omega
  · rcases ctrQ_mem_of_isL3Eps3 (quasisimple_of_inFStar_w12 hY) h with h | h <;> omega

theorem ctrQ_mem_of_not_pocketed [Finite G] {Y : Subgroup G} (hY : InFStar Y) (hF : ¬ InF Y)
    (hL : ¬ IsL3Eps3 Y) : ctrQ Y = 360 ∨ ctrQ Y = 265680 := by
  unfold InFStar IsFStarGroup at hY
  rcases hY with hF' | ⟨hq, hstar⟩
  · exact absurd hF' hF
  · unfold SmallF3StarQuotient at hstar
    rcases hstar with h | h | h | h
    · exact Or.inl (ctrQ_of_l29 hq h)
    · exact Or.inr (ctrQ_of_l281 hq h)
    · exact absurd (Or.inl h) hL
    · exact absurd (Or.inr h) hL

theorem ctrQ_ne_of_pocketed [Finite G] {X K : Subgroup G} (hX : InFStar X)
    (hpk : InF X ∨ IsL3Eps3 X) (hK : InFStar K) (hF : ¬ InF K) (hL : ¬ IsL3Eps3 K) :
    ctrQ X ≠ ctrQ K := by
  have h1 := ctrQ_mem_of_pocketed hX hpk
  have h2 := ctrQ_mem_of_not_pocketed hK hF hL
  omega

end CFSG.OddStandard.SmallF3.Omega
