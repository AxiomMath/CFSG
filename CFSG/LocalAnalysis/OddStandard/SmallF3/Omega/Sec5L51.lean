module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem isQuasisimple_of_inFStar' [Finite G] {Y : Subgroup G} (hY : InFStar Y) :
    IsQuasisimple Y := by
  unfold InFStar IsFStarGroup IsFGroup at hY
  rcases hY with h | h
  · exact h.1
  · exact h.1

private theorem inF_of_inFStar_of_ctrQ_gt' [Finite G] {Y : Subgroup G} (hY : InFStar Y)
    (hgt : 265680 < ctrQ Y) : InF Y := by
  have hq : IsQuasisimple Y := isQuasisimple_of_inFStar' hY
  rcases ctrQ_cases_of_inFStar hY with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · exact ⟨hq, Or.inl (Or.inl h)⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inl h))⟩
  · rcases h with h | h
    · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨hq, Or.inr h⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))⟩
  · rw [hc] at hgt; exact absurd hgt (by norm_num)
  · rw [hc] at hgt; exact absurd hgt (by norm_num)
  · rw [hc] at hgt; exact absurd hgt (by norm_num)
  · rw [hc] at hgt; exact absurd hgt (by norm_num)

theorem asc82Lemma51_of (h7 : AschOmega7) (h38 : Asc82Lemma38) (h311 : Asc82Lemma311) :
    Asc82Lemma51 := by
  intro G _ _ t L h
  have hLq : ctrQ L = 3265920 := ctrQ_of_twoU43 h.component.isQuasisimple h.twoU43
  refine inCStar_of_ctrQ_maximal h.a2 ⟨t, h.involution, h.component⟩ (Or.inl h.inF) ?_
  intro Y hC hYF hdvd
  obtain ⟨y, hy2, hYc⟩ := hC
  have hpos : 0 < ctrQ Y := Nat.card_pos
  have hdvd' : 3265920 ∣ ctrQ Y := by rw [← hLq]; exact hdvd
  have hle : 3265920 ≤ ctrQ Y := Nat.le_of_dvd hpos hdvd'
  have hset : ∀ Y : Subgroup G, IsComponentIn Y (centralizer ({y} : Set G)) → InF Y →
      Sec3SettingLB G y Y := fun Y hYc hFY =>
    { simple := h.simple, a1 := h.a1, a2 := h.a2, notChev3 := h.notChev3
      involution := hy2, component := hYc, inF := hFY, lBalance := h.lBalance
      kProper := h.kProper, notCat := h.notCat }
  rcases ctrQ_cases_of_inFStar hYF with
    ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨h7Y, hc⟩ | ⟨hplus, hc⟩ | ⟨hminus, hc⟩ |
      ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · rw [hc] at hle; exact absurd hle (by norm_num)
  · rw [hc] at hdvd'; exact absurd hdvd' (by norm_num)
  · rw [hc, hLq]
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt' hYF (by rw [hc]; norm_num)
    exact h7 G y Y (hset Y hYc hFY) h7Y
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt' hYF (by rw [hc]; norm_num)
    exact h311 G y Y (hset Y hYc hFY) hplus
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt' hYF (by rw [hc]; norm_num)
    exact h38 G y Y (hset Y hYc hFY) hminus
  · rw [hc] at hle; exact absurd hle (by norm_num)
  · rw [hc] at hle; exact absurd hle (by norm_num)
  · rw [hc] at hle; exact absurd hle (by norm_num)
  · rw [hc] at hle; exact absurd hle (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
