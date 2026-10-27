module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem isQuasisimple_of_inFStar [Finite G] {Y : Subgroup G} (hY : InFStar Y) :
    IsQuasisimple Y := by
  unfold InFStar IsFStarGroup IsFGroup at hY
  rcases hY with h | h
  · exact h.1
  · exact h.1

private theorem inF_of_inFStar_of_ctrQ_gt [Finite G] {Y : Subgroup G} (hY : InFStar Y)
    (hgt : 265680 < ctrQ Y) : InF Y := by
  have hq : IsQuasisimple Y := isQuasisimple_of_inFStar hY
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

theorem asc82Lemma101_of (h6p : AschOmega6Plus) (h6m : AschOmega6Minus) (h7 : AschOmega7)
    (h8p : AschOmega8Plus) (h8m : AschOmega8Minus) (h6z : AschOmega6MinusZ2) :
    Asc82Lemma101 := by
  intro G _ _ t L h
  have hLq : ctrQ L = 25920 := ctrQ_of_psp4 h.component.isQuasisimple h.psp4
  refine inCStar_of_ctrQ_maximal h.a2 ⟨t, h.involution, h.component⟩ (Or.inl h.inF) ?_
  intro Y hC hYF hdvd
  obtain ⟨y, hy2, hYc⟩ := hC
  have hpos : 0 < ctrQ Y := Nat.card_pos
  have hle : 25920 ≤ ctrQ Y := by
    rw [← hLq]
    exact Nat.le_of_dvd hpos hdvd
  rcases ctrQ_cases_of_inFStar hYF with
    ⟨_, hc⟩ | ⟨hmodel, hc⟩ | ⟨hmodel, hc⟩ | ⟨hmodel, hc⟩ | ⟨hmodel, hc⟩ | ⟨hmodel, hc⟩ |
      ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · rw [hc, hLq]
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt hYF (by rw [hc]; norm_num)
    exact h6p G y Y
      { simple := h.simple, a1 := h.a1, a2 := h.a2, notChev3 := h.notChev3
        involution := hy2, component := hYc, inF := hFY, lBalance := h.lBalance
        kProper := h.kProper, notCat := h.notCat } hmodel
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt hYF (by rw [hc]; norm_num)
    rcases hmodel with hm | hz
    · exact h6m G y Y
        { simple := h.simple, a1 := h.a1, a2 := h.a2, notChev3 := h.notChev3
          involution := hy2, component := hYc, inF := hFY, lBalance := h.lBalance
          kProper := h.kProper, notCat := h.notCat } hm
    · exact h6z G y Y
        { simple := h.simple, a1 := h.a1, a2 := h.a2, notChev3 := h.notChev3
          involution := hy2, component := hYc, inF := hFY, lBalance := h.lBalance
          kProper := h.kProper, notCat := h.notCat } hz
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt hYF (by rw [hc]; norm_num)
    exact h7 G y Y
      { simple := h.simple, a1 := h.a1, a2 := h.a2, notChev3 := h.notChev3
        involution := hy2, component := hYc, inF := hFY, lBalance := h.lBalance
        kProper := h.kProper, notCat := h.notCat } hmodel
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt hYF (by rw [hc]; norm_num)
    exact h8p G y Y
      { simple := h.simple, a1 := h.a1, a2 := h.a2, notChev3 := h.notChev3
        involution := hy2, component := hYc, inF := hFY, lBalance := h.lBalance
        kProper := h.kProper, notCat := h.notCat } hmodel
  · exfalso
    have hFY : InF Y := inF_of_inFStar_of_ctrQ_gt hYF (by rw [hc]; norm_num)
    exact h8m G y Y
      { simple := h.simple, a1 := h.a1, a2 := h.a2, notChev3 := h.notChev3
        involution := hy2, component := hYc, inF := hFY, lBalance := h.lBalance
        kProper := h.kProper, notCat := h.notCat } hmodel
  · rw [hLq, hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hLq, hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hLq, hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hLq, hc] at hdvd; exact absurd hdvd (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
