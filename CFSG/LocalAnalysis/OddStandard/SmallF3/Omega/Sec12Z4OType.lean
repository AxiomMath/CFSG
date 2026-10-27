module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L101

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem z4o_isQuasisimple_of_inFStar [Finite G] {Y : Subgroup G} (hY : InFStar Y) :
    IsQuasisimple Y := by
  unfold InFStar IsFStarGroup IsFGroup at hY
  rcases hY with h | h
  · exact h.1
  · exact h.1

theorem z4o_inF_of_inFStar_of_ctrQ_gt [Finite G] {Y : Subgroup G} (hY : InFStar Y)
    (hgt : 265680 < ctrQ Y) : InF Y := by
  have hq : IsQuasisimple Y := z4o_isQuasisimple_of_inFStar hY
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

theorem z4o_sec3SettingLB [Finite G] {t y : G} {L Y : Subgroup G} (hS : Sec3SettingLB G t L)
    (hy : orderOf y = 2) (hY : IsComponentIn Y (centralizer ({y} : Set G))) (hYF : InF Y) :
    Sec3SettingLB G y Y :=
  { simple := hS.simple, a1 := hS.a1, a2 := hS.a2, notChev3 := hS.notChev3
    involution := hy, component := hY, inF := hYF, lBalance := hS.lBalance
    kProper := hS.kProper, notCat := hS.notCat }

theorem sec123z4_type [Finite G] (h6p : AschOmega6Plus) (h6m : AschOmega6Minus)
    (h7 : AschOmega7) (h8p : AschOmega8Plus) (h8m : AschOmega8Minus)
    (h6z : AschOmega6MinusZ2) {t s : G} {L I : Subgroup G} (hS : Sec3SettingLB G t L)
    (hs : orderOf s = 2) (hI : IsComponentIn I (centralizer ({s} : Set G)))
    (hIF : InFStar I) (h360 : 360 ∣ ctrQ I) :
    IsOmega5 I ∨ IsL29 I ∨ IsL281 I := by
  rcases ctrQ_cases_of_inFStar hIF with
    ⟨h, _⟩ | ⟨hm, hc⟩ | ⟨hm, hc⟩ | ⟨hm, hc⟩ | ⟨hm, hc⟩ | ⟨hm, hc⟩ |
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · exact Or.inl h
  · exact (h6p G s I (z4o_sec3SettingLB hS hs hI
      (z4o_inF_of_inFStar_of_ctrQ_gt hIF (by rw [hc]; norm_num))) hm).elim
  · have hF := z4o_inF_of_inFStar_of_ctrQ_gt hIF (by rw [hc]; norm_num)
    rcases hm with hm | hz
    · exact (h6m G s I (z4o_sec3SettingLB hS hs hI hF) hm).elim
    · exact (h6z G s I (z4o_sec3SettingLB hS hs hI hF) hz).elim
  · exact (h7 G s I (z4o_sec3SettingLB hS hs hI
      (z4o_inF_of_inFStar_of_ctrQ_gt hIF (by rw [hc]; norm_num))) hm).elim
  · exact (h8p G s I (z4o_sec3SettingLB hS hs hI
      (z4o_inF_of_inFStar_of_ctrQ_gt hIF (by rw [hc]; norm_num))) hm).elim
  · exact (h8m G s I (z4o_sec3SettingLB hS hs hI
      (z4o_inF_of_inFStar_of_ctrQ_gt hIF (by rw [hc]; norm_num))) hm).elim
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · rw [hc] at h360; exact absurd h360 (by norm_num)
  · rw [hc] at h360; exact absurd h360 (by norm_num)

theorem inCStar_of_isOmega5 [Finite G] (h6p : AschOmega6Plus) (h6m : AschOmega6Minus)
    (h7 : AschOmega7) (h8p : AschOmega8Plus) (h8m : AschOmega8Minus)
    (h6z : AschOmega6MinusZ2) {t s : G} {L I : Subgroup G} (hS : Sec3SettingLB G t L)
    (hs : orderOf s = 2) (hI : IsComponentIn I (centralizer ({s} : Set G)))
    (hIF : InFStar I) (h5 : IsOmega5 I) : InCStar I :=
  asc82Lemma101_of h6p h6m h7 h8p h8m h6z G s I
    { toSec3SettingLB := z4o_sec3SettingLB hS hs hI
        ⟨z4o_isQuasisimple_of_inFStar hIF, Or.inl (Or.inl h5)⟩
      psp4 := h5 }

theorem inCStar_of_isL281 [Finite G] (h8m : AschOmega8Minus) {t : G} {L I : Subgroup G}
    (hS : Sec3SettingLB G t L) (hI : InC I) (hIF : InFStar I) (h81 : IsL281 I) :
    InCStar I := by
  have hIq : ctrQ I = 265680 := ctrQ_of_l281 (z4o_isQuasisimple_of_inFStar hIF) h81
  refine inCStar_of_ctrQ_maximal hS.a2 hI hIF ?_
  intro Y hC hYF hdvd
  obtain ⟨y, hy2, hYc⟩ := hC
  rw [hIq] at hdvd ⊢
  rcases ctrQ_cases_of_inFStar hYF with
    ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨hm, hc⟩ |
      ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)
  · exact (h8m G y Y (z4o_sec3SettingLB hS hy2 hYc
      (z4o_inF_of_inFStar_of_ctrQ_gt hYF (by rw [hc]; norm_num))) hm).elim
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)
  · exact hc
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)
  · rw [hc] at hdvd; exact absurd hdvd (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
