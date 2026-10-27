module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LieType.Simplicity.Classical
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem oddCore_le_center_of_isQuasisimple [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (hne : oddCore Y ≠ ⊤) : oddCore Y ≤ center Y := by
  have hOpen : CFSG.Open.IsQuasisimple ↥Y := ⟨Group.isPerfect_def.mp hY.1, hY.2.1⟩
  exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hOpen
    (oddCore ↥Y) hne

theorem ctrQ_eq_card_quotient_center_oddCore [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (hne : oddCore Y ≠ ⊤) :
    ctrQ Y = Nat.card ((Y ⧸ oddCore Y) ⧸ center (Y ⧸ oddCore Y)) := by
  let N : Subgroup ↥Y := oddCore ↥Y
  haveI : N.Normal := oddCore_normal ↥Y
  let Q := ↥Y ⧸ N
  let q : ↥Y →* Q := QuotientGroup.mk' N
  have hle : N ≤ Subgroup.center ↥Y := oddCore_le_center_of_isQuasisimple hY hne
  haveI : Group.IsPerfect ↥Y := hY.1
  have hcenter : (Subgroup.center ↥Y).map q = Subgroup.center Q :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel q
      (QuotientGroup.mk'_surjective N)
      (by rw [show q.ker = N from QuotientGroup.ker_mk' N]; exact hle)
  have e1 : Q ⧸ (Subgroup.center ↥Y).map q ≃* ↥Y ⧸ Subgroup.center ↥Y :=
    QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center ↥Y) hle
  have e2 : Q ⧸ (Subgroup.center ↥Y).map q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  show ctrQ Y = Nat.card (Q ⧸ Subgroup.center Q)
  calc ctrQ Y = Nat.card (↥Y ⧸ Subgroup.center ↥Y) := rfl
    _ = Nat.card (Q ⧸ (Subgroup.center ↥Y).map q) := (Nat.card_congr e1.toEquiv).symm
    _ = Nat.card (Q ⧸ Subgroup.center Q) := Nat.card_congr e2.toEquiv

theorem center_eq_oddCore_of_simple [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (hs : IsSimpleGroup (Y ⧸ oddCore Y)) : center Y = oddCore Y := by
  haveI : IsSimpleGroup (↥Y ⧸ oddCore ↥Y) := hs
  have hle : oddCore ↥Y ≤ Subgroup.center ↥Y := by
    refine oddCore_le_center_of_isQuasisimple hY ?_
    intro htop
    exact (not_subsingleton (↥Y ⧸ oddCore ↥Y))
      ((QuotientGroup.subsingleton_iff).mpr htop)
  refine le_antisymm ?_ hle
  let q : ↥Y →* (↥Y ⧸ oddCore ↥Y) := QuotientGroup.mk' (oddCore ↥Y)
  have hcenterQ : Subgroup.center (↥Y ⧸ oddCore ↥Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥Y ⧸ oddCore ↥Y)) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative (↥Y ⧸ oddCore ↥Y) := Subgroup.center_eq_top_iff.mp h
      haveI : Group.IsPerfect ↥Y := hY.1
      haveI : Group.IsPerfect (↥Y ⧸ oddCore ↥Y) := inferInstance
      exact Group.IsPerfect.not_isMulCommutative (↥Y ⧸ oddCore ↥Y) inferInstance
  intro x hx
  have hxq : q x ∈ Subgroup.center (↥Y ⧸ oddCore ↥Y) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (oddCore ↥Y) y
    rw [← map_mul q z x, ← map_mul q x z, Subgroup.mem_center_iff.mp hx z]
  have hx1 : q x = 1 := by
    have hmem : q x ∈ (⊥ : Subgroup (↥Y ⧸ oddCore ↥Y)) := hcenterQ ▸ hxq
    simpa using hmem
  rw [← QuotientGroup.ker_mk' (N := oddCore ↥Y)]
  exact MonoidHom.mem_ker.mpr hx1

theorem ctrQ_eq_card_of_simple [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (hs : IsSimpleGroup (Y ⧸ oddCore Y)) : ctrQ Y = Nat.card (Y ⧸ oddCore Y) := by
  unfold ctrQ
  rw [center_eq_oddCore_of_simple hY hs]

private theorem ctrQ_of_classical_model [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    {t : CFSG.Open.StatedLieTag} {n f N : ℕ}
    (hmodel : CFSG.Open.StatedClassicalModel (Y ⧸ oddCore Y) t n 3 f)
    (hN : Nat.card (Y ⧸ oddCore Y) = N) : ctrQ Y = N := by
  have hs : IsSimpleGroup (Y ⧸ oddCore Y) :=
    (CFSG.LieType.Simplicity.fam_classical_converse (Y ⧸ oddCore Y)
      ⟨t, n, 3, f, hmodel⟩).2.2
  rw [ctrQ_eq_card_of_simple hY hs, hN]

theorem ctrQ_of_psp4 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .PSp 2 3 1) : ctrQ Y = 25920 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.2.1 rfl]
    decide +kernel)

theorem ctrQ_of_l43 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .PSL 4 3 1) : ctrQ Y = 6065280 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).1 rfl]
    decide +kernel)

theorem ctrQ_of_u43 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .PSU 4 3 1) : ctrQ Y = 3265920 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.1 rfl]
    decide +kernel)

theorem ctrQ_of_twoU43 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : IsTwoU43 (Y ⧸ oddCore Y)) : ctrQ Y = 3265920 := by
  have hne : oddCore ↥Y ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥Y ⧸ oddCore ↥Y) := (QuotientGroup.subsingleton_iff).mpr htop
    haveI : Finite (↥Y ⧸ oddCore ↥Y) := inferInstance
    have h1 : Nat.card (Subgroup.center (↥Y ⧸ oddCore ↥Y)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    have h2 : Nat.card (Subgroup.center (↥Y ⧸ oddCore ↥Y)) = 2 := h.1
    omega
  rw [ctrQ_eq_card_quotient_center_oddCore hY hne]
  have hq : Nat.card ((↥Y ⧸ oddCore ↥Y) ⧸ Subgroup.center (↥Y ⧸ oddCore ↥Y)) = 3265920 := by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two
      (G := (↥Y ⧸ oddCore ↥Y) ⧸ Subgroup.center (↥Y ⧸ oddCore ↥Y))
      (show (3 : ℕ) ≠ 2 by norm_num)
      (h.2.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
    decide +kernel
  exact hq

theorem ctrQ_of_omega7 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .POmegaOdd 3 3 1) : ctrQ Y = 4585351680 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.2.2.1 rfl]
    decide +kernel)

theorem ctrQ_of_omega8plus [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .POmegaPlus 4 3 1) : ctrQ Y = 4952179814400 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.2.2.2.1 rfl]
    decide +kernel)

theorem ctrQ_of_omega8minus [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .POmegaMinus 4 3 1) : ctrQ Y = 10151968619520 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.2.2.2.2 rfl]
    decide +kernel)

theorem ctrQ_of_l29 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .PSL 2 3 2) : ctrQ Y = 360 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).1 rfl]
    decide +kernel)

theorem ctrQ_of_l281 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .PSL 2 3 4) : ctrQ Y = 265680 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).1 rfl]
    decide +kernel)

theorem ctrQ_of_l33 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .PSL 3 3 1) : ctrQ Y = 5616 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).1 rfl]
    decide +kernel)

theorem ctrQ_of_u33 [Finite G] {Y : Subgroup G} (hY : IsQuasisimple Y)
    (h : LieModel (Y ⧸ oddCore Y) .PSU 3 3 1) : ctrQ Y = 6048 := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ctrQ_of_classical_model hY hmodel (by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y ⧸ oddCore Y)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.1 rfl]
    decide +kernel)

theorem ctrQ_cases_of_inFStar [Finite G] {Y : Subgroup G} (h : InFStar Y) :
    (LieModel (Y ⧸ oddCore Y) .PSp 2 3 1 ∧ ctrQ Y = 25920) ∨
    (LieModel (Y ⧸ oddCore Y) .PSL 4 3 1 ∧ ctrQ Y = 6065280) ∨
    ((LieModel (Y ⧸ oddCore Y) .PSU 4 3 1 ∨ IsTwoU43 (Y ⧸ oddCore Y)) ∧ ctrQ Y = 3265920) ∨
    (LieModel (Y ⧸ oddCore Y) .POmegaOdd 3 3 1 ∧ ctrQ Y = 4585351680) ∨
    (LieModel (Y ⧸ oddCore Y) .POmegaPlus 4 3 1 ∧ ctrQ Y = 4952179814400) ∨
    (LieModel (Y ⧸ oddCore Y) .POmegaMinus 4 3 1 ∧ ctrQ Y = 10151968619520) ∨
    (LieModel (Y ⧸ oddCore Y) .PSL 2 3 2 ∧ ctrQ Y = 360) ∨
    (LieModel (Y ⧸ oddCore Y) .PSL 2 3 4 ∧ ctrQ Y = 265680) ∨
    (LieModel (Y ⧸ oddCore Y) .PSL 3 3 1 ∧ ctrQ Y = 5616) ∨
    (LieModel (Y ⧸ oddCore Y) .PSU 3 3 1 ∧ ctrQ Y = 6048) := by
  unfold InFStar IsFStarGroup at h
  rcases h with hF | ⟨hY, hstar⟩
  · unfold IsFGroup at hF
    obtain ⟨hY, hQ⟩ := hF
    rcases hQ with hOmega | hTwo
    · unfold SmallF3OmegaQuotient at hOmega
      rcases hOmega with h | h | h | h | h | h
      · left; exact ⟨h, ctrQ_of_psp4 hY h⟩
      · right; left; exact ⟨h, ctrQ_of_l43 hY h⟩
      · right; right; left; exact ⟨Or.inl h, ctrQ_of_u43 hY h⟩
      · right; right; right; left; exact ⟨h, ctrQ_of_omega7 hY h⟩
      · right; right; right; right; left; exact ⟨h, ctrQ_of_omega8plus hY h⟩
      · right; right; right; right; right; left; exact ⟨h, ctrQ_of_omega8minus hY h⟩
    · right; right; left; exact ⟨Or.inr hTwo, ctrQ_of_twoU43 hY hTwo⟩
  · unfold SmallF3StarQuotient at hstar
    rcases hstar with h | h | h | h
    · right; right; right; right; right; right; left; exact ⟨h, ctrQ_of_l29 hY h⟩
    · right; right; right; right; right; right; right; left; exact ⟨h, ctrQ_of_l281 hY h⟩
    · right; right; right; right; right; right; right; right; left; exact ⟨h, ctrQ_of_l33 hY h⟩
    · right; right; right; right; right; right; right; right; right; exact ⟨h, ctrQ_of_u33 hY h⟩

end CFSG.OddStandard.SmallF3.Omega
