module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Transport
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem centralizer_pair_le_left (x y : G) :
    Subgroup.centralizer ({x, y} : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
  Subgroup.centralizer_le (by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact Set.mem_insert x {y})

private theorem le_centralizer_pair {K : Subgroup G} {x y : G}
    (hx : K ≤ Subgroup.centralizer ({x} : Set G))
    (hy : K ≤ Subgroup.centralizer ({y} : Set G)) :
    K ≤ Subgroup.centralizer ({x, y} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with hwx | hwy
  · rw [hwx]
    exact Subgroup.mem_centralizer_iff.mp (hx hz) x (Set.mem_singleton x)
  · rw [hwy]
    exact Subgroup.mem_centralizer_iff.mp (hy hz) y (Set.mem_singleton y)

theorem inFStar_of_inF {X : Subgroup G} (h : InF X) : InFStar X :=
  Or.inl h

theorem card_quotient_oddCore_of_isFStarGroup_not_isFGroup {L : Type} [Group L] [Finite L]
    (hS : IsFStarGroup L) (hF : ¬ IsFGroup L) :
    Nat.card (L ⧸ oddCore L) = 360 ∨ Nat.card (L ⧸ oddCore L) = 265680 ∨
      Nat.card (L ⧸ oddCore L) = 5616 ∨ Nat.card (L ⧸ oddCore L) = 6048 := by
  unfold IsFStarGroup at hS
  rcases hS with hFg | ⟨-, hQ⟩
  · exact absurd hFg hF
  · unfold SmallF3StarQuotient at hQ
    rcases hQ with h | h | h | h
    · left
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
      decide +kernel
    · right; left
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
      decide +kernel
    · right; right; left
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
      decide +kernel
    · right; right; right
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
      decide +kernel

private theorem not_dvd_of_isFGroup_order {a n : ℕ}
    (ha : a ∈ ({25920, 6065280, 3265920, 4585351680, 4952179814400, 10151968619520,
      6531840} : Finset ℕ))
    (hn : n = 360 ∨ n = 265680 ∨ n = 5616 ∨ n = 6048) : ¬ a ∣ n := by
  rintro hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl | rfl <;>
    exact absurd hdvd (by decide +kernel)

theorem not_card_quotient_oddCore_dvd_of_isFGroup {L : Type} [Group L] [Finite L]
    (hF : IsFGroup L) {n : ℕ} (hn : n = 360 ∨ n = 265680 ∨ n = 5616 ∨ n = 6048) :
    ¬ Nat.card (L ⧸ oddCore L) ∣ n := by
  rintro hdvd
  unfold IsFGroup at hF
  obtain ⟨-, hQ⟩ := hF
  rcases hQ with h | h
  · unfold SmallF3OmegaQuotient at h
    rcases h with h | h | h | h | h | h
    · have hcard : Nat.card (L ⧸ oddCore L) = 25920 := by
        rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
          (show (3 : ℕ) ≠ 2 by norm_num)
          (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.1 rfl]
        decide +kernel
      exact (not_dvd_of_isFGroup_order (by simp [hcard]) hn) hdvd
    · have hcard : Nat.card (L ⧸ oddCore L) = 6065280 := by
        rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
          (show (3 : ℕ) ≠ 2 by norm_num)
          (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
        decide +kernel
      exact (not_dvd_of_isFGroup_order (by simp [hcard]) hn) hdvd
    · have hcard : Nat.card (L ⧸ oddCore L) = 3265920 := by
        rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
          (show (3 : ℕ) ≠ 2 by norm_num)
          (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
        decide +kernel
      exact (not_dvd_of_isFGroup_order (by simp [hcard]) hn) hdvd
    · have hcard : Nat.card (L ⧸ oddCore L) = 4585351680 := by
        rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
          (show (3 : ℕ) ≠ 2 by norm_num)
          (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.1 rfl]
        decide +kernel
      exact (not_dvd_of_isFGroup_order (by simp [hcard]) hn) hdvd
    · have hcard : Nat.card (L ⧸ oddCore L) = 4952179814400 := by
        rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
          (show (3 : ℕ) ≠ 2 by norm_num)
          (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.1 rfl]
        decide +kernel
      exact (not_dvd_of_isFGroup_order (by simp [hcard]) hn) hdvd
    · have hcard : Nat.card (L ⧸ oddCore L) = 10151968619520 := by
        rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
          (show (3 : ℕ) ≠ 2 by norm_num)
          (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.2 rfl]
        decide +kernel
      exact (not_dvd_of_isFGroup_order (by simp [hcard]) hn) hdvd
  · unfold IsTwoU43 at h
    obtain ⟨hcenter, hmodel⟩ := h
    have hq : Nat.card ((L ⧸ oddCore L) ⧸ center (L ⧸ oddCore L)) = 3265920 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two
        (G := (L ⧸ oddCore L) ⧸ center (L ⧸ oddCore L))
        (show (3 : ℕ) ≠ 2 by norm_num)
        (hmodel.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
      decide +kernel
    have hcard : Nat.card (L ⧸ oddCore L) = 6531840 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (L ⧸ oddCore L)), hq, hcenter]
    exact (not_dvd_of_isFGroup_order (by simp [hcard]) hn) hdvd

theorem inF_of_le_of_inFStar [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y) (hX : InF X)
    (hY : InFStar Y) : InF Y := by
  by_contra hF
  exact not_card_quotient_oddCore_dvd_of_isFGroup hX
    (card_quotient_oddCore_of_isFStarGroup_not_isFGroup hY hF)
    (card_quotient_oddCore_dvd hXY)

theorem inFStar_of_walterArrow (hA : AschA2 G) {X Y : Subgroup G} (h : WalterArrow X Y)
    (hX : InFStar X) : InFStar Y := by
  unfold WalterArrow at h
  obtain ⟨x, y, hx, hy, hxy, hXc, hYc, hXY, -⟩ := h
  exact hA x y hx hy hxy X Y
    (hXc.mono (le_centralizer_pair hXc.le (hXY.trans hYc.le)) (centralizer_pair_le_left x y))
    hYc (hXY.trans le_sup_left) hX

theorem inFStar_of_walterArrowDiag (hA : AschA2 G) {X Y : Subgroup G} (h : WalterArrowDiag X Y)
    (hX : InFStar X) : InFStar Y := by
  unfold WalterArrowDiag at h
  obtain ⟨x, y, hx, hy, hxy, hXc, hYc, hle, -⟩ := h
  have hxCy : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hxy.symm
  have hconj : IsComponentIn (CFSG.conjugate Y x) (Subgroup.centralizer ({y} : Set G)) :=
    hYc.conjugate hxCy
  have hXCy : X ≤ Subgroup.centralizer ({y} : Set G) := hle.trans (sup_le hYc.le hconj.le)
  exact hA x y hx hy hxy X Y
    (hXc.mono (le_centralizer_pair hXc.le hXCy) (centralizer_pair_le_left x y))
    hYc hle hX

theorem inFStar_of_walterChain (hA : AschA2 G) {X Y : Subgroup G} (h : WalterChain X Y)
    (hX : InFStar X) : InFStar Y := by
  unfold WalterChain at h
  induction h with
  | refl => exact hX
  | tail hab hbc ih =>
      rcases hbc with hstep | hstep
      · exact inFStar_of_walterArrow hA hstep ih
      · exact inFStar_of_walterArrowDiag hA hstep ih

end CFSG.OddStandard.SmallF3.Omega
