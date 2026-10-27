module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.Octad

open Subgroup

variable {G : Type} [Group G]

structure YFactsB (L B : Subgroup G) (phi : G → G) (Y : Subgroup G) : Prop where
  B_le : B ≤ Y
  central : ∀ y ∈ Y, ∀ u ∈ B, y * u = u * y
  sq_mem : ∀ y ∈ Y, y * y ∈ B
  phi_mem : ∀ y ∈ Y, phi y ∈ B
  phi_mul : ∀ y ∈ Y, ∀ y' ∈ Y, phi (y * y') = phi y * phi y'
  phi_ker : ∀ y ∈ Y, phi y = 1 → y ∈ B
  phi_surj : ∀ u ∈ B, ∃ y ∈ Y, phi y = u
  phi_conj : ∀ h ∈ egNL L B, ∀ y ∈ Y,
    h * y * h⁻¹ ∈ Y ∧ phi (h * y * h⁻¹) = h * phi y * h⁻¹

structure IsSectB (B Y : Subgroup G) (phi η : G → G) : Prop where
  mem : ∀ u ∈ B, η u ∈ Y
  phi_eq : ∀ u ∈ B, phi (η u) = u

section Sect

variable {L B Y : Subgroup G} {phi η : G → G}

theorem sq_eq_of_phi_eq (hBsq : ∀ u ∈ B, u * u = 1) (hF : YFactsB L B phi Y) {y y' : G}
    (hy : y ∈ Y) (hy' : y' ∈ Y) (h : phi y = phi y') : y * y = y' * y' := by
  have ht : y⁻¹ * y' ∈ Y := Y.mul_mem (Y.inv_mem hy) hy'
  have hmul := hF.phi_mul y hy _ ht
  rw [mul_inv_cancel_left] at hmul
  have h1 : phi (y⁻¹ * y') = 1 := by
    have : phi y * phi (y⁻¹ * y') = phi y * 1 := by rw [← hmul, ← h, mul_one]
    exact mul_left_cancel this
  have htB : y⁻¹ * y' ∈ B := hF.phi_ker _ ht h1
  obtain ⟨t, ht', rfl⟩ : ∃ t ∈ B, y' = y * t := ⟨y⁻¹ * y', htB, by group⟩
  have hc := hF.central y hy t ht'
  calc y * y = y * y * (t * t) := by rw [hBsq t ht', mul_one]
    _ = y * (y * t) * t := by group
    _ = y * (t * y) * t := by rw [hc]
    _ = (y * t) * (y * t) := by group

theorem sect_sq (hBsq : ∀ u ∈ B, u * u = 1) (hF : YFactsB L B phi Y) (hη : IsSectB B Y phi η)
    {y : G} (hy : y ∈ Y) : η (phi y) * η (phi y) = y * y :=
  sq_eq_of_phi_eq hBsq hF (hη.mem _ (hF.phi_mem y hy)) hy (hη.phi_eq _ (hF.phi_mem y hy))

theorem sect_sq_fix (hb : OctadBasics L B) (hF : YFactsB L B phi Y) (hη : IsSectB B Y phi η)
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) : η x * η x = 1 ∨ η x * η x = x := by
  have hy := hη.mem x hx
  refine hb.fix x hx hx1 (η x * η x) (hF.sq_mem _ hy) (fun h hh hhx => ?_)
  obtain ⟨hhY, hphi⟩ := hF.phi_conj h hh (η x) hy
  rw [hη.phi_eq x hx, hhx] at hphi
  have hsq := sq_eq_of_phi_eq hb.elem.2 hF hhY hy (by rw [hphi, hη.phi_eq x hx])
  calc h * (η x * η x) * h⁻¹ = (h * η x * h⁻¹) * (h * η x * h⁻¹) := by group
    _ = η x * η x := hsq

theorem sect_sq_conj (hBsq : ∀ u ∈ B, u * u = 1) (hF : YFactsB L B phi Y)
    (hη : IsSectB B Y phi η) {h x : G} (hh : h ∈ egNL L B) (hx : x ∈ B) :
    η (h * x * h⁻¹) * η (h * x * h⁻¹) = h * (η x * η x) * h⁻¹ := by
  obtain ⟨hhY, hphi⟩ := hF.phi_conj h hh (η x) (hη.mem x hx)
  rw [hη.phi_eq x hx] at hphi
  have := sect_sq hBsq hF hη hhY
  rw [hphi] at this
  rw [this]
  group

end Sect

theorem Y_sq_dichotomy {L B Y : Subgroup G} {phi : G → G} (hb : OctadBasics L B)
    (hF : YFactsB L B phi Y) : (∀ y ∈ Y, y * y = 1) ∨ ∀ y ∈ Y, y * y = phi y := by
  choose! η hηY hηphi using hF.phi_surj
  have hη : IsSectB B Y phi η := ⟨hηY, hηphi⟩
  have hBsq := hb.elem.2
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ B, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B = ⊥ := by rw [eq_bot_iff_forall]; exact hcon
    have h16 := hb.card_B
    rw [hbot, card_bot] at h16
    norm_num at h16
  have hconst : ∀ x ∈ B, x ≠ 1 → (η x * η x = x ↔ η a * η a = a) := by
    intro x hx hx1
    obtain ⟨h, hh, rfl⟩ := hb.trans a ha x hx ha1 hx1
    rw [sect_sq_conj hBsq hF hη hh ha]
    constructor
    · intro e
      exact mul_left_cancel (mul_right_cancel e)
    · intro e
      rw [e]
  by_cases hT : η a * η a = a
  · right
    intro y hy
    by_cases hy1 : phi y = 1
    · rw [hy1]
      exact hBsq y (hF.phi_ker y hy hy1)
    · exact (sect_sq hBsq hF hη hy).symm.trans ((hconst _ (hF.phi_mem y hy) hy1).2 hT)
  · left
    intro y hy
    by_cases hy1 : phi y = 1
    · exact hBsq y (hF.phi_ker y hy hy1)
    · have hx := hF.phi_mem y hy
      rw [← sect_sq hBsq hF hη hy]
      rcases sect_sq_fix hb hF hη hx hy1 with h | h
      · exact h
      · exact absurd ((hconst _ hx hy1).1 h) hT

theorem abelian_of_sq_eq {Y : Subgroup G} {phi : G → G}
    (hmul : ∀ y ∈ Y, ∀ y' ∈ Y, phi (y * y') = phi y * phi y')
    (hsq : ∀ y ∈ Y, y * y = phi y) : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
  intro y hy y' hy'
  have h1 := hsq _ (Y.mul_mem hy hy')
  rw [hmul y hy y' hy', ← hsq y hy, ← hsq y' hy'] at h1
  have h2 : y * (y' * y) * y' = y * (y * y') * y' := by
    calc y * (y' * y) * y' = y * y' * (y * y') := by group
      _ = y * y * (y' * y') := h1
      _ = y * (y * y') * y' := by group
  exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem abelian_of_sq_eq_one {Y : Subgroup G} (hsq : ∀ y ∈ Y, y * y = 1) :
    ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
  intro y hy y' hy'
  have e1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
  have e2 : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right (hsq y' hy')
  have e3 : (y * y')⁻¹ = y * y' := inv_eq_of_mul_eq_one_right (hsq _ (Y.mul_mem hy hy'))
  calc y * y' = (y * y')⁻¹ := e3.symm
    _ = y' * y := by rw [mul_inv_rev, e1, e2]

end CFSG.EvenSporadicStandard.M24Std.Octad
