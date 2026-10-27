module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FQa

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T7F2

variable {G : Type} [Group G] {R : Subgroup G} {x y : G} {m : ℕ} {N : Subgroup G}

theorem alpha_cast_eq (c : QuatCoord R x y m) {α : ↥N →* (ZMod (2 ^ (m + 1)))ˣ}
    (hα : ∀ h : ↥N, (h : G) * x * (h : G)⁻¹ = x ^ ((α h : ZMod (2 ^ (m + 1))).val))
    {h : ↥N} {i : ℤ} (hi : (h : G) * x * (h : G)⁻¹ = x ^ i) :
    ((α h : (ZMod (2 ^ (m + 1)))ˣ) : ZMod (2 ^ (m + 1))) = (i : ZMod (2 ^ (m + 1))) := by
  have h1 : x ^ (((α h : ZMod (2 ^ (m + 1))).val : ℕ) : ℤ) = x ^ i := by
    rw [zpow_natCast, ← hα h, hi]
  have h2 := c.zpow_eq_iff.mp h1
  have h3 : (((α h : ZMod (2 ^ (m + 1))).val : ℕ) : ZMod (2 ^ (m + 1))) =
      (i : ZMod (2 ^ (m + 1))) := by
    have h4 : ((((α h : ZMod (2 ^ (m + 1))).val : ℕ) : ℤ) : ZMod (2 ^ (m + 1))) =
        (i : ZMod (2 ^ (m + 1))) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      have : (((2 ^ (m + 1) : ℕ)) : ℤ) = (2 : ℤ) ^ (m + 1) := by push_cast; rfl
      rw [this]
      exact (dvd_sub_comm.mp h2)
    simpa using h4
  rwa [ZMod.natCast_zmod_val] at h3

theorem alpha_eq_neg_one (c : QuatCoord R x y m) {α : ↥N →* (ZMod (2 ^ (m + 1)))ˣ}
    (hα : ∀ h : ↥N, (h : G) * x * (h : G)⁻¹ = x ^ ((α h : ZMod (2 ^ (m + 1))).val))
    {h : ↥N} {i : ℤ} (hi : (h : G) * x * (h : G)⁻¹ = x ^ i) (hdvd : (2 : ℤ) ^ (m + 1) ∣ i + 1) :
    α h = -1 := by
  apply Units.ext
  rw [alpha_cast_eq c hα hi]
  have : ((i + 1 : ℤ) : ZMod (2 ^ (m + 1))) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : (((2 ^ (m + 1) : ℕ)) : ℤ) = (2 : ℤ) ^ (m + 1) := by push_cast; rfl
    rw [this]
    exact hdvd
  push_cast at this
  simp only [Units.val_neg, Units.val_one]
  linear_combination this

theorem alpha_eq_one (c : QuatCoord R x y m) {α : ↥N →* (ZMod (2 ^ (m + 1)))ˣ}
    (hα : ∀ h : ↥N, (h : G) * x * (h : G)⁻¹ = x ^ ((α h : ZMod (2 ^ (m + 1))).val))
    {h : ↥N} (hx : (h : G) * x * (h : G)⁻¹ = x) : α h = 1 := by
  apply Units.ext
  have := alpha_cast_eq c hα (i := 1) (h := h) (by rw [zpow_one]; exact hx)
  simpa using this

theorem alpha_eq_pm_one_of_mem_R (c : QuatCoord R x y m) {α : ↥N →* (ZMod (2 ^ (m + 1)))ˣ}
    (hα : ∀ h : ↥N, (h : G) * x * (h : G)⁻¹ = x ^ ((α h : ZMod (2 ^ (m + 1))).val))
    {h : ↥N} (hR : (h : G) ∈ R) : α h = 1 ∨ α h = -1 := by
  obtain ⟨i, hi, hhx⟩ := mult_of_mem_R c hR
  rcases hi with rfl | rfl
  · left
    exact Units.ext (by simpa using alpha_cast_eq c hα hhx)
  · right
    exact Units.ext (by simpa using alpha_cast_eq c hα hhx)

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
