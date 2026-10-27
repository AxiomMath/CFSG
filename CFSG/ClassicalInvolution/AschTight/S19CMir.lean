module

public import CFSG.ClassicalInvolution.AschTight.Sec71Setup

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem mul_inv_mem_of_dData {Ω : Set (Subgroup G)} {W R K : Subgroup G} {u r z a : G}
    (hdd : Sec71.DData Ω W R K u r z) (ha2 : a * a = 1) (haR : a * r * a⁻¹ ∈ R)
    (haU : ∀ x ∈ Subgroup.zpowers u, a * x * a⁻¹ ∈ Subgroup.zpowers u) :
    a * r * a⁻¹ * r⁻¹ ∈ Subgroup.zpowers u := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  rcases hdd.cover _ haR with h | ⟨y, hy, hyr⟩
  · exfalso
    apply hdd.r_not_mem
    have h' := haU _ h
    have e : a * (a * r * a⁻¹) * a⁻¹ = r := by
      calc a * (a * r * a⁻¹) * a⁻¹ = (a * a) * r * (a⁻¹ * a⁻¹) := by group
        _ = r := by rw [ha2, hai, ha2, one_mul, mul_one]
    rwa [e] at h'
  · rw [hyr, mul_inv_cancel_right]
    exact hy

theorem conj_conj_eq_of_mem {W : Subgroup G} (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {a r rL y : G} (har : a * r * a⁻¹ = r) (haL : a * rL * a⁻¹ = y * rL) (hy : y ∈ W)
    (hrL : rL ∈ Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ W) :
    (a * (r⁻¹ * rL) * a⁻¹) * x * (a * (r⁻¹ * rL) * a⁻¹)⁻¹ = (r⁻¹ * rL) * x * (r⁻¹ * rL)⁻¹ := by
  have hx' : rL * x * rL⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hrL x).mp hx
  have hr' : a * r⁻¹ * a⁻¹ = r⁻¹ := by
    rw [← inv_inj, show (a * r⁻¹ * a⁻¹)⁻¹ = a * r * a⁻¹ by group, har, inv_inv]
  have e : a * (r⁻¹ * rL) * a⁻¹ = r⁻¹ * (y * rL) := by
    rw [show a * (r⁻¹ * rL) * a⁻¹ = (a * r⁻¹ * a⁻¹) * (a * rL * a⁻¹) by group, hr', haL]
  rw [e]
  calc r⁻¹ * (y * rL) * x * (r⁻¹ * (y * rL))⁻¹ = r⁻¹ * (y * (rL * x * rL⁻¹)) * y⁻¹ * r := by
        group
    _ = r⁻¹ * ((rL * x * rL⁻¹) * y) * y⁻¹ * r := by rw [hWc y hy _ hx']
    _ = (r⁻¹ * rL) * x * (r⁻¹ * rL)⁻¹ := by group

theorem conj_conj_zpow {W U : Subgroup G} (hUW : U ≤ W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {a r rL y : G} (har : a * r * a⁻¹ = r) (haL : a * rL * a⁻¹ = y * rL) (hy : y ∈ W)
    (hrL : rL ∈ Subgroup.normalizer (W : Set G)) {e : ℤ}
    (hact : ∀ x ∈ U, a * x * a⁻¹ = x ^ e) {x : G} (hx : x ∈ U) :
    a * ((r⁻¹ * rL) * x * (r⁻¹ * rL)⁻¹) * a⁻¹ = ((r⁻¹ * rL) * x * (r⁻¹ * rL)⁻¹) ^ e := by
  have hax : a * x * a⁻¹ ∈ W := by rw [hact x hx]; exact zpow_mem (hUW hx) _
  have h1 := conj_conj_eq_of_mem hWc har haL hy hrL hax
  calc a * ((r⁻¹ * rL) * x * (r⁻¹ * rL)⁻¹) * a⁻¹ =
      (a * (r⁻¹ * rL) * a⁻¹) * (a * x * a⁻¹) * (a * (r⁻¹ * rL) * a⁻¹)⁻¹ := by group
    _ = (r⁻¹ * rL) * (a * x * a⁻¹) * (r⁻¹ * rL)⁻¹ := h1
    _ = (r⁻¹ * rL) * x ^ e * (r⁻¹ * rL)⁻¹ := by rw [hact x hx]
    _ = ((r⁻¹ * rL) * x * (r⁻¹ * rL)⁻¹) ^ e := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
