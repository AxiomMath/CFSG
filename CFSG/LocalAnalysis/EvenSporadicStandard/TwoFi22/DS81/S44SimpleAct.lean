module

public import Mathlib.GroupTheory.GroupAction.Blocks

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction

section Orbit

variable {G α : Type*} [Group G] [MulAction G α]

theorem simple_card_stabilizer_mul_ncard_orbit (a : α) :
    Nat.card (stabilizer G a) * (orbit G a).ncard = Nat.card G := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]

theorem simple_ncard_orbit_dvd_card (a : α) : (orbit G a).ncard ∣ Nat.card G :=
  Dvd.intro_left _ (simple_card_stabilizer_mul_ncard_orbit a)

theorem simple_ncard_orbit_dvd (N : Subgroup G) [N.Normal] (a : α) :
    (orbit N a).ncard ∣ (orbit G a).ncard := by
  have hB : MulAction.IsBlock G (orbit N (⟨a, mem_orbit_self a⟩ : orbit G a)) :=
    MulAction.IsBlock.orbit_of_normal (N := N) _
  have h := hB.ncard_dvd_card ⟨_, mem_orbit_self _⟩
  rw [Nat.card_coe_set_eq] at h
  have himg : Subtype.val '' (orbit N (⟨a, mem_orbit_self a⟩ : orbit G a)) = orbit N a := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, ⟨n, hn⟩, rfl⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact h

theorem simple_smul_mem_orbit_normal (N : Subgroup G) [N.Normal] {a : α} {g : G}
    (hg : g • a = a) {b : α} (hb : b ∈ orbit N a) : g • b ∈ orbit N a := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨⟨g * k * g⁻¹, ‹N.Normal›.conj_mem k k.2 g⟩, ?_⟩
  have hg' : g⁻¹ • a = a := by rw [inv_smul_eq_iff]; exact hg.symm
  show (g * (k : G) * g⁻¹) • a = g • (k : G) • a
  rw [mul_smul, mul_smul, hg']

theorem simple_smul_eq_of_fixes (N : Subgroup G) [N.Normal] {a : α}
    (hN : ∀ k ∈ N, k • a = a) {b : α} (hb : b ∈ orbit G a) {k : G} (hk : k ∈ N) :
    k • b = b := by
  obtain ⟨g, rfl⟩ := hb
  have h : g⁻¹ * k * g ∈ N := ‹N.Normal›.conj_mem' k hk g
  show k • g • a = g • a
  calc k • g • a = (k * g) • a := (mul_smul k g a).symm
    _ = (g * (g⁻¹ * k * g)) • a := by rw [mul_assoc g⁻¹, mul_inv_cancel_left]
    _ = g • (g⁻¹ * k * g) • a := mul_smul _ _ _
    _ = g • a := by rw [hN _ h]

end Orbit

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
