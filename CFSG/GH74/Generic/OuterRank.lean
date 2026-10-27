module

public import CFSG.GH74.Generic.QuaternionCentral

public section

namespace CFSG.GH74.Generic

open Subgroup

theorem isPGroup_zpowers_of_pow_two_pow_eq_one {X : Type*} [Group X] {v : X} {n : ℕ}
    (h : v ^ (2 ^ n) = 1) : IsPGroup 2 (Subgroup.zpowers v) := by
  have hord : orderOf v ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

variable {X : Type*} [Group X] [Finite X]

theorem outer_two_subgroup_not_centralizing (hX : Gen4 X) {j : ℕ} (hj : 1 ≤ j)
    {K : Subgroup X} (φ : Qgen j × Qgen j →* ↥K)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (Qgen.z j, Qgen.z j)) (T : Subgroup X) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Qgen j × Qgen j) (t : X), t ∈ T → (φ a : X) * t = t * (φ a : X)) : T ≤ K := by
  let Φ : Qgen j × Qgen j →* X := K.subtype.comp φ
  have hΦ : ∀ g, Φ g = 1 → g = 1 ∨ g = (Qgen.z j, Qgen.z j) := fun g hg =>
    hφ g (Subtype.ext hg)
  intro t ht
  obtain ⟨g, -, hg⟩ := qq_commuting_two_subgroup_le_range hX hj Φ hΦ T hT hcomm ht
  rw [← hg]
  exact (φ _).2

theorem outer_two_element_moves_qq (hX : Gen4 X) {j : ℕ} (hj : 1 ≤ j) {K : Subgroup X}
    (φ : Qgen j × Qgen j →* ↥K)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (Qgen.z j, Qgen.z j)) {v : X} {n : ℕ}
    (hv : v ^ (2 ^ n) = 1) (hvK : v ∉ K) :
    ∃ a : Qgen j × Qgen j, v * (φ a : X) ≠ (φ a : X) * v := by
  by_contra hcon
  push Not at hcon
  have hT := isPGroup_zpowers_of_pow_two_pow_eq_one hv
  have hle := outer_two_subgroup_not_centralizing hX hj φ hφ (Subgroup.zpowers v) hT
    (fun a t ht => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have h1 : Commute (φ a : X) v := (hcon a).symm
      exact (h1.zpow_right k).eq)
  exact hvK (hle (Subgroup.mem_zpowers v))

end CFSG.GH74.Generic
