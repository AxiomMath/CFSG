module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_eq_four_of_le {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQP : Q < P)
    (hQ : Nat.card Q = 64) (hP256 : Nat.card P ≤ 256) (hmod : Q.relIndex P % 3 = 1) :
    Q.relIndex P = 4 ∧ Nat.card P = 256 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hinf : Q ⊓ P = Q := inf_eq_left.mpr hQP.le
  have hmul : Q.relIndex P * Nat.card (Q ⊓ P : Subgroup G) = Nat.card P := by
    simpa using Subgroup.relIndex_mul_card (H := Q) (K := P)
  rw [hinf, hQ, hn] at hmul
  have hdvd : Q.relIndex P ∣ 2 ^ n := ⟨64, hmul.symm⟩
  obtain ⟨j, hjle, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hrne1 : Q.relIndex P ≠ 1 := fun h =>
    (not_le_of_gt hQP) ((Subgroup.relIndex_eq_one).mp h)
  have hj0 : j ≠ 0 := by
    intro hj
    apply hrne1
    simp [hr, hj]
  have hrle : 2 ^ j ≤ 4 := by
    rw [hr] at hmul
    omega
  have hj2 : j ≤ 2 := by
    by_contra h
    have hj3 : 3 ≤ j := by omega
    have h8 : 8 ≤ 2 ^ j := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
    omega
  have hj1 : 1 ≤ j := by omega
  interval_cases j
  · rw [hr] at hmod
    norm_num at hmod
  · rw [hr] at hmul
    norm_num at hmul
    refine ⟨by rw [hr]; norm_num, ?_⟩
    rw [hn]
    exact hmul.symm

theorem exists_pow_four_eq {P V : Subgroup G} (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {ρ : G} (hρ3 : ρ ^ 3 = 1) (hρP : ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P) (hV4 : Nat.card V = 4)
    (hVρ : ∀ v ∈ V, ρ * v * ρ⁻¹ ∈ V) (hfix : ∀ v ∈ V, ρ * v * ρ⁻¹ = v → v = 1)
    (hPV : ∀ x ∈ P, x ^ 4 ∈ V) {x : G} (hx : x ∈ P) (hx4 : x ^ 4 ≠ 1) :
    ∀ y ∈ V, ∃ w ∈ P, w ^ 4 = y := by
  let F : Subgroup G :=
    { carrier := {z | ∃ w ∈ P, w ^ 4 = z}
      one_mem' := ⟨1, P.one_mem, by simp⟩
      mul_mem' := by
        rintro z z' ⟨w, hw, rfl⟩ ⟨u, hu, rfl⟩
        exact ⟨w * u, P.mul_mem hw hu, by rw [Commute.mul_pow (hPab w hw u hu)]⟩
      inv_mem' := by
        rintro z ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, P.inv_mem hw, by simp [inv_pow]⟩ }
  have memF : ∀ z : G, z ∈ F ↔ ∃ w ∈ P, w ^ 4 = z := fun z => Iff.rfl
  let a : G := x ^ 4
  let b : G := ρ * a * ρ⁻¹
  have haF : a ∈ F := ⟨x, hx, rfl⟩
  have hbF : b ∈ F := by
    refine ⟨ρ * x * ρ⁻¹, hρP x hx, ?_⟩
    simp only [b, a]
    rw [conj_pow]
  have hFV : F ≤ V := by
    intro z hz
    obtain ⟨w, hwP, rfl⟩ := hz
    exact hPV w hwP
  have haV : a ∈ V := hFV haF
  have ha_ne : a ≠ 1 := hx4
  have hb_ne : b ≠ 1 := by
    intro h
    apply ha_ne
    have h' := congrArg (fun t => ρ⁻¹ * t * ρ) h
    dsimp only [b] at h'
    group at h'
    exact h'
  have hba : b ≠ a := by
    intro h
    exact ha_ne (hfix a haV h)
  have hcarddvd : Nat.card F ∣ Nat.card V := Subgroup.card_dvd_of_le hFV
  rw [hV4] at hcarddvd
  have hc1 : Nat.card F ≠ 1 := by
    intro h
    have hbot : F = ⊥ := Subgroup.eq_bot_of_card_eq (H := F) h
    have : a ∈ (⊥ : Subgroup G) := hbot ▸ haF
    exact ha_ne (by simpa using this)
  have hc2 : Nat.card F ≠ 2 := by
    intro h2
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp h2
    have hya : (⟨a, haF⟩ : F) = y := huniq _ (by simpa using ha_ne)
    have hyb : (⟨b, hbF⟩ : F) = y := huniq _ (by simpa using hb_ne)
    have : (⟨b, hbF⟩ : F) = ⟨a, haF⟩ := by rw [hyb, hya]
    exact hba (congrArg Subtype.val this)
  haveI : Nonempty F := ⟨⟨a, haF⟩⟩
  have hc3 : 3 ≤ Nat.card F := by
    have hp : 0 < Nat.card F := Nat.card_pos
    omega
  have hc4 : Nat.card F = 4 := by
    have hle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hcarddvd
    interval_cases Nat.card F
    · norm_num at hcarddvd
    · rfl
  have hFV_eq : F = V := Subgroup.eq_of_le_of_card_ge hFV (by rw [hV4, hc4])
  intro y hy
  have hyF : y ∈ F := hFV_eq ▸ hy
  obtain ⟨w, hwP, hw⟩ := hyF
  exact ⟨w, hwP, hw⟩


end CFSG.OddStandard.SmallF3.HarrisU33.S4B
