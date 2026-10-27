module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf5

section Cent

variable {Γ : Type*} [Group Γ]

theorem centralizes_of_inner {Q : Subgroup Γ} (hQ2 : IsPGroup 2 Q) {u q' : Γ} (hq' : q' ∈ Q)
    (hu3 : u ^ 3 = 1) (hact : ∀ p ∈ Q, u * p * u⁻¹ = q'⁻¹ * p * q') :
    ∀ p ∈ Q, u * p = p * u := by
  have he : ∀ p ∈ Q, (q' * u) * p = p * (q' * u) := by
    intro p hp
    have h1 := hact p hp
    have h2 : u * p = q'⁻¹ * p * q' * u := by
      calc u * p = (u * p * u⁻¹) * u := by group
        _ = q'⁻¹ * p * q' * u := by rw [h1]
    calc (q' * u) * p = q' * (u * p) := by group
      _ = q' * (q'⁻¹ * p * q' * u) := by rw [h2]
      _ = p * (q' * u) := by group
  have huq : u * q' = q' * u := by
    have := he q' hq'
    have h3 : q' * (u * q') = q' * (q' * u) := by
      calc q' * (u * q') = (q' * u) * q' := by group
        _ = q' * (q' * u) := this
        _ = q' * (q' * u) := rfl
    exact mul_left_cancel h3
  obtain ⟨j, hj⟩ := hQ2 (⟨q', hq'⟩ : Q)
  have hqj : q' ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcomm : Commute q' u := huq.symm
  have hpow : u ^ (2 ^ j) = (q' * u) ^ (2 ^ j) := by
    rw [hcomm.mul_pow, hqj, one_mul]
  have hN : ∀ p ∈ Q, u ^ (2 ^ j) * p = p * u ^ (2 ^ j) := by
    intro p hp
    rw [hpow]
    exact ((show Commute (q' * u) p from he p hp).pow_left (2 ^ j)).eq
  have h41 : u ^ (2 ^ j * 2 ^ j) = u := by
    rw [pow_eq_pow_mod _ hu3]
    have : (2 ^ j * 2 ^ j) % 3 = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num [Nat.pow_mod]
    rw [this, pow_one]
  intro p hp
  have hcN : ∀ p ∈ Q, Commute (u ^ (2 ^ j)) p := fun p hp => hN p hp
  have : Commute u p := by
    rw [← h41, pow_mul]
    exact (hcN p hp).pow_left (2 ^ j)
  exact this.eq

theorem q8_facts {Q : Subgroup Γ} (e : ↥Q ≃* QuaternionGroup 2) {z : Γ} (hz : z ∈ Q) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) :
    IsPGroup 2 Q ∧ (∀ p ∈ Q, p * z = z * p) ∧
      (∀ q ∈ Q, (∀ p ∈ Q, p * q = q * p) → q = 1 ∨ q = z) := by
  have hdec1 : ∀ g : QuaternionGroup 2, g * g = 1 → g ≠ 1 → ∀ h, h * g = g * h := by decide
  have hdec2 : ∀ g h : QuaternionGroup 2, g * g = 1 → h * h = 1 → g ≠ 1 → h ≠ 1 → g = h := by decide
  have hdec3 : ∀ g : QuaternionGroup 2, (∀ h, h * g = g * h) → g = 1 ∨ g * g = 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr e.toEquiv]
    simp [QuaternionGroup.card]
  · intro p hp
    have hzz : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by rw [← map_mul]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hz2)
    have hz1' : e ⟨z, hz⟩ ≠ 1 := fun h => hz1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
    have := hdec1 _ hzz hz1' (e ⟨p, hp⟩)
    have h2 : e (⟨p, hp⟩ * ⟨z, hz⟩) = e (⟨z, hz⟩ * ⟨p, hp⟩) := by rw [map_mul, map_mul]; exact this
    exact congrArg Subtype.val (e.injective h2)
  · intro q hq hqc
    have hcq : ∀ h, h * e ⟨q, hq⟩ = e ⟨q, hq⟩ * h := by
      intro h
      obtain ⟨⟨p, hp⟩, rfl⟩ := e.surjective h
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hqc p hp))
    rcases hdec3 _ hcq with h1 | h1
    · left
      exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h1)
    · by_cases hq1 : q = 1
      · exact Or.inl hq1
      · right
        have hzz : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by rw [← map_mul]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hz2)
        have hz1' : e ⟨z, hz⟩ ≠ 1 := fun h => hz1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
        have hq1' : e ⟨q, hq⟩ ≠ 1 := fun h => hq1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
        have := hdec2 _ _ h1 hzz hq1' hz1'
        exact congrArg Subtype.val (e.injective this)

end Cent

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf5
