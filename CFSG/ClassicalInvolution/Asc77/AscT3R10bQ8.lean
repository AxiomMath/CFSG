module

public import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

section Q8

variable {G : Type} [Group G]

theorem z_zpow_cases {z : G} (hz2 : z * z = 1) (a : ℤ) : z ^ a = 1 ∨ z ^ a = z := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' a
  · left
    rw [zpow_mul, show z ^ (2 : ℤ) = 1 by rw [zpow_two, hz2], one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, show z ^ (2 : ℤ) = 1 by rw [zpow_two, hz2], one_zpow, one_mul]

structure Q8Dat (R : Subgroup G) (z u r : G) : Prop where
  hu : u ∈ R
  hr : r ∈ R
  hu2 : u * u = z
  hr2 : r * r = z
  hru : r * u * r⁻¹ = u⁻¹
  hrn : r ∉ Subgroup.zpowers u
  hcover : ∀ x ∈ R, x ∈ Subgroup.zpowers u ∨ ∃ y ∈ Subgroup.zpowers u, x = y * r

theorem Q8Dat.inv {R : Subgroup G} {z u r : G} (D : Q8Dat R z u r) (hz2 : z * z = 1) :
    Q8Dat R z u⁻¹ r where
  hu := R.inv_mem D.hu
  hr := D.hr
  hu2 := by
    rw [← mul_inv_rev, D.hu2]
    exact inv_eq_of_mul_eq_one_right hz2
  hr2 := D.hr2
  hru := by
    have : r * u⁻¹ * r⁻¹ = (r * u * r⁻¹)⁻¹ := by group
    rw [this, D.hru]
  hrn := by rw [Subgroup.zpowers_inv]; exact D.hrn
  hcover := by rw [Subgroup.zpowers_inv]; exact D.hcover

theorem Q8Dat.sq_cases {R : Subgroup G} {z u r : G} (D : Q8Dat R z u r) (hz2 : z * z = 1) :
    ∀ x ∈ R, x * x = 1 ∨ x * x = z := by
  intro x hx
  have hconj : ∀ a : ℤ, r * u ^ a * r⁻¹ = u ^ (-a) := by
    intro a
    rw [← conj_zpow, D.hru, inv_zpow']
  rcases D.hcover x hx with h | ⟨y, hy, rfl⟩
  · obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, D.hu2]
    exact z_zpow_cases hz2 a
  · right
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h3 : r * u ^ a = u ^ (-a) * r := by
      calc r * u ^ a = (r * u ^ a * r⁻¹) * r := by group
        _ = u ^ (-a) * r := by rw [hconj]
    calc u ^ a * r * (u ^ a * r) = u ^ a * (r * u ^ a) * r := by group
      _ = u ^ a * (u ^ (-a) * r) * r := by rw [h3]
      _ = u ^ (a + -a) * (r * r) := by rw [zpow_add]; group
      _ = z := by rw [D.hr2, add_neg_cancel, zpow_zero, one_mul]

theorem Q8Dat.key {R : Subgroup G} {z u r v t : G} (D : Q8Dat R z u r) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hvR : ∀ x ∈ R, v * x * v⁻¹ ∈ R) (hvu : v * u = u * v) (hvv : v * v = t)
    (ht2 : t * t = 1) (hrt : r * t * r⁻¹ = t * z) :
    ∀ x ∈ R, (x ∈ Subgroup.zpowers u →
        x * (v * x * v⁻¹) * u = u ∨ x * (v * x * v⁻¹) * u = u⁻¹) ∧
      (x ∉ Subgroup.zpowers u → x * (v * x * v⁻¹) * u = 1 ∨ x * (v * x * v⁻¹) * u = z) := by
  obtain ⟨-, hr, hu2, hr2, hru, hrn, hcover⟩ := D
  have hu4 : u ^ 4 = 1 := by
    rw [show u ^ 4 = (u * u) * (u * u) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
      hu2, hz2]
  have hzu : z * u = u * z := by rw [← hu2]; group
  have hzu' : z * u = u⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [mul_assoc, hu2, hz2]
  have hconjr : ∀ a : ℤ, r * u ^ a * r⁻¹ = u ^ (-a) := by
    intro a
    rw [← conj_zpow, hru, inv_zpow']
  have hvz : ∀ a : ℤ, v * u ^ a * v⁻¹ = u ^ a := by
    intro a
    have : v * u ^ a = u ^ a * v := ((Commute.zpow_right (show Commute v u from hvu) a).eq)
    rw [this]
    group
  have hu2z : ∀ a : ℤ, u ^ (2 * a) = z ^ a := by
    intro a
    rw [zpow_mul, zpow_two, hu2]
  intro x hx
  constructor
  · intro hxu
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxu
    rw [hvz a]
    have h1 : u ^ a * u ^ a * u = z ^ a * u := by
      rw [← zpow_add, ← two_mul, hu2z]
    rw [h1]
    rcases z_zpow_cases hz2 a with h | h
    · left
      rw [h, one_mul]
    · right
      rw [h, hzu']
  · intro hxn
    rcases hcover x hx with h | ⟨y, hy, rfl⟩
    · exact absurd h hxn
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hr1 : v * r * v⁻¹ ∈ R := hvR r hr
    obtain ⟨k, hk⟩ : ∃ k : ℤ, v * r * v⁻¹ = u ^ k * r := by
      rcases hcover _ hr1 with h | ⟨y', hy', h⟩
      · exfalso
        apply hrn
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
        have : r = v⁻¹ * (u ^ j) * v := by rw [hj]; group
        rw [this]
        have h3 : v⁻¹ * u ^ j * v = u ^ j := by
          have : u ^ j * v = v * u ^ j :=
            ((Commute.zpow_left (show Commute u v from hvu.symm) j).eq)
          calc v⁻¹ * u ^ j * v = v⁻¹ * (u ^ j * v) := by rw [mul_assoc]
            _ = u ^ j := by rw [this]; group
        rw [h3]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) j
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
        exact ⟨k, by rw [h, ← hk]⟩
    have hvvr : v * (v * r * v⁻¹) * v⁻¹ = z * r := by
      have h1 : v * (v * r * v⁻¹) * v⁻¹ = t * r * t := by
        have : t = v * v := hvv.symm
        have hti : t = t⁻¹ := eq_inv_of_mul_eq_one_left ht2
        calc v * (v * r * v⁻¹) * v⁻¹ = (v * v) * r * (v * v)⁻¹ := by group
          _ = t * r * t := by rw [hvv, ← hti]
      rw [h1]
      have hrt' : r * t = t * z * r := by
        calc r * t = (r * t * r⁻¹) * r := by group
          _ = t * z * r := by rw [hrt]
      calc t * r * t = t * (r * t) := by rw [mul_assoc]
        _ = t * (t * z * r) := by rw [hrt']
        _ = (t * t) * z * r := by group
        _ = z * r := by rw [ht2, one_mul]
    have hvvr' : v * (v * r * v⁻¹) * v⁻¹ = u ^ (2 * k) * r := by
      rw [hk]
      have : v * (u ^ k * r) * v⁻¹ = u ^ k * (v * r * v⁻¹) := by
        calc v * (u ^ k * r) * v⁻¹ = (v * u ^ k * v⁻¹) * (v * r * v⁻¹) := by group
          _ = u ^ k * (v * r * v⁻¹) := by rw [hvz]
      rw [this, hk, ← mul_assoc, ← zpow_add, ← two_mul]
    have hk2 : u ^ (2 * k) = z := by
      have : u ^ (2 * k) * r = z * r := hvvr'.symm.trans hvvr
      exact mul_right_cancel this
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exfalso
      apply hz1
      rw [← hk2]
      have : u ^ (2 * (2 * m)) = (u ^ 4) ^ m := by
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [this, hu4, one_zpow]
    ·
      have hvx : v * (u ^ a * r) * v⁻¹ = u ^ a * (u ^ (2 * m + 1) * r) := by
        calc v * (u ^ a * r) * v⁻¹ = (v * u ^ a * v⁻¹) * (v * r * v⁻¹) := by group
          _ = u ^ a * (u ^ (2 * m + 1) * r) := by rw [hvz, hk]
      rw [hvx]
      have h2 : u ^ a * r * (u ^ a * (u ^ (2 * m + 1) * r)) * u =
          u ^ (-(2 * m + 1)) * z * u := by
        have h3 : r * u ^ (a + (2 * m + 1)) = u ^ (-(a + (2 * m + 1))) * r := by
          have := hconjr (a + (2 * m + 1))
          calc r * u ^ (a + (2 * m + 1)) = (r * u ^ (a + (2 * m + 1)) * r⁻¹) * r := by group
            _ = u ^ (-(a + (2 * m + 1))) * r := by rw [this]
        calc u ^ a * r * (u ^ a * (u ^ (2 * m + 1) * r)) * u
            = u ^ a * (r * u ^ (a + (2 * m + 1))) * r * u := by
              rw [zpow_add]; group
          _ = u ^ a * (u ^ (-(a + (2 * m + 1))) * r) * r * u := by rw [h3]
          _ = u ^ (a + -(a + (2 * m + 1))) * (r * r) * u := by rw [zpow_add]; group
          _ = u ^ (-(2 * m + 1)) * z * u := by
              rw [hr2]
              congr 3
              ring
      rw [h2]
      have h4 : u ^ (-(2 * m + 1)) * z * u = z ^ (-m) * z * (u⁻¹ * u) := by
        have : u ^ (-(2 * m + 1)) = z ^ (-m) * u⁻¹ := by
          rw [show -(2 * m + 1) = 2 * (-m) + -1 by ring, zpow_add, hu2z, zpow_neg_one]
        rw [this]
        calc z ^ (-m) * u⁻¹ * z * u = z ^ (-m) * (u⁻¹ * z) * u := by group
          _ = z ^ (-m) * (z * u⁻¹) * u := by
            congr 2
            have : Commute u⁻¹ z := (Commute.inv_left (show Commute u z from by
              rw [← hu2]; exact Commute.refl u |>.mul_right (Commute.refl u)))
            exact this.eq
          _ = z ^ (-m) * z * (u⁻¹ * u) := by group
      rw [h4, inv_mul_cancel, mul_one]
      rcases z_zpow_cases hz2 (-m) with h | h
      · right
        rw [h, one_mul]
      · left
        rw [h, hz2]

theorem order_four_abstract {R R' W : Subgroup G} {z t u r u₂ r₂ v : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (ht2 : t * t = 1) (DR : Q8Dat R z u r)
    (DR' : Q8Dat R' z u₂ r₂) (hRR' : ∀ x ∈ R, ∀ y ∈ R', x * y = y * x)
    (hvR : ∀ x ∈ R, v * x * v⁻¹ ∈ R) (hvR' : ∀ x ∈ R', v * x * v⁻¹ ∈ R')
    (hvu : v * u = u * v) (hvu₂ : v * u₂ = u₂ * v) (hvv : v * v = t) (hut : u * u₂ = t)
    (hrt : r * t * r⁻¹ = t * z) (hrt₂ : r₂ * t * r₂⁻¹ = t * z) (huW : u ∈ W) (hu₂W : u₂ ∈ W)
    (hvW : v ∈ W) {s : G} (hs : ∃ x ∈ R, ∃ x' ∈ R', ∃ k : ℤ, s = x * x' * v ^ k)
    (hs2 : s * s ≠ 1) (hs4 : (s * s) * (s * s) = 1) : s * s = z ∨ s ∈ W := by
  have hv4 : v ^ 4 = 1 := by
    rw [show v ^ 4 = (v * v) * (v * v) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
      hvv, ht2]
  have hvk : ∀ k : ℤ, v ^ k = 1 ∨ v ^ k = v ∨ v ^ k = t ∨ v ^ k = t * v := by
    intro k
    have hk : v ^ k = v ^ (k % 4) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 4]
      rw [zpow_add, zpow_mul, show v ^ (4 : ℤ) = 1 by exact_mod_cast hv4, one_zpow, mul_one]
    have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rw [hk]
    rcases h4 with h | h | h | h <;> rw [h]
    · left
      simp
    · right
      left
      simp
    · right
      right
      left
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hvv]
    · right
      right
      right
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, pow_two, hvv]
  have FA : ∀ X ∈ R, ∀ X' ∈ R', (X * X') * (X * X') ≠ 1 → (X * X') * (X * X') = z := by
    intro X hX X' hX' hne
    have h1 : (X * X') * (X * X') = (X * X) * (X' * X') := by
      calc (X * X') * (X * X') = X * (X' * X) * X' := by group
        _ = X * (X * X') * X' := by rw [← hRR' X hX X' hX']
        _ = (X * X) * (X' * X') := by group
    rw [h1] at hne ⊢
    rcases DR.sq_cases hz2 X hX with h | h <;> rcases DR'.sq_cases hz2 X' hX' with h' | h'
    · rw [h, h'] at hne
      simp at hne
    · rw [h, h', one_mul]
    · rw [h, h', mul_one]
    · rw [h, h', hz2] at hne
      simp at hne
  have FB : ∀ X ∈ R, ∀ X' ∈ R', (X * X' * v) * (X * X' * v) ≠ 1 →
      ((X * X' * v) * (X * X' * v)) * ((X * X' * v) * (X * X' * v)) = 1 →
      (X * X' * v) * (X * X' * v) = z ∨ X * X' * v ∈ W := by
    intro X hX X' hX' hne h4
    have hαX : v * X * v⁻¹ ∈ R := hvR X hX
    have hαX' : v * X' * v⁻¹ ∈ R' := hvR' X' hX'
    have hKR := DR.key hz2 hz1 hvR hvu hvv ht2 hrt X hX
    have hKR' := DR'.key hz2 hz1 hvR' hvu₂ hvv ht2 hrt₂ X' hX'
    set A := X * (v * X * v⁻¹) * u with hA
    set B := X' * (v * X' * v⁻¹) * u₂ with hB
    have hAR : A ∈ R := R.mul_mem (R.mul_mem hX hαX) DR.hu
    have hBR' : B ∈ R' := R'.mul_mem (R'.mul_mem hX' hαX') DR'.hu
    have hsq : (X * X' * v) * (X * X' * v) = A * B := by
      have e1 : X' * (v * X * v⁻¹) = (v * X * v⁻¹) * X' := (hRR' _ hαX X' hX').symm
      have e2 : X' * (v * X' * v⁻¹) * u = u * X' * (v * X' * v⁻¹) := by
        calc X' * (v * X' * v⁻¹) * u = X' * ((v * X' * v⁻¹) * u) := by group
          _ = X' * (u * (v * X' * v⁻¹)) := by rw [hRR' u DR.hu _ hαX']
          _ = (X' * u) * (v * X' * v⁻¹) := by group
          _ = (u * X') * (v * X' * v⁻¹) := by rw [hRR' u DR.hu X' hX']
      calc (X * X' * v) * (X * X' * v)
          = X * X' * (v * X * v⁻¹) * (v * X' * v⁻¹) * (v * v) := by group
        _ = X * X' * (v * X * v⁻¹) * (v * X' * v⁻¹) * (u * u₂) := by rw [hvv, hut]
        _ = X * (X' * (v * X * v⁻¹)) * (v * X' * v⁻¹) * u * u₂ := by group
        _ = X * ((v * X * v⁻¹) * X') * (v * X' * v⁻¹) * u * u₂ := by rw [e1]
        _ = X * (v * X * v⁻¹) * (X' * (v * X' * v⁻¹) * u) * u₂ := by group
        _ = X * (v * X * v⁻¹) * (u * X' * (v * X' * v⁻¹)) * u₂ := by rw [e2]
        _ = A * B := by rw [hA, hB]; group
    have hs4' : (A * B) * (A * B) = (A * A) * (B * B) := by
      calc (A * B) * (A * B) = A * (B * A) * B := by group
        _ = A * (A * B) * B := by rw [← hRR' A hAR B hBR']
        _ = (A * A) * (B * B) := by group
    rw [hsq] at hne h4 ⊢
    rw [hs4'] at h4
    by_cases hXu : X ∈ Subgroup.zpowers u <;> by_cases hX'u : X' ∈ Subgroup.zpowers u₂
    · right
      exact W.mul_mem (W.mul_mem (Subgroup.zpowers_le.mpr huW hXu)
        (Subgroup.zpowers_le.mpr hu₂W hX'u)) hvW
    · exfalso
      have hA2 : A * A = z := by
        rcases (hKR.1 hXu) with h | h <;> rw [h]
        · exact DR.hu2
        · rw [← mul_inv_rev, DR.hu2]
          exact inv_eq_of_mul_eq_one_right hz2
      have hB2 : B * B = 1 := by
        rcases (hKR'.2 hX'u) with h | h <;> rw [h]
        · simp
        · exact hz2
      rw [hA2, hB2, mul_one] at h4
      exact hz1 h4
    · exfalso
      have hB2 : B * B = z := by
        rcases (hKR'.1 hX'u) with h | h <;> rw [h]
        · exact DR'.hu2
        · rw [← mul_inv_rev, DR'.hu2]
          exact inv_eq_of_mul_eq_one_right hz2
      have hA2 : A * A = 1 := by
        rcases (hKR.2 hXu) with h | h <;> rw [h]
        · simp
        · exact hz2
      rw [hA2, hB2, one_mul] at h4
      exact hz1 h4
    · left
      rcases (hKR.2 hXu) with h | h <;> rcases (hKR'.2 hX'u) with h' | h' <;> rw [h, h'] at hne ⊢
      · simp at hne
      · rw [one_mul]
      · rw [mul_one]
      · rw [hz2] at hne
        simp at hne
  obtain ⟨x, hx, x', hx', k, rfl⟩ := hs
  rcases hvk k with h | h | h | h <;> rw [h] at hs2 hs4 ⊢
  · rw [mul_one] at hs2 hs4 ⊢
    exact Or.inl (FA x hx x' hx' hs2)
  · exact FB x hx x' hx' hs2 hs4
  · have e : x * x' * t = (x * u) * (x' * u₂) := by
      rw [← hut]
      calc x * x' * (u * u₂) = x * (x' * u) * u₂ := by group
        _ = x * (u * x') * u₂ := by rw [← hRR' u DR.hu x' hx']
        _ = (x * u) * (x' * u₂) := by group
    rw [e] at hs2 hs4 ⊢
    exact Or.inl (FA _ (R.mul_mem hx DR.hu) _ (R'.mul_mem hx' DR'.hu) hs2)
  · have e : x * x' * (t * v) = (x * u) * (x' * u₂) * v := by
      rw [← hut]
      calc x * x' * (u * u₂ * v) = x * (x' * u) * u₂ * v := by group
        _ = x * (u * x') * u₂ * v := by rw [← hRR' u DR.hu x' hx']
        _ = (x * u) * (x' * u₂) * v := by group
    rw [e] at hs2 hs4 ⊢
    exact FB _ (R.mul_mem hx DR.hu) _ (R'.mul_mem hx' DR'.hu) hs2 hs4

end Q8

end CFSG.ClassicalInvolution.Asc77.T3CII
