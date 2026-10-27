module

public import CFSG.GH74.Uniqueness.SU.SU1Normal2

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem conj_zpow_of_acts {y a : P} {u : ℕ} (hy : y * a * y⁻¹ = a ^ u) (m : ℤ) :
    y * a ^ m * y⁻¹ = a ^ ((u : ℤ) * m) := by
  rw [← conj_zpow, hy, ← zpow_natCast, ← zpow_mul]

theorem false_of_u0 {k : ℕ} (hP : IsPGroup 2 P) {Q : Subgroup P} {a : P} (h : NSetting Q a)
    (hord : orderOf a = 2 ^ k) (hk : 3 ≤ k)
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False)
    {y : P} (hyQ : y ∈ Q) (hy : y * a * y⁻¹ = a ^ (2 ^ (k - 1) + 1)) : False := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  set w : ℕ := 2 ^ k' with hw
  have hw1 : 1 ≤ w := Nat.one_le_two_pow
  have hN : 2 ^ (k' + 3) = 8 * w := by rw [pow_add, hw]; ring
  have hNh : 2 ^ (k' + 3 - 1) = 4 * w := by
    rw [show k' + 3 - 1 = k' + 2 by omega, pow_add, hw]; ring
  rw [hNh] at hy
  rw [hN] at hord
  have haN : a ^ (8 * w) = 1 := by rw [← hord]; exact pow_orderOf_eq_one a
  have hzp : ∀ c : ℤ, a ^ (((8 * w : ℕ) : ℤ) * c) = 1 := fun c => by
    rw [zpow_mul, zpow_natCast, haN, one_zpow]
  have hyA : y ∉ zpowers a := by
    intro hmem
    have hc : y * a = a * y := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hm]
      exact ((Commute.refl a).zpow_left m).eq
    have h1 : a ^ (4 * w + 1) = a ^ 1 := by
      rw [← hy, pow_one]
      calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [hc]
        _ = a := by group
    have h2 := pow_inj_mod.mp h1
    rw [hord, Nat.mod_eq_of_lt (by omega : 4 * w + 1 < 8 * w),
      Nat.mod_eq_of_lt (by omega : 1 < 8 * w)] at h2
    omega
  have hyy : y * y ∈ zpowers a := by
    apply h.centralizer (y * y) (Q.mul_mem hyQ hyQ)
    have h1 := conj_npow hy 2
    have h2 : (4 * w + 1) ^ 2 = 8 * w * (2 * w + 1) + 1 := by ring
    have h3 : a ^ ((4 * w + 1) ^ 2) = a := by
      rw [h2, pow_add, pow_mul, haN, one_pow, one_mul, pow_one]
    rw [h3] at h1
    calc y * y * a = (y ^ 2 * a * (y ^ 2)⁻¹) * (y * y) := by rw [pow_two]; group
      _ = a * (y * y) := by rw [h1]
  obtain ⟨j, hj⟩ := exists_pow_eq_of_mem_zpowers hyy
  have hj2 : 2 ∣ j := by
    have h1 : y * a ^ j * y⁻¹ = a ^ j := by rw [hj]; group
    rw [conj_of_mem_zpowers hy (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) j)] at h1
    have h2 : (a ^ j) ^ (4 * w) = 1 := by
      rw [pow_succ] at h1
      exact mul_eq_right.mp h1
    rw [← pow_mul] at h2
    have h3 : 8 * w ∣ j * (4 * w) := hord ▸ orderOf_dvd_of_pow_eq_one h2
    have h4 : 2 * (4 * w) ∣ j * (4 * w) := by
      have : 2 * (4 * w) = 8 * w := by ring
      rw [this]
      exact h3
    exact Nat.dvd_of_mul_dvd_mul_right (by omega) h4
  obtain ⟨j', rfl⟩ := hj2
  have key : ∀ i : ℤ, (y * a ^ i) * (y * a ^ i) =
      a ^ (((4 * w + 1 : ℕ) : ℤ) * i + ((2 * j' : ℕ) : ℤ) + i) := by
    intro i
    calc (y * a ^ i) * (y * a ^ i) = (y * a ^ i * y⁻¹) * (y * y) * a ^ i := by group
      _ = a ^ (((4 * w + 1 : ℕ) : ℤ) * i) * a ^ (((2 * j' : ℕ)) : ℤ) * a ^ i := by
          rw [conj_zpow_of_acts hy i, ← hj, zpow_natCast]
      _ = _ := by rw [← zpow_add, ← zpow_add]
  obtain ⟨i, hi⟩ : ∃ i : ℤ, (y * a ^ i) * (y * a ^ i) = 1 := by
    rcases Nat.even_or_odd' j' with ⟨s, rfl | rfl⟩
    · refine ⟨-((2 * s : ℕ) : ℤ), ?_⟩
      rw [key]
      have : ((4 * w + 1 : ℕ) : ℤ) * (-((2 * s : ℕ) : ℤ)) + ((2 * (2 * s) : ℕ) : ℤ) +
          (-((2 * s : ℕ) : ℤ)) = ((8 * w : ℕ) : ℤ) * (-(s : ℤ)) := by push_cast; ring
      rw [this]
      exact hzp _
    · refine ⟨((2 * w : ℕ) : ℤ) - ((2 * s + 1 : ℕ) : ℤ), ?_⟩
      rw [key]
      have : ((4 * w + 1 : ℕ) : ℤ) * (((2 * w : ℕ) : ℤ) - ((2 * s + 1 : ℕ) : ℤ)) +
          ((2 * (2 * s + 1) : ℕ) : ℤ) + (((2 * w : ℕ) : ℤ) - ((2 * s + 1 : ℕ) : ℤ)) =
          ((8 * w : ℕ) : ℤ) * ((w : ℤ) - (s : ℤ)) := by push_cast; ring
      rw [this]
      exact hzp _
  set y' : P := y * a ^ i with hy'
  have haiA : a ^ i ∈ zpowers a := zpow_mem (Subgroup.mem_zpowers a) i
  have hy'Q : y' ∈ Q := Q.mul_mem hyQ (h.le haiA)
  have hy'A : y' ∉ zpowers a := by
    intro hmem
    apply hyA
    have := (zpowers a).mul_mem hmem ((zpowers a).inv_mem haiA)
    simpa [hy'] using this
  have hy'2 : y' ^ 2 = 1 := by rw [pow_two]; exact hi
  have hu' : y' * a * y'⁻¹ = a ^ (4 * w + 1) := by
    have hcomm : a ^ i * a = a * a ^ i := ((Commute.refl a).zpow_left i).eq
    calc y' * a * y'⁻¹ = y * (a ^ i * a * (a ^ i)⁻¹) * y⁻¹ := by rw [hy']; group
      _ = y * a * y⁻¹ := by rw [hcomm]; group
      _ = a ^ (4 * w + 1) := hy
  set z : P := a ^ (4 * w) with hz
  have hzA : z ∈ zpowers a := Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, show 4 * w * 2 = 8 * w by ring, haN]
  have hz1 : z ≠ 1 := by
    intro hz1
    have : orderOf a ∣ 4 * w := orderOf_dvd_of_pow_eq_one hz1
    rw [hord] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  have hzc : z ∈ center P :=
    mem_center_of_normal_prime Nat.prime_two hP hz1 hz2 (h.normal_zpowers_pow _)
  have hZc : zpowers z ≤ center P := Subgroup.zpowers_le.mpr hzc
  have hy'z : y' ∉ zpowers z := fun hmem => hy'A (Subgroup.zpowers_le.mpr hzA hmem)
  obtain ⟨hel, hcard⟩ := isElemAbelian_card_sup_zpowers Nat.prime_two hz2 hy'2 hz1 hy'z
    ((Subgroup.mem_center_iff.mp hzc y').symm)
  have hEQ : zpowers z ⊔ zpowers y' ≤ Q :=
    sup_le ((Subgroup.zpowers_le.mpr hzA).trans h.le) (Subgroup.zpowers_le.mpr hy'Q)
  have hEn : (zpowers z ⊔ zpowers y').Normal := by
    have hle : ∀ g : P, (zpowers z ⊔ zpowers y').map (MulAut.conj g).toMonoidHom ≤
        zpowers z ⊔ zpowers y' := by
      intro g
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · intro x hx
        rw [Subgroup.mem_comap]
        change g * x * g⁻¹ ∈ _
        have hxc : x ∈ center P := hZc hx
        have : g * x * g⁻¹ = x := by
          rw [Subgroup.mem_center_iff.mp hxc g]
          group
        rw [this]
        exact Subgroup.mem_sup_left hx
      · rw [Subgroup.mem_comap]
        change g * y' * g⁻¹ ∈ _
        obtain ⟨c₀, hc₀, hgy⟩ := h.conj_mem_coset hy'Q g
        rw [hgy]
        have hc₀z : c₀ ∈ zpowers z := by
          obtain ⟨m', hm'⟩ := exists_pow_eq_of_mem_zpowers hc₀
          have h1 : (y' * c₀) * (y' * c₀) = 1 := by
            have : (g * y' * g⁻¹) * (g * y' * g⁻¹) = 1 := by
              calc (g * y' * g⁻¹) * (g * y' * g⁻¹) = g * (y' * y') * g⁻¹ := by group
                _ = 1 := by rw [← pow_two, hy'2]; group
            rwa [hgy] at this
          have h2 : (y' * c₀) * (y' * c₀) = c₀ ^ (4 * w + 1) * c₀ := by
            calc (y' * c₀) * (y' * c₀) = (y' * c₀ * y'⁻¹) * (y' * y') * c₀ := by group
              _ = c₀ ^ (4 * w + 1) * 1 * c₀ := by
                  rw [conj_of_mem_zpowers hu' hc₀, ← pow_two, hy'2]
              _ = c₀ ^ (4 * w + 1) * c₀ := by rw [mul_one]
          rw [h2, ← hm', ← pow_mul, ← pow_add] at h1
          have hcop : Nat.Coprime (4 * w) (2 * w + 1) := by
            have h2' : Nat.Coprime 2 (2 * w + 1) :=
              (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
            have e : 4 * w = 2 ^ (k' + 2) := by rw [pow_add, hw]; ring
            rw [e]
            exact Nat.Coprime.pow_left _ h2'
          have hdvd : 4 * w ∣ m' * (2 * w + 1) := by
            have h3 : 8 * w ∣ m' * (4 * w + 1) + m' := hord ▸ orderOf_dvd_of_pow_eq_one h1
            have h4 : 2 * (4 * w) ∣ 2 * (m' * (2 * w + 1)) := by
              have e1 : 2 * (4 * w) = 8 * w := by ring
              have e2 : 2 * (m' * (2 * w + 1)) = m' * (4 * w + 1) + m' := by ring
              rw [e1, e2]
              exact h3
            exact Nat.dvd_of_mul_dvd_mul_left two_pos h4
          obtain ⟨q, hq⟩ := hcop.dvd_of_dvd_mul_right hdvd
          rw [← hm', hq, pow_mul]
          exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
        exact (zpowers z ⊔ zpowers y').mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers y'))
          (Subgroup.mem_sup_left hc₀z)
    exact ⟨fun x hx g => hle g ⟨x, hx, rfl⟩⟩
  exact hstar _ hEn hEQ hel hcard

end CFSG.GH74.Uniqueness.SU.SU1
