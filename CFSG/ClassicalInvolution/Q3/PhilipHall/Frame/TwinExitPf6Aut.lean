module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf5Cent
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6

open scoped MatrixGroups

section Aut

variable {Γ : Type*} [Group Γ]

theorem fixed_of_normalizes {L Q : Subgroup Γ} {y z : Γ} (σ : Γ →* Γ) (hQL : Q ≤ L)
    (hQn : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q)
    (hLgen : L = Q ⊔ Subgroup.zpowers y) (hy3 : y ^ 3 = 1) (hyact : ∃ q ∈ Q, y * q ≠ q * y)
    (hz : z ∈ Q) (hzc : ∀ p ∈ Q, p * z = z * p) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hcen : ∀ q ∈ Q, (∀ p ∈ Q, p * q = q * p) → q = 1 ∨ q = z)
    (hσL : ∀ l ∈ L, σ l ∈ L) (hσQ : ∀ q ∈ Q, σ q = q) :
    ∀ l ∈ L, σ l = l := by
  have hyL : y ∈ L := hLgen ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hQnorm : ∀ l ∈ L, ∀ q ∈ Q, l⁻¹ * q * l ∈ Q := by
    intro l hl q hq
    have := hQn l⁻¹ (L.inv_mem hl) q hq
    simpa using this
  have hBn : Subgroup.zpowers y ≤ Subgroup.normalizer (Q : Set Γ) := by
    intro b hb
    have hbL : b ∈ L := hLgen ▸ Subgroup.mem_sup_right hb
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨fun hq => by simpa using hQn b hbL q hq,
      fun hq => by simpa [mul_assoc] using hQnorm b hbL _ hq⟩
  have hdec : ∀ l ∈ L, ∃ q ∈ Q, ∃ k : ℤ, l = q * y ^ k := by
    intro l hl
    have h1 : l ∈ ((Q ⊔ Subgroup.zpowers y : Subgroup Γ) : Set Γ) := hLgen ▸ hl
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q (Subgroup.zpowers y) hBn] at h1
    obtain ⟨q, hq, b, hb, e⟩ := h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ⟨q, hq, k, e.symm⟩
  suffices hxy : σ y = y by
    intro l hl
    obtain ⟨q, hq, k, rfl⟩ := hdec l hl
    rw [map_mul, map_zpow, hxy, hσQ q hq]
  set w : Γ := σ y with hw
  have hwL : w ∈ L := hσL y hyL
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow, hy3, map_one]
  have hwact : ∀ p ∈ Q, w * p * w⁻¹ = y * p * y⁻¹ := by
    intro p hp
    have hyp : y * p * y⁻¹ ∈ Q := hQn y hyL p hp
    calc w * p * w⁻¹ = σ y * σ p * (σ y)⁻¹ := by rw [hw, hσQ p hp]
      _ = σ (y * p * y⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = y * p * y⁻¹ := hσQ _ hyp
  set v : Γ := y⁻¹ * w with hv
  have hvL : v ∈ L := L.mul_mem (L.inv_mem hyL) hwL
  have hvc : ∀ p ∈ Q, v * p = p * v := by
    intro p hp
    have h1 := hwact p hp
    calc v * p = y⁻¹ * (w * p * w⁻¹) * w := by rw [hv]; group
      _ = y⁻¹ * (y * p * y⁻¹) * w := by rw [h1]
      _ = p * (y⁻¹ * w) := by group
  obtain ⟨q', hq', k, hk⟩ := hdec v hvL
  set u : Γ := y ^ k with hu
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have huact : ∀ p ∈ Q, u * p * u⁻¹ = q'⁻¹ * p * q' := by
    intro p hp
    have h1 := hvc p hp
    rw [hk] at h1
    calc u * p * u⁻¹ = q'⁻¹ * (q' * u * p) * u⁻¹ := by group
      _ = q'⁻¹ * (p * (q' * u)) * u⁻¹ := by rw [h1]
      _ = q'⁻¹ * p * q' := by group
  have hucen := TwinExitPf5.centralizes_of_inner hQ2 hq' hu3 huact
  have hu1 : u = 1 := by
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have hy3z : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
    have hyk : y ^ k = y ^ (k % 3) := zpow_eq_zpow_emod k hy3z
    obtain ⟨q₀, hq₀, hq₀y⟩ := hyact
    rcases hk3 with h0 | h1 | h2
    · rw [hu, hyk, h0, zpow_zero]
    · exfalso
      have : u = y := by rw [hu, hyk, h1, zpow_one]
      exact hq₀y (this ▸ hucen q₀ hq₀)
    · exfalso
      have hy2 : u = y ^ 2 := by rw [hu, hyk, h2, zpow_two, pow_two]
      have hyy : y = u * u := by
        rw [hy2]
        calc y = y ^ 4 := by
              calc y = y * (y ^ 3) := by rw [hy3, mul_one]
                _ = y ^ 4 := by group
          _ = y ^ 2 * y ^ 2 := by group
      have hc1 := hucen q₀ hq₀
      apply hq₀y
      rw [hyy]
      calc u * u * q₀ = u * (u * q₀) := by group
        _ = u * (q₀ * u) := by rw [hc1]
        _ = (u * q₀) * u := by group
        _ = (q₀ * u) * u := by rw [hc1]
        _ = q₀ * (u * u) := by group
  rw [hu1, mul_one] at hk
  have hq'c : ∀ p ∈ Q, p * q' = q' * p := by
    intro p hp
    have := hvc p hp
    rw [hk] at this
    exact this.symm
  have hyz : y * z = z * y := by
    have hyzQ : y * z * y⁻¹ ∈ Q := hQn y hyL z hz
    have hcz : ∀ p ∈ Q, p * (y * z * y⁻¹) = (y * z * y⁻¹) * p := by
      intro p hp
      have hp' : y⁻¹ * p * y ∈ Q := hQnorm y hyL p hp
      have h1 := hzc _ hp'
      calc p * (y * z * y⁻¹) = y * ((y⁻¹ * p * y) * z) * y⁻¹ := by group
        _ = y * (z * (y⁻¹ * p * y)) * y⁻¹ := by rw [h1]
        _ = (y * z * y⁻¹) * p := by group
    rcases hcen _ hyzQ hcz with h | h
    · exfalso
      apply hz1
      calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
    · calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [h]
  rcases hcen q' hq' hq'c with h1 | hz'
  · rw [h1] at hk
    calc σ y = y * (y⁻¹ * w) := by rw [hw]; group
      _ = y := by rw [← hv, hk]; group
  · exfalso
    have hwy : w = y * z := by
      calc w = y * (y⁻¹ * w) := by group
        _ = y * z := by rw [← hv, hk, hz']
    have hcm : Commute y z := hyz
    have : (y * z) ^ 3 = z := by
      rw [hcm.mul_pow, hy3, one_mul]
      rw [pow_three, hz2, mul_one]
    rw [hwy, this] at hw3
    exact hz1 hw3

theorem fixed_of_normalizes_q8 {L Q : Subgroup Γ} {y z : Γ} (σ : Γ →* Γ) (hQL : Q ≤ L)
    (hQn : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) (e : ↥Q ≃* QuaternionGroup 2)
    (hLgen : L = Q ⊔ Subgroup.zpowers y) (hy3 : y ^ 3 = 1) (hyact : ∃ q ∈ Q, y * q ≠ q * y)
    (hz : z ∈ Q) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hσL : ∀ l ∈ L, σ l ∈ L) (hσQ : ∀ q ∈ Q, σ q = q) :
    ∀ l ∈ L, σ l = l := by
  obtain ⟨h2, hzc, hcen⟩ := TwinExitPf5.q8_facts e hz hz1 hz2
  exact fixed_of_normalizes σ hQL hQn h2 hLgen hy3 hyact hz hzc hz1 hz2 hcen hσL hσQ

end Aut

section SL2

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem sl2_exists_order_three :
    ∃ y₀ : SL(2, ZMod 3), y₀ ^ 3 = 1 ∧ y₀ ≠ 1 ∧ ∃ g : SL(2, ZMod 3), g * y₀ ≠ y₀ * g := by
  decide +kernel

theorem exists_gen_of_sl2 {L Q : Subgroup Γ} (e : ↥L ≃* SL(2, ZMod 3)) (hQL : Q ≤ L)
    (hQc : Nat.card Q = 8) :
    ∃ y ∈ L, y ^ 3 = 1 ∧ L = Q ⊔ Subgroup.zpowers y ∧ ∃ q ∈ Q, y * q ≠ q * y := by
  obtain ⟨y₀, hy₀3, hy₀1, g₀, hg₀⟩ := sl2_exists_order_three
  set y : ↥L := e.symm y₀ with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, hy₀3, map_one]
  have hy1 : y ≠ 1 := fun h => hy₀1 (by simpa [hy] using congrArg e h)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hord' : orderOf (y : Γ) = 3 := by rw [Subgroup.orderOf_coe]; exact hord
  have hyL : (y : Γ) ∈ L := y.2
  have hL24 : Nat.card L = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hS : Q ⊔ Subgroup.zpowers (y : Γ) ≤ L :=
    sup_le hQL (Subgroup.zpowers_le.mpr hyL)
  have h8 : 8 ∣ Nat.card ↥(Q ⊔ Subgroup.zpowers (y : Γ)) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Q ≤ Q ⊔ Subgroup.zpowers (y : Γ))
    rwa [hQc] at this
  have h3 : 3 ∣ Nat.card ↥(Q ⊔ Subgroup.zpowers (y : Γ)) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers (y : Γ) ≤
      Q ⊔ Subgroup.zpowers (y : Γ))
    rwa [Nat.card_zpowers, hord'] at this
  have h24 : 24 ∣ Nat.card ↥(Q ⊔ Subgroup.zpowers (y : Γ)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 8) (n := 3) (by norm_num) h8 h3
  have hle : Nat.card ↥(Q ⊔ Subgroup.zpowers (y : Γ)) ≤ 24 := by
    rw [← hL24]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hS)
  have hSc : Nat.card ↥(Q ⊔ Subgroup.zpowers (y : Γ)) = 24 := by
    have := Nat.le_of_dvd Nat.card_pos h24
    omega
  have hLeq : L = Q ⊔ Subgroup.zpowers (y : Γ) :=
    (Subgroup.eq_of_le_of_card_ge hS (by rw [hL24, hSc])).symm
  refine ⟨y, hyL, by exact_mod_cast congrArg Subtype.val hy3, hLeq, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcentr : L ≤ Subgroup.centralizer ({(y : Γ)} : Set Γ) := by
    refine hLeq.le.trans (sup_le (fun q hq => ?_) (Subgroup.zpowers_le.mpr ?_))
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcon q hq).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
  have hl : (e.symm g₀ : Γ) ∈ Subgroup.centralizer ({(y : Γ)} : Set Γ) := hcentr (e.symm g₀).2
  rw [Subgroup.mem_centralizer_singleton_iff] at hl
  have h1 : (e.symm g₀) * y = y * (e.symm g₀) := Subtype.ext hl
  have h2 := congrArg e h1
  simp only [map_mul, hy, MulEquiv.apply_symm_apply] at h2
  exact hg₀ h2

end SL2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
