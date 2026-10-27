module

public import CFSG.GH74.Generic.S1.KL3G2Fin
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape

public section

open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

namespace KL3G2

open Matrix CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem shape_mem_I₁ {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (h₁ : Nat.card F₁ = 3) (h₂ : Nat.card F₂ = 3) (Sh : Shape Y F₁ F₂) {g d : Y}
    (hd : orderOf d = 8) (hg : Odd (orderOf g)) (hgd : g * d = d * g) : g ∈ Sh.I₁ := by
  obtain ⟨π, -, hπk⟩ := Sh.exists_pglHom
  have hδ1 : π d ≠ 1 := by
    intro h1
    have hdI : d ∈ Sh.I₁ := by rw [← hπk]; exact h1
    apply KL3G2.sl2_orderOf_ne_eight h₁ (Sh.e₁ ⟨d, hdI⟩)
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hd
  have hmd : orderOf (π d) ∣ 8 := hd ▸ orderOf_map_dvd π d
  have hm1 : orderOf (π d) ≠ 1 := fun h => hδ1 (orderOf_eq_one_iff.1 h)
  have hex : ∃ k : ℕ, (π d ^ k) ^ 2 = 1 ∧ π d ^ k ≠ 1 := by
    obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf (π d) ∣ 2 ^ 3 from hmd)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hm1 hmi
    have h2m : 2 ∣ orderOf (π d) := by
      rw [hmi]
      exact dvd_pow_self 2 hi0
    have hmpos : 0 < orderOf (π d) := Nat.pos_of_dvd_of_pos hmd (by norm_num)
    obtain ⟨k, hk⟩ := h2m
    have hk0 : k ≠ 0 := by rintro rfl; omega
    have hdvd : k ∣ orderOf (π d) := ⟨2, by omega⟩
    have hord : orderOf (π d ^ k) = 2 := by
      rw [orderOf_pow_of_dvd hk0 hdvd, hk]
      exact Nat.mul_div_cancel 2 (Nat.pos_of_ne_zero hk0)
    refine ⟨k, ?_, ?_⟩
    · have := pow_orderOf_eq_one (π d ^ k)
      rwa [hord] at this
    · intro h1
      rw [h1, orderOf_one] at hord
      omega
  obtain ⟨k, hc2, hc1⟩ := hex
  have hcomm : π g * π d ^ k = π d ^ k * π g := by
    have h1 : Commute (π g) (π d) := by
      have := congrArg π hgd
      rw [map_mul, map_mul] at this
      exact this
    exact (h1.pow_right k).eq
  have h4 := KL3G2.pgl2_cent_four h₂ (π g) (π d ^ k) hc2 hc1 hcomm
  have hr : π g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hcop : Nat.Coprime 4 (orderOf g) := by
    have : Nat.Coprime 2 (orderOf g) := (Nat.coprime_two_left).2 hg
    simpa using Nat.Coprime.pow_left 2 this
  have : π g = 1 := by
    have := pow_gcd_eq_one.2 ⟨h4, hr⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [← hπk]
  exact this


theorem shape_odd_eq_one {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (h₁ : Nat.card F₁ = 3) (h₂ : Nat.card F₂ = 3) (Sh : Shape Y F₁ F₂) {g d : Y}
    (hd : orderOf d = 8) (hg : Odd (orderOf g)) (hgd : g * d = d * g) : g = 1 := by
  have hI₁ : g ∈ Sh.I₁ := shape_mem_I₁ h₁ h₂ Sh hd hg hgd
  have hI₂ : g ∈ Sh.I₂ := shape_mem_I₁ h₂ h₁ Sh.swap hd hg hgd
  have h12 : g ∈ Sh.I₁ ⊓ Sh.I₂ := ⟨hI₁, hI₂⟩
  rw [Sh.inter] at h12
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h12
  have hgg : g ^ 2 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, Sh.z_sq,
      one_zpow]
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hgg
  have hodd2 : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hg
      exact absurd hg (by decide)
  exact orderOf_eq_one_iff.1 hodd2

end KL3G2

end CFSG.GH74.Generic.S1
