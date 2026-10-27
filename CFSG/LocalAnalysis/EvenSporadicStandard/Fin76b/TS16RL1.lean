module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace LiftRL

variable {G : Type*} [Group G]

@[expose] def conjOrbit (H : Subgroup G) (x : G) : Set G := {y | ∃ h ∈ H, h * x * h⁻¹ = y}

theorem conjOrbit_card_mul (H : Subgroup G) (x : G) :
    (conjOrbit H x).ncard * Nat.card ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card H := by
  let _ : MulAction H G := MulAction.compHom G (MulAut.conj.comp H.subtype)
  have hsmul : ∀ (g : H) (y : G), g • y = (g : G) * y * (g : G)⁻¹ := fun _ _ => rfl
  have horb : Nat.card (MulAction.orbit H x) * Nat.card (MulAction.stabilizer H x) =
      Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  have hset : MulAction.orbit H x = conjOrbit H x := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, (hsmul g x).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, hsmul _ _⟩
  have h1 : Nat.card (MulAction.orbit H x) = (conjOrbit H x).ncard := by
    rw [← Nat.card_coe_set_eq, hset]
  have h2 : Nat.card (MulAction.stabilizer H x) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_congr ⟨fun g => ⟨g.1.1, Subgroup.mem_inf.2 ⟨g.1.2, ?_⟩⟩,
      fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · have hg := g.2
      rw [MulAction.mem_stabilizer_iff, hsmul] at hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g.1.1 * x = g.1.1 * x * (g.1.1)⁻¹ * g.1.1 := by group
        _ = x * g.1.1 := by rw [hg]
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
      show g.1 * x * g.1⁻¹ = x
      rw [hc, mul_inv_cancel_right]
  rw [← h1, ← h2]
  exact horb

theorem odd_card_of_odd_orders {H : Type*} [Group H] [Finite H] (S : Subgroup H)
    (hS : ∀ n ∈ S, Odd (orderOf n)) : Odd (Nat.card S) := by
  by_contra hodd
  have heven : 2 ∣ Nat.card S := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have h2 : Odd (orderOf (x : H)) := hS (x : H) x.2
  rw [Subgroup.orderOf_coe, hx] at h2
  exact absurd h2 (by decide)

theorem card_comap_surj {M Γ : Type*} [Group M] [Finite M] [Group Γ] [Finite Γ]
    (φ : M →* Γ) (hφ : Function.Surjective φ) (C : Subgroup Γ) :
    Nat.card (C.comap φ) = Nat.card φ.ker * Nat.card C := by
  have h1 := Subgroup.card_mul_index (C.comap φ)
  have h2 := Subgroup.card_mul_index C
  have h3 := Subgroup.card_ker_mul_card_of_surjective hφ
  rw [Subgroup.index_comap_of_surjective C hφ] at h1
  have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h3, ← h2]
  ring

theorem mem_zpowers_involution {t z : G} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hz : z ∈ Subgroup.zpowers t) : z = 1 ∨ z = t := by
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hk := zpow_mod_orderOf t k
  rw [hord] at hk
  push_cast at hk
  rw [← hk]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

theorem mem_conjOrbit_of_involution {N : Subgroup G} {η n : G} (hodd : Odd (orderOf n))
    (hnN : n ∈ N) (hη : η * η = 1) (hinv : (η * n) * (η * n) = 1) :
    η * n ∈ conjOrbit N η := by
  obtain ⟨j, hj⟩ := hodd
  have hpow : n ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one n
  have h1 : η * n * η * n = 1 := by simpa only [mul_assoc] using hinv
  have hconj : η * n * η = n⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hηinv : η⁻¹ = η := inv_eq_of_mul_eq_one_right hη
  have hcp : η * n ^ j * η = n⁻¹ ^ j := by
    have := conj_pow (a := η) (b := n) (i := j)
    rw [hηinv, hconj] at this
    exact this.symm
  have hinvpow : (n ^ j)⁻¹ = η * n ^ j * η := by
    rw [← inv_pow]
    exact hcp.symm
  have hsq : n ^ j * n ^ j = n⁻¹ := by
    have h2 : n ^ j * n ^ j * n = 1 := by
      rw [← pow_add, ← pow_succ, show j + j + 1 = 2 * j + 1 by omega]
      exact hpow
    exact eq_inv_of_mul_eq_one_left h2
  have hconj2 : n⁻¹ * η = η * n := by
    rw [← hconj]
    simp only [mul_assoc, hη, mul_one]
  have hfinal : n ^ j * η * (n ^ j)⁻¹ = η * n := by
    calc n ^ j * η * (n ^ j)⁻¹ = n ^ j * (η * η) * n ^ j * η := by
          rw [hinvpow]
          simp only [mul_assoc]
      _ = n ^ j * n ^ j * η := by rw [hη, mul_one]
      _ = n⁻¹ * η := by rw [hsq]
      _ = η * n := hconj2
  exact ⟨n ^ j, pow_mem hnN j, hfinal⟩

end LiftRL

end CFSG.EvenSporadicStandard.Fin76b
