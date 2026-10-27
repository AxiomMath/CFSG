module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19M

open CFSG.ClassicalInvolution.Generic

variable {K E : Type*} [Group K] [Group E]

theorem pow_natCard_mul_self {N : Subgroup K} [Finite N] {y : K} (hy : y * y ∈ N) :
    y ^ Nat.card N * y ^ Nat.card N = 1 := by
  have h1 : (⟨y * y, hy⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
  have h2 : (y * y) ^ Nat.card N = 1 := by
    have := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    exact this
  rw [← pow_add, ← two_mul, pow_mul, sq, h2]

theorem map_pow_natCard_ker {ψ : K →* E} (hodd : Odd (Nat.card ψ.ker)) {y : K}
    (hy : ψ y * ψ y = 1) : ψ (y ^ Nat.card ψ.ker) = ψ y := by
  obtain ⟨k, hk⟩ := hodd
  rw [map_pow, hk, pow_succ, pow_mul, sq, hy, one_pow, one_mul]

theorem exists_involution_lift {ψ : K →* E} (hψ : Function.Surjective ψ) [Finite ψ.ker]
    (hodd : Odd (Nat.card ψ.ker)) {x : E} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ y : K, y * y = 1 ∧ y ≠ 1 ∧ ψ y = x := by
  obtain ⟨y₀, rfl⟩ := hψ x
  have hy₀ : y₀ * y₀ ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, hx]
  refine ⟨y₀ ^ Nat.card ψ.ker, pow_natCard_mul_self hy₀, fun h => hx1 ?_,
    map_pow_natCard_ker hodd hx⟩
  rw [← map_pow_natCard_ker hodd hx, h, map_one]

theorem isUniqueInvolution_map {ψ : K →* E} [Finite ψ.ker] (hodd : Odd (Nat.card ψ.ker))
    {R : Subgroup K} {c : K} (hc : IsUniqueInvolution R c) :
    IsUniqueInvolution (R.map ψ) (ψ c) where
  mem := Subgroup.mem_map_of_mem ψ hc.mem
  ne_one := by
    intro h
    have hord : orderOf c = 2 := orderOf_eq_prime (by rw [sq, hc.sq]) hc.ne_one
    have h2 : 2 ∣ Nat.card ψ.ker := hord ▸ Subgroup.orderOf_dvd_natCard ψ.ker h
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
  sq := by rw [← map_mul, hc.sq, map_one]
  unique := by
    rintro _ ⟨r, hr, rfl⟩ hr2
    have hrr : r * r ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, hr2]
    rcases hc.unique _ (R.pow_mem hr _) (pow_natCard_mul_self hrr) with h | h
    · left
      rw [← map_pow_natCard_ker hodd hr2, h, map_one]
    · right
      rw [← map_pow_natCard_ker hodd hr2, h]

theorem odd_natCard_ker [Finite K] {ψ : K →* E} (hker : ψ.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card (Subgroup.center K))) : Odd (Nat.card ψ.ker) :=
  Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19M
