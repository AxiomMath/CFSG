module

public import Mathlib.GroupTheory.PGroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamLift

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AY

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {g : G} {a : ℕ}
    (h : g ^ p ^ a = 1) : IsPGroup p (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ p ^ a := orderOf_dvd_of_pow_eq_one h
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp hd
  exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])

section Quot

variable {H : Type} [Group H] [Finite H]

theorem exists_pow_three_lift {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {v : H}
    (hv : v * v = 1) {q : H ⧸ N} (hq3 : q ^ 3 = 1)
    (hc : q * (QuotientGroup.mk v : H ⧸ N) = QuotientGroup.mk v * q) :
    ∃ y : H, (QuotientGroup.mk y : H ⧸ N) = q ∧ y * v = v * y ∧ ∃ a : ℕ, y ^ 3 ^ a = 1 := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨w, hwN, hwC⟩ := YGam.exists_mem_centralizer_of_quot_comm hN hv hc
  have hw1 : (QuotientGroup.mk w : H ⧸ N) = 1 := (QuotientGroup.eq_one_iff w).mpr hwN
  set z := w⁻¹ * y₀ with hz
  have hzq : (QuotientGroup.mk z : H ⧸ N) = QuotientGroup.mk y₀ := by
    rw [hz, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw1, inv_one, one_mul]
  have hzc : z * v = v * z := Subgroup.mem_centralizer_singleton_iff.mp hwC
  obtain ⟨a, r, hr, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 3 (by norm_num)
  have hr2 : r * r % 3 = 1 := by
    have : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  refine ⟨z ^ (r * r), ?_, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, hzq, pow_eq_pow_mod _ hq3, hr2, pow_one]
  · exact (Commute.pow_left (show Commute z v from hzc) _).eq
  · refine ⟨a, ?_⟩
    rw [← pow_mul, show r * r * 3 ^ a = (3 ^ a * r) * r by ring, ← hord, pow_mul,
      pow_orderOf_eq_one, one_pow]

end Quot

section Comm

theorem commutator_pow_ne_one {Q : Type*} [Group Q] {x q : Q} (hx : x * x = 1) (hnc : q * x ≠ x * q)
    (hc : (q * x * q⁻¹) * x = x * (q * x * q⁻¹)) {M : ℕ} (hM : Odd M) :
    (q * x * q⁻¹ * x⁻¹) ^ M ≠ 1 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  set a := q * x * q⁻¹ with ha
  have haa : a * a = 1 := by
    calc a * a = q * (x * x) * q⁻¹ := by rw [ha]; group
      _ = 1 := by rw [hx]; group
  have hd2 : (a * x) * (a * x) = 1 := by
    calc (a * x) * (a * x) = a * (x * a) * x := by group
      _ = a * (a * x) * x := by rw [← hc]
      _ = (a * a) * (x * x) := by group
      _ = 1 := by rw [haa, hx, one_mul]
  rw [hxi]
  intro h
  obtain ⟨k, rfl⟩ := hM
  have h1 : (a * x) ^ (2 * k + 1) = a * x := by
    rw [pow_succ, pow_mul, pow_two, hd2, one_pow, one_mul]
  rw [h1] at h
  have hax : a = x := by
    calc a = a * x * x := by rw [mul_assoc, hx, mul_one]
      _ = x := by rw [h, one_mul]
  apply hnc
  have : q * x * q⁻¹ = x := hax
  calc q * x = (q * x * q⁻¹) * q := by group
    _ = x * q := by rw [this]

theorem commutator_pow_card {Y : Type*} [Group Y] {O : Subgroup Y} {u e y o : Y}
    (hyu : y * u = u * y) (heO : ∀ g ∈ O, e * g * e⁻¹ ∈ O) (ho : o ∈ O)
    (h : y * e * y⁻¹ = o * e * o⁻¹) :
    (y * (u * e) * y⁻¹ * (u * e)⁻¹) ^ Nat.card O = 1 := by
  have hyu' : y * u * y⁻¹ = u := by rw [hyu]; group
  have hg : o * (e * o⁻¹ * e⁻¹) ∈ O := O.mul_mem ho (heO o⁻¹ (O.inv_mem ho))
  have h1 : y * (u * e) * y⁻¹ * (u * e)⁻¹ = u * (o * (e * o⁻¹ * e⁻¹)) * u⁻¹ := by
    calc y * (u * e) * y⁻¹ * (u * e)⁻¹ = (y * u * y⁻¹) * (y * e * y⁻¹) * (e⁻¹ * u⁻¹) := by group
      _ = u * (o * e * o⁻¹) * (e⁻¹ * u⁻¹) := by rw [h, hyu']
      _ = u * (o * (e * o⁻¹ * e⁻¹)) * u⁻¹ := by group
  have h2 : (o * (e * o⁻¹ * e⁻¹)) ^ Nat.card O = 1 := by
    have := pow_card_eq_one' (G := ↥O) (x := ⟨_, hg⟩)
    exact congrArg Subtype.val this
  rw [h1, conj_pow, h2]
  group

end Comm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AY
