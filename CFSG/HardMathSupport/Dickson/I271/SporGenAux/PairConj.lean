module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

variable {G : Type*} [Group G]

theorem card_closure_pair [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y : G}
    (hcomm : x * y = y * x) (hx : x ^ p = 1) (hy : y ^ p = 1) (hx1 : x ≠ 1)
    (hpow : ∀ k < p, y ≠ x ^ k) (hfac : (Nat.card G).factorization p = 2) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
  have hG : ¬ p ^ 3 ∣ Nat.card G := by
    intro h
    have h0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have := (hp.out.pow_dvd_iff_le_factorization h0).1 h
    omega
  have hQ := card_closure_pair_eq_sq hcomm hx hy hx1 hpow hG
  rw [hQ, Subgroup.card_top, hfac]

theorem exists_conj_of_pair [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y z : G}
    (hcomm : x * y = y * x) (hx : x ^ p = 1) (hy : y ^ p = 1) (hx1 : x ≠ 1)
    (hpow : ∀ k < p, y ≠ x ^ k) (hfac : (Nat.card G).factorization p = 2)
    (hconj : ∀ i j : ℕ, i < p → j < p → i + j ≠ 0 → ∃ m : G, m * (x ^ i * y ^ j) = z * m)
    (s : G) (hs : orderOf s = p) : ∃ c : G, c * s * c⁻¹ = z := by
  have hQfull := card_closure_pair hcomm hx hy hx1 hpow hfac
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨i, hi, j, hj, hw⟩ := exists_pow_mul_pow_of_mem hp.out.pos hcomm hx hy hgQ
  have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
  have hij : i + j ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    rw [hi0, hj0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  obtain ⟨m, hm⟩ := hconj i j hi hj hij
  refine ⟨m * g⁻¹, ?_⟩
  rw [← hw] at hm
  calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
    _ = z := by rw [hm]; group

end CFSG.HardMathSupport.Dickson.I271
