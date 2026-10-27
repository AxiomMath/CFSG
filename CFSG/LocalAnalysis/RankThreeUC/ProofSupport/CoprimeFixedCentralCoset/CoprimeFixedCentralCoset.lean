module

import Mathlib.Tactic.Group

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeFixedCentralCoset

theorem commutator_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (X : Subgroup G) (hX : ∀ x ∈ X, x ^ p = 1) (b g : G)
    (hb : ∀ x ∈ X, b * x = x * b) (hx : b * g * b⁻¹ * g⁻¹ ∈ X)
    (hcop : Nat.Coprime (orderOf b) p) : b * g * b⁻¹ * g⁻¹ = 1 := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = b * g * b⁻¹ * g⁻¹ := ⟨_, rfl⟩
  rw [← hxdef] at hx ⊢
  have hbx : b * x = x * b := hb x hx
  have key : ∀ n : ℕ, b ^ n * g * (b ^ n)⁻¹ = x ^ n * g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : b * g * b⁻¹ = x * g := by rw [hxdef]; group
      have hc : Commute b (x ^ n) := (Commute.pow_right (show Commute b x from hbx) n)
      calc b ^ (n + 1) * g * (b ^ (n + 1))⁻¹
          = b ^ n * (b * g * b⁻¹) * (b ^ n)⁻¹ := by
            rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
        _ = (b ^ n * x * (b ^ n)⁻¹) * (b ^ n * g * (b ^ n)⁻¹) := by
            rw [h1]; group
        _ = x ^ (n + 1) * g := by
            rw [ih]
            have : b ^ n * x * (b ^ n)⁻¹ = x := by
              have := (Commute.pow_left (show Commute b x from hbx) n)
              rw [this.eq]; simp
            rw [this, pow_succ', mul_assoc]
  have h2 : x ^ orderOf b = 1 := by
    have := key (orderOf b)
    rw [pow_orderOf_eq_one] at this
    simpa using this.symm
  have h3 : x ^ p = 1 := hX x hx
  have : orderOf x ∣ Nat.gcd (orderOf b) p := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeFixedCentralCoset
