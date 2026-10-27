module

public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.HardMathSupport.Foote.E27.Extraspecial

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_normal_special (h : E27Config X K R T z) (hz : z ∈ K)
    {J : Type*} [Group J] [Finite J] (φ : ↥K ≃* J) {Q L : Subgroup J} {k : ℕ} (hk : 4 ≤ k)
    (hQ : Nat.card Q = 3 ^ (2 * k + 1)) (hZ : Nat.card (center Q) = 3)
    (hcomm : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ center Q) (hcube : ∀ x : Q, x ^ 3 ∈ center Q)
    (hLQ : L ≤ normalizer (Q : Set J)) (hL : 3 ^ (Nat.card J).factorization 3 ∣ Nat.card L) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 hL
  refine h.false_of_centralizer_kill hz φ (P.map L.subtype) ?_ ?_
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hP]
  · rintro s ⟨p, -, rfl⟩ hs3 -
    exact eightyOne_dvd_card_centralizer_of_special hk hQ hZ hcomm hcube (hLQ p.2) hs3

end CFSG.HardMathSupport.Foote.E27
