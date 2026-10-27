module

public import CFSG.HardMathSupport.Foote.E27.NormalAbelian
public import CFSG.HardMathSupport.Foote.E27.FusionTransfer

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_normal_abelian_of_equiv {J : Type*} [Group J] [Finite J]
    (h : E27Config X K R T z) (hz : z ∈ K) (e : ↥K ≃* J) (S A : Subgroup J)
    (hS : Nat.card ↥S = 3 ^ (Nat.card J).factorization 3) (hAS : A ≤ S)
    (hnorm : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1)
    (hcard : 3 ^ 7 ≤ Nat.card ↥A) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardS : Nat.card ↥(S.comap (e : ↥K →* J)) = 3 ^ (Nat.card ↥K).factorization 3 := by
    rw [card_comap_equiv, hS, Nat.card_congr e.toEquiv]
  refine h.false_of_normal_abelian hz (Sylow.ofCard (S.comap (e : ↥K →* J)) hcardS)
    (A.comap (e : ↥K →* J)) (Subgroup.comap_mono hAS) ?_ ?_ ?_ ?_
  · intro s hs a ha
    have hs' : e s ∈ S := hs
    have ha' : e a ∈ A := ha
    have := hnorm (e s) hs' (e a) ha'
    change e (s * a * s⁻¹) ∈ A
    rwa [map_mul, map_mul, map_inv]
  · intro a ha b hb
    apply e.injective
    rw [map_mul, map_mul]
    exact hcomm _ ha _ hb
  · intro a ha
    apply e.injective
    rw [map_pow, map_one]
    exact hexp _ ha
  · rw [card_comap_equiv]
    exact hcard

end CFSG.HardMathSupport.Foote.E27

end
