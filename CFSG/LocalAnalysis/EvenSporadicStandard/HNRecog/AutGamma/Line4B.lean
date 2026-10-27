module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.A8Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.LineGlue

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Equiv Equiv.Perm CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem config_4B : ∃ β ξ η δ : alternatingGroup (Fin 8),
    TT β ∧ TT ξ ∧ TT η ∧ TT ((β * ξ) ^ 2) ∧ (β * η) ^ 3 = 1 ∧ β * η ≠ 1 ∧ TT δ ∧
      TT (β * δ) ∧ TT (η * δ) ∧ TT (ξ * η) ∧ (β * (ξ * η)) ^ 3 = 1 ∧ β * (ξ * η) ≠ 1 ∧
        TT ((ξ * η) * δ) := by
  refine ⟨ttElem (swap 0 1 * swap 4 5) (by decide) (by decide),
    ttElem (swap 0 2 * swap 1 3) (by decide) (by decide),
    ttElem (swap 1 3 * swap 4 5) (by decide) (by decide),
    ttElem (swap 4 5 * swap 6 7) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩ <;> decide

theorem hasLine_4B (hL : F5Local G a z) : HasLine a z .k4B .k3A .k3A := by
  obtain ⟨E⟩ := A8Emb.nonempty hL
  obtain ⟨β, ξ, η, δ, hβ, hξ, hη, hβξ, h3, h1, hδ, hβδ, hηδ, hξη, h3', h1', hξηδ⟩ := config_4B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have o1 : orderOf (E.φ β * E.φ η) = 3 := by
    rw [← map_mul, E.orderOf_φ]; exact orderOf_eq_prime h3 h1
  have o2 : orderOf (E.φ β * (E.φ ξ * E.φ η)) = 3 := by
    rw [← map_mul, ← map_mul, E.orderOf_φ]; exact orderOf_eq_prime h3' h1'
  have hd1 : E.φ δ ∈ orb2A a (E.φ β) := ⟨E.isConj_a hδ, by rw [← map_mul]; exact E.isConj_a hβδ⟩
  have hd2 : E.φ δ ∈ orb2A a (E.φ η) := ⟨E.isConj_a hδ, by rw [← map_mul]; exact E.isConj_a hηδ⟩
  have hd3 : E.φ δ ∈ orb2A a (E.φ ξ * E.φ η) :=
    ⟨E.isConj_a hδ, by rw [← map_mul, ← map_mul]; exact E.isConj_a hξηδ⟩
  refine ⟨E.φ β, E.isConj_a hβ, E.φ ξ, ⟨E.isConj_a hξ, ?_⟩, E.φ η,
    ⟨E.isConj_a hη, o1, E.φ δ, hd1, hd2⟩, ?_⟩
  · rw [← map_mul, ← map_pow]; exact E.isConj_a hβξ
  · rw [← map_mul] at hd3 ⊢
    exact ⟨E.isConj_a hξη, by rw [← map_mul] at o2; exact o2, E.φ δ, hd1, hd3⟩

theorem line_4B (hL : F5Local G a z) :
    ∀ x ∈ orb4B a a, ∃ y ∈ orb3A a a, x * y ∈ orb3A a a :=
  line_of_hasLine (k₁ := .k4B) (k₂ := .k3A) (k₃ := .k3A) (isConjOrbit_orb4B hL) (hasLine_4B hL)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
