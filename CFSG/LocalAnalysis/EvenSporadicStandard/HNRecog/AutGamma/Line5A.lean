module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.A8Glue

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Equiv Equiv.Perm CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem config_5A : ∃ β ξ η s : alternatingGroup (Fin 8),
    TT β ∧ TT ξ ∧ TT η ∧ ξ ≠ β ∧ (β * ξ) ^ 5 = 1 ∧ β * ξ ≠ 1 ∧ s ^ 3 = 1 ∧ s ≠ 1 ∧
      s * β = β * s ∧ s * ξ = ξ * s ∧ TT ((β * η) ^ 2) ∧ TT (ξ * η) ∧
        (β * (ξ * η)) ^ 6 = 1 ∧ (β * (ξ * η)) ^ 2 ≠ 1 ∧ (β * (ξ * η)) ^ 3 ≠ 1 ∧
          TT ((β * (ξ * η)) ^ 3) := by
  refine ⟨ttElem (swap 0 1 * swap 2 3) (by decide) (by decide),
    ttElem (swap 1 2 * swap 3 4) (by decide) (by decide),
    ttElem (swap 1 2 * swap 5 6) (by decide) (by decide),
    ⟨(swap 5 6 * swap 6 7 : Perm (Fin 8)), by rw [mem_alternatingGroup]; decide⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem hasLine_5A (hL : F5Local G a z) : HasLine a z .k5A .k4B .k6A := by
  obtain ⟨E⟩ := A8Emb.nonempty hL
  obtain ⟨β, ξ, η, s, hβ, hξ, hη, hne, h5, h1, hs3, hs1, hsβ, hsξ, h4, hξη, h6, h2, h3, hc⟩ :=
    config_5A
  refine ⟨E.φ β, E.isConj_a hβ, E.φ ξ, E.mem_orb5A hL hβ hξ hne h5 h1 hs3 hs1 hsβ hsξ,
    E.φ η, E.mem_orb4B hη h4, ?_⟩
  rw [← map_mul]
  exact E.mem_orb6A hξη h6 h2 h3 hc

theorem line_5A (hL : F5Local G a z) :
    ∀ x ∈ orb5A a a, ∃ y ∈ orb4B a a, x * y ∈ orb6A a a :=
  line_of_hasLine (k₁ := .k5A) (k₂ := .k4B) (k₃ := .k6A) (isConjOrbit_orb5A hL) (hasLine_5A hL)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
