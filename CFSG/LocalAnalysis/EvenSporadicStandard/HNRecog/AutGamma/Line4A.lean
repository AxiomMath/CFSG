module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.A8Glue

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Equiv Equiv.Perm CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem config_4A : ∃ β t₁ t₂ : alternatingGroup (Fin 8),
    TT β ∧ FF t₁ ∧ FF t₂ ∧ FF ((β * t₁) ^ 2) ∧ TT ((β * t₂) ^ 2) ∧ TT (t₁ * t₂) ∧
      TT ((β * (t₁ * t₂)) ^ 2) := by
  refine ⟨ttElem (swap 1 2 * swap 5 6) (by decide) (by decide),
    ffElem (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) (by decide) (by decide),
    ffElem (swap 0 3 * swap 1 2 * swap 4 5 * swap 6 7) (by decide) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem hasLine_4A (hF : IsF5Type a z) (hL : F5Local G a z) : HasLine a z .k4A .k4B .k4B := by
  obtain ⟨E⟩ := A8Emb.nonempty hL
  obtain ⟨β, t₁, t₂, hβ, h1, h2, h3, h4, h12, h5⟩ := config_4A
  refine ⟨E.φ β, E.isConj_a hβ, a * E.φ t₁, ⟨E.isConj_a_mul h1, ?_⟩, a * E.φ t₂,
    ⟨E.isConj_a_mul h2, ?_⟩, ?_⟩
  · rw [E.vertex_mul_a_mul, E.sq_a_mul hF]
    exact E.isConj_z h3
  · rw [E.vertex_mul_a_mul, E.sq_a_mul hF]
    exact E.isConj_a h4
  · rw [E.a_mul_a_mul hF]
    exact E.mem_orb4B h12 h5

theorem line_4A (hF : IsF5Type a z) (hL : F5Local G a z) :
    ∀ x ∈ orb4A a z a, ∃ y ∈ orb4B a a, x * y ∈ orb4B a a :=
  line_of_hasLine (k₁ := .k4A) (k₂ := .k4B) (k₃ := .k4B) (isConjOrbit_orb4A hL)
    (hasLine_4A hF hL)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
