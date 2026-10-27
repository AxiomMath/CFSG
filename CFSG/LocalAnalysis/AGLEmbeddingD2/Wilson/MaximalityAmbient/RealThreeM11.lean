module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.M11PinnedInputs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def letM11 (l : ℤ) : NativeSporadic.M11 :=
  if l = 1 then m11a else if l = -1 then m11a⁻¹ else if l = 2 then m11b else m11b⁻¹

@[expose] def wordM11 (w : List ℤ) : NativeSporadic.M11 := (w.map letM11).prod

@[expose] def m11x : NativeSporadic.M11 := wordM11 [1, 2, 1, 2, 2, 1, -2]

@[expose] def m11y : NativeSporadic.M11 := wordM11 [1, -2, 1, 2, 1, -2, 1, 2]

@[expose] def m11t : NativeSporadic.M11 := wordM11 [1]

theorem m11_pair_facts :
    m11x * m11y = m11y * m11x ∧ m11x ^ 3 = 1 ∧ m11y ^ 3 = 1 ∧
      m11t * m11x * m11t⁻¹ = m11x⁻¹ ∧ m11t * m11y * m11t⁻¹ = m11y⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem m11_pair_inj :
    Function.Injective fun p : Fin 3 × Fin 3 => m11x ^ (p.1 : ℕ) * m11y ^ (p.2 : ℕ) := by
  intro p q h
  revert p q
  decide +kernel

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
