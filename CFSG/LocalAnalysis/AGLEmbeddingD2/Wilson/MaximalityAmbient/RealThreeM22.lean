module

public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def letM22 (l : ℤ) : NativeSporadic.M22 :=
  if l = 1 then m22a else if l = -1 then m22a⁻¹ else if l = 2 then m22b else m22b⁻¹

@[expose] def wordM22 (w : List ℤ) : NativeSporadic.M22 := (w.map letM22).prod

@[expose] def m22x : NativeSporadic.M22 := wordM22 [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2]

@[expose] def m22y : NativeSporadic.M22 := wordM22 [1, 2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2]

@[expose] def m22t : NativeSporadic.M22 := wordM22 [-2, 1, 2, 2, 1, 2]

theorem m22_pair_facts :
    m22x * m22y = m22y * m22x ∧ m22x ^ 3 = 1 ∧ m22y ^ 3 = 1 ∧
      m22t * m22x * m22t⁻¹ = m22x⁻¹ ∧ m22t * m22y * m22t⁻¹ = m22y⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem m22_pair_inj :
    Function.Injective fun p : Fin 3 × Fin 3 => m22x ^ (p.1 : ℕ) * m22y ^ (p.2 : ℕ) := by
  intro p q h
  revert p q
  decide +kernel

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
