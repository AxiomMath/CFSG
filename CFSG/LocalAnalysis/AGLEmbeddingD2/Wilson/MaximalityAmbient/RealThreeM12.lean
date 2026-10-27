module

public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def letM12 (l : ℤ) : NativeSporadic.M12 :=
  if l = 1 then m12a else if l = -1 then m12a⁻¹ else if l = 2 then m12b else m12b⁻¹

@[expose] def wordM12 (w : List ℤ) : NativeSporadic.M12 := (w.map letM12).prod

@[expose] def m12x : NativeSporadic.M12 :=
  wordM12 [1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2]

@[expose] def m12y : NativeSporadic.M12 :=
  wordM12 [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1,
    -2]

@[expose] def m12z : NativeSporadic.M12 := m12x * m12y * m12x⁻¹ * m12y⁻¹

@[expose] def m12f (p : Fin 3 × Fin 3 × Fin 3) : NativeSporadic.M12 :=
  m12x ^ (p.1 : ℕ) * m12y ^ (p.2.1 : ℕ) * m12z ^ (p.2.2 : ℕ)

@[expose] def m12tws : List (List ℤ) :=
  [[], [2, 1, 2, 1, -2, 1, -2], [2, 1, 2, 1, -2, 1, -2],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2],
    [1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2],
    [1, -2, 1, 2, 1], [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1, -2, 1, 2, 1],
    [1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2],
    [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1, -2, 1, 2, 1],
    [-2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2],
    [2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2], [1, -2, 1, 2, 1],
    [2, 1, 2, 1, -2, 1, -2], [2, 1, 2, 1, -2, 1, -2], [1, -2, 1, 2, 1],
    [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1, -2, 1, 2, 1],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [2, 1, 2, 1, -2, 1, -2],
    [2, 1, 2, 1, -2, 1, -2], [1, -2, 1, 2, 1], [1, -2, 1, 2, 1],
    [2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2],
    [-2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2]]

@[expose] def m12t (p : Fin 3 × Fin 3 × Fin 3) : NativeSporadic.M12 :=
  wordM12 (m12tws.getD (9 * (p.1 : ℕ) + 3 * (p.2.1 : ℕ) + (p.2.2 : ℕ)) [])

@[expose] def m12σx (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  (p.1 + 1, p.2.1, p.2.2 - p.2.1)

@[expose] def m12σy (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  (p.1, p.2.1 + 1, p.2.2)

theorem m12_gen_facts : m12x ^ 3 = 1 ∧ m12y ^ 3 = 1 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem m12f_inj : Function.Injective m12f := by
  intro p q h
  revert p q
  decide +kernel

theorem m12f_σx : ∀ p, m12f p * m12x = m12f (m12σx p) := by decide +kernel

theorem m12f_σy : ∀ p, m12f p * m12y = m12f (m12σy p) := by decide +kernel

theorem m12f_one : ∃ p, m12f p = 1 := ⟨(0, 0, 0), by decide +kernel⟩

theorem m12f_tinv : ∀ p, m12t p * m12f p * (m12t p)⁻¹ = (m12f p)⁻¹ := by decide +kernel

theorem m12f_mem : ∀ p, m12f p ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) := by
  intro p
  have hx : m12x ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) :=
    Subgroup.subset_closure (by simp)
  have hy : m12y ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) :=
    Subgroup.subset_closure (by simp)
  have hz : m12z ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) :=
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hz _)

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
