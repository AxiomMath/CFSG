module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf Equiv Equiv.Perm

@[expose] def c₂ : A5 := ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.2 (by decide)⟩

@[expose] def c₃ : A5 := ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.2 (by decide)⟩

@[expose] def inversions (y : Fin 5 → Fin 5) : ℕ :=
  (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ y p.2 < y p.1).card

@[expose] def cls (x : A5) : Fin 5 :=
  if x = 1 then 0 else if x ^ 2 = 1 then 1 else if x ^ 3 = 1 then 2 else
    if inversions (fun i : Fin 5 => ((x : Perm (Fin 5)) ^ (i : ℕ)) 0) % 2 = 0 then 3 else 4

@[expose] def rep : Fin 5 → A5 := ![1, c₂, c₃, a₀, a₀ ^ 2]

@[expose] def ofSwaps (l : List (Fin 5 × Fin 5)) : A5 :=
  if h : Perm.sign ((l.map fun s => swap s.1 s.2).prod) = 1 then
    ⟨_, mem_alternatingGroup.2 h⟩ else 1

theorem exists_conj_rep : ∀ x : A5, ∃ y : A5, y * rep (cls x) * y⁻¹ = x := by
  decide +kernel

@[expose] def gramFn (b : Fin 5 → ZMod 2) (x : A5) : ZMod 2 := b (cls x)

@[expose] def b₁ : Fin 5 → ZMod 2 := ![0, 0, 0, 1, 1]

@[expose] def b₂ : Fin 5 → ZMod 2 := ![0, 0, 1, 0, 1]

@[expose] def b₃ : Fin 5 → ZMod 2 := ![0, 0, 1, 1, 0]

theorem eq_gramFn_comp_rep (f : A5 → ZMod 2) (hf : ∀ x y : A5, f (y * x * y⁻¹) = f x) :
    f = gramFn (f ∘ rep) := by
  funext x
  obtain ⟨y, hy⟩ := exists_conj_rep x
  simp only [gramFn, Function.comp]
  rw [← hf (rep (cls x)) y, hy]

end CFSG.EvenSporadicStandard.HNRecog.ML1
