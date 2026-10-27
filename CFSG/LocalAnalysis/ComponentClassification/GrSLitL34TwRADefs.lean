module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

@[expose] def RA : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure ((L34Facts.T0 : Set (Equiv.Perm (Fin 42))) ∪ {g₅, g₆})

@[expose] def Pw : Subgroup WrE where
  carrier := {x | x.a ∈ RA ∧ x.b ∈ RA}
  one_mem' := ⟨RA.one_mem, RA.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, WrE.mul_def]
    cases hye : y.e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨RA.mul_mem hx.1 hy.1, RA.mul_mem hx.2 hy.2⟩
    · simp only [↓reduceIte]
      exact ⟨RA.mul_mem hx.2 hy.1, RA.mul_mem hx.1 hy.2⟩
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, WrE.inv_def]
    cases hxe : x.e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨RA.inv_mem hx.1, RA.inv_mem hx.2⟩
    · simp only [↓reduceIte]
      exact ⟨RA.inv_mem hx.2, RA.inv_mem hx.1⟩

@[expose] def N0w : Subgroup WrE where
  carrier := {x | x.e = false ∧ x.a ∈ L34Facts.T0 ∧ x.b ∈ L34Facts.T0}
  one_mem' := ⟨rfl, L34Facts.T0.one_mem, L34Facts.T0.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, WrE.mul_def, hy.1]
    simp only [Bool.false_eq_true, ↓reduceIte, hx.1, Bool.xor_false, true_and]
    exact ⟨L34Facts.T0.mul_mem hx.2.1 hy.2.1, L34Facts.T0.mul_mem hx.2.2 hy.2.2⟩
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, WrE.inv_def, hx.1]
    simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    exact ⟨L34Facts.T0.inv_mem hx.2.1, L34Facts.T0.inv_mem hx.2.2⟩

end CFSG.ComponentClassification.GrSLit.L34Tw
