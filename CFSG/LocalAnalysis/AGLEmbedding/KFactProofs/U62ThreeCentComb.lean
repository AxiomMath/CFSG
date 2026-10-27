module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.AGLEmbedding.U62ThreeCent

@[expose] def doubleCycles : List (Fin 6 → Fin 6) :=
[
  ![1, 2, 0, 4, 5, 3], ![1, 2, 0, 5, 3, 4], ![1, 3, 4, 0, 5, 2], ![1, 3, 5, 0, 2, 4],
  ![1, 4, 3, 5, 0, 2], ![1, 4, 5, 2, 0, 3], ![1, 5, 3, 4, 2, 0], ![1, 5, 4, 2, 3, 0],
  ![2, 0, 1, 4, 5, 3], ![2, 0, 1, 5, 3, 4], ![2, 3, 4, 5, 0, 1], ![2, 3, 5, 4, 1, 0],
  ![2, 4, 3, 0, 5, 1], ![2, 4, 5, 1, 3, 0], ![2, 5, 3, 0, 1, 4], ![2, 5, 4, 1, 0, 3],
  ![3, 0, 4, 1, 5, 2], ![3, 0, 5, 1, 2, 4], ![3, 2, 4, 5, 1, 0], ![3, 2, 5, 4, 0, 1],
  ![3, 4, 0, 2, 5, 1], ![3, 4, 1, 5, 2, 0], ![3, 5, 0, 2, 1, 4], ![3, 5, 1, 4, 0, 2],
  ![4, 0, 3, 5, 1, 2], ![4, 0, 5, 2, 1, 3], ![4, 2, 3, 1, 5, 0], ![4, 2, 5, 0, 3, 1],
  ![4, 3, 0, 5, 2, 1], ![4, 3, 1, 2, 5, 0], ![4, 5, 0, 1, 2, 3], ![4, 5, 1, 0, 3, 2],
  ![5, 0, 3, 4, 2, 1], ![5, 0, 4, 2, 3, 1], ![5, 2, 3, 1, 0, 4], ![5, 2, 4, 0, 1, 3],
  ![5, 3, 0, 4, 1, 2], ![5, 3, 1, 2, 0, 4], ![5, 4, 0, 1, 3, 2], ![5, 4, 1, 0, 2, 3]
]

theorem comb_dichotomy : ∀ k : Fin 6 → ZMod 3,
    (∃ a b c : Fin 6, a < b ∧ b < c ∧ k a = k b ∧ k b = k c) ∨
    (∃ s ∈ doubleCycles, (∀ i, s (s (s i)) = i) ∧ (∃ i, s i ≠ i) ∧
      ∃ l : ZMod 3, ∀ i, k (s i) = k i + l) := by
  decide +kernel

theorem cycle_facts : ∀ a b c : Fin 6, a < b → b < c →
    (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 ∧ Equiv.swap a b * Equiv.swap b c ≠ 1 := by
  decide +kernel

theorem cycle_support : ∀ a b c i : Fin 6, a < b → b < c →
    (Equiv.swap a b * Equiv.swap b c) i = i ∨
      ((i = a ∨ i = b ∨ i = c) ∧ ((Equiv.swap a b * Equiv.swap b c) i = a ∨
        (Equiv.swap a b * Equiv.swap b c) i = b ∨ (Equiv.swap a b * Equiv.swap b c) i = c)) := by
  decide +kernel

theorem exists_cycle_perm (k : Fin 6 → ZMod 3) :
    ∃ σ : Equiv.Perm (Fin 6), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ ∃ l : ZMod 3, ∀ i, k (σ i) = k i + l := by
  rcases comb_dichotomy k with ⟨a, b, c, hab, hbc, hk1, hk2⟩ | ⟨s, -, h3, ⟨i0, hi0⟩, l, hl⟩
  · obtain ⟨hσ3, hσ1⟩ := cycle_facts a b c hab hbc
    refine ⟨Equiv.swap a b * Equiv.swap b c, hσ3, hσ1, 0, fun i => ?_⟩
    rw [add_zero]
    rcases cycle_support a b c i hab hbc with h | ⟨hi, hσ⟩
    · rw [h]
    · have hka : k a = k a := rfl
      have hkb : k b = k a := hk1.symm
      have hkc : k c = k a := hk2.symm.trans hk1.symm
      have hi' : k i = k a := by rcases hi with rfl | rfl | rfl <;> assumption
      have hσ' : k ((Equiv.swap a b * Equiv.swap b c) i) = k a := by
        rcases hσ with h | h | h <;> rw [h] <;> assumption
      rw [hi', hσ']
  · let σ : Equiv.Perm (Fin 6) :=
      { toFun := s
        invFun := fun i => s (s i)
        left_inv := fun i => h3 i
        right_inv := fun i => h3 i }
    have hσ3 : σ ^ 3 = 1 := Equiv.ext fun i => h3 i
    refine ⟨σ, hσ3, fun h => hi0 ?_, l, hl⟩
    have := congrArg (fun τ : Equiv.Perm (Fin 6) => τ i0) h
    exact this

end CFSG.AGLEmbedding.U62ThreeCent
