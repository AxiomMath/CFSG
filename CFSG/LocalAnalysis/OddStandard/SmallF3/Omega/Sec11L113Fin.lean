module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def Sec113TypeA (σ : Equiv.Perm (Fin 6)) : Prop :=
  ∃ a b : Fin 6, 2 ≤ a ∧ 2 ≤ b ∧ a ≠ b ∧ σ = Equiv.swap 0 1 * Equiv.swap a b

@[expose] def Sec113TypeS (σ : Equiv.Perm (Fin 6)) : Prop :=
  ∃ a b : Fin 6, 2 ≤ a ∧ 2 ≤ b ∧ a ≠ b ∧ σ = Equiv.swap a b

structure Sec113Shape (σ : Equiv.Perm (Fin 6)) : Prop where
  pres : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)
  ex : ∃ a b c : Fin 6, 2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ σ a = b ∧ σ c = c

theorem Sec113TypeA.shape {σ : Equiv.Perm (Fin 6)} (h : Sec113TypeA σ) : Sec113Shape σ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · revert a b; decide +kernel
  · revert a b; decide +kernel

theorem Sec113TypeS.shape {σ : Equiv.Perm (Fin 6)} (h : Sec113TypeS σ) : Sec113Shape σ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · revert a b; decide +kernel
  · revert a b; decide +kernel

theorem sec113_single_add_sum (i j : Fin 6) :
    ∑ l, (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) : Fin 6 → ZMod 2) l = 0 := by
  revert i j
  decide +kernel

theorem sec113_single_sum (i : Fin 6) : ∑ l, (Pi.single i (1 : ZMod 2) : Fin 6 → ZMod 2) l = 1 := by
  revert i
  decide +kernel

theorem sec113_e0_add_ne (k : Fin 6) (hk : 2 ≤ k) :
    (Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single k (1 : ZMod 2) : Fin 6 → ZMod 2) 0 ≠
      (Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single k (1 : ZMod 2) : Fin 6 → ZMod 2) 1 := by
  revert k
  decide +kernel

theorem sec113_pair_eq (a c : Fin 6) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    (Pi.single a (1 : ZMod 2) + Pi.single c (1 : ZMod 2) : Fin 6 → ZMod 2) 0 =
      (Pi.single a (1 : ZMod 2) + Pi.single c (1 : ZMod 2) : Fin 6 → ZMod 2) 1 := by
  revert a c; decide +kernel

theorem sec113_ab_ne (a b : Fin 6) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    ¬ ((Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2) : Fin 6 → ZMod 2) = 0 ∨
      (Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2) : Fin 6 → ZMod 2) = fun _ => 1) := by
  revert a b; decide +kernel

theorem sec113_ab_z_ne (a b : Fin 6) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    ¬ ((Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2) +
        (Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single (1 : Fin 6) (1 : ZMod 2)) :
          Fin 6 → ZMod 2) = 0 ∨
      (Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2) +
        (Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single (1 : Fin 6) (1 : ZMod 2)) :
          Fin 6 → ZMod 2) = fun _ => 1) := by
  revert a b; decide +kernel

end CFSG.OddStandard.SmallF3.Omega
