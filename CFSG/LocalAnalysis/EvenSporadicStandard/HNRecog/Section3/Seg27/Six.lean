module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

structure Seg27Six (X : Subgroup (Equiv.Perm (Fin 8))) (p q : Fin 8) : Prop where
  le_alt : X ≤ alternatingGroup (Fin 8)
  card : Nat.card X = 60
  ne : p ≠ q
  fix_p : ∀ g ∈ X, g p = p
  fix_q : ∀ g ∈ X, g q = q
  card_stab : ∀ r, r ≠ p → r ≠ q →
    Nat.card (X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) r :
      Subgroup (Equiv.Perm (Fin 8))) = 10
  inv_fix2 : ∀ r s : Fin 8, ∃ t ∈ X, orderOf t = 2 ∧ t r = r ∧ t s = s

namespace Seg27Six

variable {X : Subgroup (Equiv.Perm (Fin 8))} {p q : Fin 8}

theorem symm (h : Seg27Six X p q) : Seg27Six X q p where
  le_alt := h.le_alt
  card := h.card
  ne := h.ne.symm
  fix_p := h.fix_q
  fix_q := h.fix_p
  card_stab r hq hp := h.card_stab r hp hq
  inv_fix2 := h.inv_fix2

theorem exists_moved (h : Seg27Six X p q) {r : Fin 8} (hp : r ≠ p) (hq : r ≠ q) :
    ∃ g ∈ X, g r ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hle : X ≤ MulAction.stabilizer (Equiv.Perm (Fin 8)) r := fun g hg =>
    MulAction.mem_stabilizer_iff.2 (by simpa [Equiv.Perm.smul_def] using hcon g hg)
  have h10 := h.card_stab r hp hq
  rw [inf_eq_left.2 hle, h.card] at h10
  exact absurd h10 (by norm_num)

theorem eq_or_eq_of_fixed (h : Seg27Six X p q) {r : Fin 8} (hr : ∀ g ∈ X, g r = r) :
    r = p ∨ r = q := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨g, hg, hgr⟩ := h.exists_moved hcon.1 hcon.2
  exact hgr (hr g hg)

end Seg27Six

end CFSG.EvenSporadicStandard.HNRecog.Section3
