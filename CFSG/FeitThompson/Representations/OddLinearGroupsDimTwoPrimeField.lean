module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Representations.OddLinearGroupsDimTwo
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix Subgroup

variable {p : ℕ}

theorem exists_cyclic_normal_sylow_of_odd_prime_field (hp : p.Prime)
    {G : Subgroup (GL (Fin 2) (ZMod p))} (hGodd : Odd (Nat.card G)) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal ∧ IsCyclic (P : Subgroup G) ∧
      (Nat.card (P : Subgroup G) = 1 ∨ Nat.card (P : Subgroup G) = p) ∧
      _root_.commutator G ≤ (P : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hnorm, -, hcomm, hdvd, -⟩ :=
    exists_normal_abelian_sylow_of_odd (k := ZMod p) (p := p) hp hGodd
  rw [Nat.card_zmod] at hdvd
  exact ⟨P, hnorm, isCyclic_of_card_dvd_prime hdvd, (Nat.dvd_prime hp).mp hdvd, hcomm⟩

theorem isMulCommutative_of_odd_of_not_dvd_prime_field (hp : p.Prime)
    {G : Subgroup (GL (Fin 2) (ZMod p))} (hGodd : Odd (Nat.card G))
    (hnd : ¬ p ∣ Nat.card G) : IsMulCommutative G :=
  have : Fact p.Prime := ⟨hp⟩
  isMulCommutative_of_odd_of_not_dvd (p := p) hp hGodd hnd

theorem card_sylow_eq_and_commutator_le_of_dvd (hp : p.Prime)
    {G : Subgroup (GL (Fin 2) (ZMod p))} (hGodd : Odd (Nat.card G))
    (hdvd : p ∣ Nat.card G) (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p ∧ _root_.commutator G ≤ (P : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hnorm, -, hQcard, hcomm⟩ := exists_cyclic_normal_sylow_of_odd_prime_field hp hGodd
  have hQ : Nat.card (Q : Subgroup G) = p := by
    refine hQcard.resolve_left fun h1 => ?_
    rw [Q.card_eq_multiplicity, Nat.pow_eq_one] at h1
    have hpos := hp.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    rcases h1 with h1 | h1
    · exact hp.ne_one h1
    · omega
  have hPQ : P = Q := Subsingleton.elim (h := (Q.unique_of_normal hnorm).instSubsingleton) P Q
  rw [hPQ]
  exact ⟨hQ, hcomm⟩

theorem sylow_normal_of_odd_prime_field (hp : p.Prime)
    {G : Subgroup (GL (Fin 2) (ZMod p))} (hGodd : Odd (Nat.card G)) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hnorm, -, -, -⟩ := exists_cyclic_normal_sylow_of_odd_prime_field hp hGodd
  have hPQ : P = Q := Subsingleton.elim (h := (Q.unique_of_normal hnorm).instSubsingleton) P Q
  rw [hPQ]
  exact hnorm

theorem isCyclic_sylow_of_odd_prime_field (hp : p.Prime)
    {G : Subgroup (GL (Fin 2) (ZMod p))} (hGodd : Odd (Nat.card G)) (P : Sylow p G) :
    IsCyclic (P : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hnorm, hcyc, -, -⟩ := exists_cyclic_normal_sylow_of_odd_prime_field hp hGodd
  have hPQ : P = Q := Subsingleton.elim (h := (Q.unique_of_normal hnorm).instSubsingleton) P Q
  rw [hPQ]
  exact hcyc

end

end CFSG.FeitThompson
