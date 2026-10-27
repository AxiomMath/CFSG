module

import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

namespace Representation

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_finrank_eq_pow_of_card_eq_prime_pow {p a : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ a) (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible] :
    ∃ b ≤ a, finrank ℂ V = p ^ b := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  have hdvd := finrank_dvd_card ρ
  rw [hcard] at hdvd
  exact (Nat.dvd_prime_pow hp).1 hdvd

theorem exists_character_one_eq_pow_of_card_eq_prime_pow {p a : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ a) (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible] :
    ∃ b ≤ a, ρ.character 1 = (p : ℂ) ^ b := by
  obtain ⟨b, hb, hfr⟩ := exists_finrank_eq_pow_of_card_eq_prime_pow hp hcard ρ
  have := nontrivial_of_isIrreducible ρ ‹_›
  refine ⟨b, hb, ?_⟩
  rw [ρ.char_one, hfr]
  push_cast
  ring

end Representation

theorem Irr.exists_one_eq_pow_of_card_eq_prime_pow {p a : ℕ} (hp : p.Prime) {P : Type*} [Group P]
    (hcard : Nat.card P = p ^ a) {χ : P → ℂ} (hχ : χ ∈ Irr P) :
    ∃ b ≤ a, χ 1 = (p : ℂ) ^ b := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨n, -, hχ1, hdvd⟩ := Irr.exists_degree hχ
  rw [hcard] at hdvd
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨b, hb, by rw [hχ1]; push_cast; ring⟩

theorem irreducibleCharacters.exists_one_eq_pow_of_card_eq_prime_pow {p a : ℕ} (hp : p.Prime)
    {P : Type*} [Group P] (hcard : Nat.card P = p ^ a) {χ : P → ℂ}
    (hχ : χ ∈ irreducibleCharacters P) : ∃ b ≤ a, χ 1 = (p : ℂ) ^ b := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨n, -, hχ1, hdvd⟩ := irreducibleCharacters.exists_degree hχ
  rw [hcard] at hdvd
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨b, hb, by rw [hχ1]; push_cast; ring⟩

end CFSG.FeitThompson
