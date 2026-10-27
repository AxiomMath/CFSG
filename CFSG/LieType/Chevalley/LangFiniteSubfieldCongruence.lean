module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect

public section

namespace CFSG.LieType.Chevalley

open Polynomial IntermediateField

theorem exceptional_Lang_finite_subfield_congruence_enlargement {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {k : Type*} [Field k] [IsAlgClosed k] [CharP k p] (E : Finset k)
    (hE : letI := ZMod.algebra k p; ∀ x ∈ E, IsAlgebraic (ZMod p) x) {M : ℕ} (_hM : 1 ≤ M) :
    ∃ K : Subfield k, Finite K ∧ (E : Set k) ⊆ K ∧ Nat.card K ≡ 1 [MOD 2 ^ M] := by
  let := ZMod.algebra k p
  have hfix : ∀ x ∈ E, ∃ n, 0 < n ∧ x ^ p ^ n = x := by
    intro x hx
    have hint := (hE x hx).isIntegral
    have := IntermediateField.adjoin.finiteDimensional hint
    have : Finite (ZMod p)⟮x⟯ := Module.finite_of_finite (ZMod p)
    let : Fintype (ZMod p)⟮x⟯ := Fintype.ofFinite _
    refine ⟨Module.finrank (ZMod p) (ZMod p)⟮x⟯, Module.finrank_pos, ?_⟩
    have h1 := FiniteField.pow_card
      (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : (ZMod p)⟮x⟯)
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card] at h1
    simpa using congrArg Subtype.val h1
  choose! n hn0 hn using hfix
  set N := Nat.totient (2 ^ M) * ∏ x ∈ E, n x with hN
  have hN0 : 0 < N := Nat.mul_pos (Nat.totient_pos.2 (by positivity))
    (Finset.prod_pos fun x hx => hn0 x hx)
  set q := p ^ N with hq
  have hq1 : 1 < q := Nat.one_lt_pow hN0.ne' hp.out.one_lt
  have hiter : ∀ (y : k) (a m : ℕ), y ^ p ^ a = y → y ^ p ^ (a * m) = y := by
    intro y a m h
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]
  set K : Subfield k := (iterateFrobenius k p N).eqLocusField (RingHom.id k) with hK
  have hmem : ∀ y, y ∈ K ↔ y ^ q = y := fun y => by
    change iterateFrobenius k p N y = y ↔ _
    rw [iterateFrobenius_def]
  have hroot : ∀ y : k, y ∈ (X ^ q - X : k[X]).rootSet k ↔ y ^ q = y := by
    intro y
    rw [mem_rootSet]
    simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
    exact ⟨fun h => h.2, fun h => ⟨FiniteField.X_pow_card_sub_X_ne_zero k hq1, h⟩⟩
  have hset : (K : Set k) = (X ^ q - X : k[X]).rootSet k :=
    Set.ext fun y => (hmem y).trans (hroot y).symm
  have hcard : Nat.card K = q := by
    have hsep : (X ^ q - X : k[X]).Separable := galois_poly_separable p q (dvd_pow_self p hN0.ne')
    have h1 := card_rootSet_eq_natDegree (K := k) hsep (IsAlgClosed.splits _)
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hq1] at h1
    rw [← h1, ← Nat.card_eq_fintype_card]
    change Nat.card ↥(K : Set k) = _
    rw [hset]
  refine ⟨K, Nat.finite_of_card_ne_zero (by omega), fun x hx => ?_, ?_⟩
  · rw [SetLike.mem_coe, hmem, hq, hN]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hx
    rw [hm, mul_left_comm]
    exact hiter x (n x) _ (hn x hx)
  · rw [hcard, hq, hN, pow_mul]
    have hcop : p.Coprime (2 ^ M) :=
      Nat.Coprime.pow_right M ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
    simpa using (Nat.ModEq.pow_totient hcop).pow (∏ x ∈ E, n x)

end CFSG.LieType.Chevalley
