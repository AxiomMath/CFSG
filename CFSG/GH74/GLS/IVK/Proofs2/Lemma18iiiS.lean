module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

@[expose] def GoodS {F : Type} [Field F] (p : ℕ) (t s : F) : Prop :=
  s ^ 2 * (t ^ 2 - 4 - s ^ 2) ≠ 0 ∧ s ^ 2 * (t ^ 2 - 4 - s ^ 2) ≠ 4 ∧
    ((t ^ 2 = 1 ∨ t ^ 4 - 3 * t ^ 2 + 1 = 0) →
      (t ^ 2 - 2 - s ^ 2 ≠ 0 ∧ (t ^ 2 - 2 - s ^ 2) ^ 2 - 1 ≠ 0 ∧
        (p = 5 ∨ (t ^ 2 - 2 - s ^ 2) ^ 4 - 3 * (t ^ 2 - 2 - s ^ 2) ^ 2 + 1 ≠ 0)))

namespace Lemma18iii

open Polynomial

theorem exists_eval_ne_zero_fin {F : Type} [Field F] [Finite F] (f : F[X]) (hf : f ≠ 0)
    (h : f.natDegree < Nat.card F) : ∃ s : F, f.eval s ≠ 0 := by
  apply Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f hf
  rw [← Nat.cast_card]
  exact_mod_cast h

theorem exists_E {F : Type} [Field F] [Finite F] (d : F) (h : 7 < Nat.card F) :
    ∃ s : F, s ≠ 0 ∧ s ^ 2 - d ≠ 0 ∧ s ^ 4 - d * s ^ 2 + 4 ≠ 0 := by
  have hdeg : (X * (X ^ 2 - C d) * (X ^ 4 - C d * X ^ 2 + C 4) : F[X]).natDegree = 7 := by
    compute_degree!
  obtain ⟨s, hs⟩ := exists_eval_ne_zero_fin
    (X * (X ^ 2 - C d) * (X ^ 4 - C d * X ^ 2 + C 4) : F[X])
    (ne_zero_of_natDegree_gt (n := 0) (by omega)) (by omega)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_add, ne_eq, mul_eq_zero,
    not_or] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  exact ⟨s, h1, h2, h3⟩

theorem exists_E_R {F : Type} [Field F] [Finite F] (d c : F) (h : 21 < Nat.card F) :
    ∃ s : F, s ≠ 0 ∧ s ^ 2 - d ≠ 0 ∧ s ^ 4 - d * s ^ 2 + 4 ≠ 0 ∧ c - s ^ 2 ≠ 0 ∧
      c - 1 - s ^ 2 ≠ 0 ∧ c + 1 - s ^ 2 ≠ 0 ∧ (c - s ^ 2) ^ 4 - 3 * (c - s ^ 2) ^ 2 + 1 ≠ 0 := by
  have hdeg : ((X * (X ^ 2 - C d) * (X ^ 4 - C d * X ^ 2 + C 4)) *
      ((C c - X ^ 2) * (C (c - 1) - X ^ 2) * (C (c + 1) - X ^ 2) *
        ((C c - X ^ 2) ^ 4 - 3 * (C c - X ^ 2) ^ 2 + 1)) : F[X]).natDegree = 21 := by
    compute_degree!
  obtain ⟨s, hs⟩ := exists_eval_ne_zero_fin
    ((X * (X ^ 2 - C d) * (X ^ 4 - C d * X ^ 2 + C 4)) *
      ((C c - X ^ 2) * (C (c - 1) - X ^ 2) * (C (c + 1) - X ^ 2) *
        ((C c - X ^ 2) ^ 4 - 3 * (C c - X ^ 2) ^ 2 + 1)) : F[X])
    (ne_zero_of_natDegree_gt (n := 0) (by omega)) (by omega)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_add, eval_ofNat, eval_one, ne_eq,
    mul_eq_zero, not_or] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩, h7⟩ := hs
  exact ⟨s, h1, h2, h3, h4, h5, h6, h7⟩

variable {F : Type} [Field F]

theorem D_ne {t s : F} (hs : s ≠ 0) (h1 : s ^ 2 - (t ^ 2 - 4) ≠ 0)
    (h2 : s ^ 4 - (t ^ 2 - 4) * s ^ 2 + 4 ≠ 0) :
    s ^ 2 * (t ^ 2 - 4 - s ^ 2) ≠ 0 ∧ s ^ 2 * (t ^ 2 - 4 - s ^ 2) ≠ 4 := by
  refine ⟨mul_ne_zero (pow_ne_zero 2 hs) fun h => h1 ?_, fun h => h2 ?_⟩
  · linear_combination -h
  · linear_combination -h

theorem goodS_of_E_R {p : ℕ} {t s : F} (hs : s ≠ 0) (h1 : s ^ 2 - (t ^ 2 - 4) ≠ 0)
    (h2 : s ^ 4 - (t ^ 2 - 4) * s ^ 2 + 4 ≠ 0) (h3 : t ^ 2 - 2 - s ^ 2 ≠ 0)
    (h4 : t ^ 2 - 2 - 1 - s ^ 2 ≠ 0) (h5 : t ^ 2 - 2 + 1 - s ^ 2 ≠ 0)
    (h6 : (t ^ 2 - 2 - s ^ 2) ^ 4 - 3 * (t ^ 2 - 2 - s ^ 2) ^ 2 + 1 ≠ 0) : GoodS p t s := by
  obtain ⟨hD0, hD4⟩ := D_ne hs h1 h2
  refine ⟨hD0, hD4, fun _ => ⟨h3, ?_, Or.inr h6⟩⟩
  have : (t ^ 2 - 2 - s ^ 2) ^ 2 - 1 = (t ^ 2 - 2 - 1 - s ^ 2) * (t ^ 2 - 2 + 1 - s ^ 2) := by
    ring
  rw [this]
  exact mul_ne_zero h4 h5

theorem goodS_one_char3 [CharP F 3] {t : F} (ht : t ^ 2 ≠ 4)
    (hrel : t ^ 2 = 1 ∨ t ^ 4 - 3 * t ^ 2 + 1 = 0) : GoodS 3 t 1 := by
  have h3 : (3 : F) = 0 := by simpa using CharP.cast_eq_zero F 3
  have h : t ^ 4 + 1 = 0 := by
    rcases hrel with h1 | h1
    · exact absurd (by linear_combination h1 - h3) ht
    · linear_combination h1 + t ^ 2 * h3
  refine ⟨?_, ?_, fun _ => ⟨?_, ?_, Or.inr ?_⟩⟩
  · intro hD
    exact one_ne_zero (α := F) (by linear_combination 9 * h3 - h + (t ^ 2 + 5) * hD)
  · intro hD
    exact one_ne_zero (α := F) (by linear_combination h - (t ^ 2 + 9) * hD - 27 * h3)
  · intro hτ
    exact one_ne_zero (α := F) (by linear_combination h - (t ^ 2 + 3) * hτ - 3 * h3)
  · intro hX
    exact one_ne_zero (α := F) (by linear_combination hX - h + (2 * (t ^ 2 - 1)) * h3)
  · intro hW
    exact one_ne_zero (α := F)
      (by linear_combination (2 - 26 * t ^ 2) * h3 - hW + (t ^ 4 - 12 * t ^ 2 + 50) * h)

theorem seven_lt_card_of_char3 [Finite F] [CharP F 3] (h4 : 4 < Nat.card F) :
    7 < Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 3
  rw [Nat.card_eq_fintype_card, hn] at h4 ⊢
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra hlt
    have : (n : ℕ) = 1 := by have := n.pos; omega
    rw [this] at h4
    norm_num at h4
  calc 7 < 3 ^ 2 := by norm_num
    _ ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2

theorem goodS_map {K L : Type} [Field K] [Field L] (f : K →+* L) {p : ℕ} {t s : K}
    (h : GoodS p t s) : GoodS p (f t) (f s) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hinj := f.injective
  refine ⟨fun h => h1 (hinj ?_), fun h => h2 (hinj ?_), fun hrel => ?_⟩
  · simpa [map_ofNat] using h
  · simpa [map_ofNat] using h
  · have hrel' : t ^ 2 = 1 ∨ t ^ 4 - 3 * t ^ 2 + 1 = 0 := by
      rcases hrel with h | h
      · exact Or.inl (hinj (by simpa [map_ofNat] using h))
      · exact Or.inr (hinj (by simpa [map_ofNat] using h))
    obtain ⟨g1, g2, g3⟩ := h3 hrel'
    refine ⟨fun h => g1 (hinj ?_), fun h => g2 (hinj ?_), g3.imp id fun h h' => h (hinj ?_)⟩
    · simpa [map_ofNat] using h
    · simpa [map_ofNat] using h
    · simpa [map_ofNat] using h'

theorem exists_goodS_of_equiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) {p : ℕ}
    (h : ∀ t : K, t ^ 2 ≠ 4 → ∃ s : K, GoodS p t s) (t : L) (ht : t ^ 2 ≠ 4) :
    ∃ s : L, GoodS p t s := by
  obtain ⟨s, hs⟩ := h (e.symm t) fun h4 => ht (by simpa [map_ofNat] using congrArg e h4)
  exact ⟨e s, by simpa using goodS_map e.toRingHom hs⟩

section SmallPrimes

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩
local instance fact_prime_seventeen : Fact (Nat.Prime 17) := ⟨by norm_num⟩
local instance fact_prime_nineteen : Fact (Nat.Prime 19) := ⟨by norm_num⟩

theorem small5 : ∀ t : ZMod 5, t ^ 2 ≠ 4 → ∃ s : ZMod 5, GoodS 5 t s := by
  unfold GoodS; decide

theorem small7 : ∀ t : ZMod 7, t ^ 2 ≠ 4 → ∃ s : ZMod 7, GoodS 7 t s := by
  unfold GoodS; decide

theorem small11 : ∀ t : ZMod 11, t ^ 2 ≠ 4 → ∃ s : ZMod 11, GoodS 11 t s := by
  unfold GoodS; decide

theorem small13 : ∀ t : ZMod 13, t ^ 2 ≠ 4 → ∃ s : ZMod 13, GoodS 13 t s := by
  unfold GoodS; decide

theorem small17 : ∀ t : ZMod 17, t ^ 2 ≠ 4 → ∃ s : ZMod 17, GoodS 17 t s := by
  unfold GoodS; decide

theorem small19 : ∀ t : ZMod 19, t ^ 2 ≠ 4 → ∃ s : ZMod 19, GoodS 19 t s := by
  unfold GoodS; decide

end SmallPrimes

theorem small_prime (p : ℕ) [Fact p.Prime]
    (hp : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) :
    ∀ t : ZMod p, t ^ 2 ≠ 4 → ∃ s : ZMod p, GoodS p t s := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [small5, small7, small11, small13, small17, small19]

theorem prime_cases {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h21 : p ≤ 21) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
  interval_cases p <;> first | omega | (exfalso; norm_num at hp)

theorem exists_goodS_small [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hodd : Odd (Nat.card F)) (hp3 : p ≠ 3) (hsmall : Nat.card F ≤ 21) (t : F)
    (ht : t ^ 2 ≠ 4) : ∃ s : F, GoodS p t s := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpp, hn⟩ := FiniteField.card F p
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hcard] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' n.ne_zero).2 even_two)
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by have := hpp.two_le; omega
    subst h4
    norm_num at hpp
  have hn1 : (n : ℕ) = 1 := by
    by_contra hne
    have h2 : 2 ≤ (n : ℕ) := by have := n.pos; omega
    have h1 : p ^ 2 ≤ p ^ (n : ℕ) := Nat.pow_le_pow_right hpp.pos h2
    have h3 : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
    omega
  have hpF : Fintype.card F = p := by rw [hn, hn1, pow_one]
  have hple : p ≤ 21 := by
    calc p = Nat.card F := by rw [hcard, hn1, pow_one]
      _ ≤ 21 := hsmall
  exact exists_goodS_of_equiv (ZMod.ringEquivOfPrime F hpp hpF)
    (small_prime p (prime_cases hpp hp5 hple)) t ht

end Lemma18iii

open Lemma18iii in
theorem exists_goodS {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hodd : Odd (Nat.card F)) (h4 : 4 < Nat.card F) (t : F) (ht : t ^ 2 ≠ 4) :
    ∃ s : F, GoodS p t s := by
  by_cases hp3 : p = 3
  · subst hp3
    by_cases hrel : t ^ 2 = 1 ∨ t ^ 4 - 3 * t ^ 2 + 1 = 0
    · exact ⟨1, goodS_one_char3 ht hrel⟩
    · obtain ⟨s, hs, h1, h2⟩ := exists_E (t ^ 2 - 4) (seven_lt_card_of_char3 h4)
      obtain ⟨hD0, hD4⟩ := D_ne hs h1 h2
      exact ⟨s, hD0, hD4, fun h => absurd h hrel⟩
  · by_cases hbig : 21 < Nat.card F
    · obtain ⟨s, hs, h1, h2, h3, h4, h5, h6⟩ := exists_E_R (t ^ 2 - 4) (t ^ 2 - 2) hbig
      exact ⟨s, goodS_of_E_R hs h1 h2 h3 h4 h5 h6⟩
    · exact exists_goodS_small hodd hp3 (not_lt.1 hbig) t ht

end CFSG.GH74.GLS.IVK.Proofs2
