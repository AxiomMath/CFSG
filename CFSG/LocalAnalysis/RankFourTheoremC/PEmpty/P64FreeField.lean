module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free

open Finset

theorem odd_geom_sum {p : ℕ} (hp : Odd p) : Odd (∑ i ∈ range p, p ^ i) := by
  rw [Nat.odd_iff, Finset.sum_nat_mod]
  have h : ∀ i ∈ range p, p ^ i % 2 = 1 := fun i _ => Nat.odd_iff.mp (hp.pow)
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_range, smul_eq_mul, mul_one]
  exact Nat.odd_iff.mp hp

theorem pow_self_sub_one_eq {p : ℕ} (hp : 1 ≤ p) :
    p ^ p - 1 = (p - 1) * ∑ i ∈ range p, p ^ i := by
  have h := geom_sum_mul (p : ℤ) p
  have h1 : (1 : ℤ) ≤ (p : ℤ) ^ p := by exact_mod_cast Nat.one_le_pow _ _ hp
  zify [Nat.one_le_pow p p hp, hp]
  push_cast
  linarith [h]

variable {F : Type*} [Field F] [Fintype F]

theorem not_isSquare_cast_of_not_isSquare {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [CharP F p]
    (hcard : Fintype.card F = p ^ p) {c : ZMod p} (hc : ¬ IsSquare c) :
    ¬ IsSquare (ZMod.castHom (dvd_refl p) F c) := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by simp⟩
  have hcharF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hcharZ : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hcZ : c ^ (p / 2) = -1 := by
    have h := FiniteField.pow_dichotomy hcharZ hc0
    rw [ZMod.card] at h
    rcases h with h | h
    · exact absurd ((FiniteField.isSquare_iff hcharZ hc0).mpr (by rw [ZMod.card]; exact h)) hc
    · exact h
  set cF := ZMod.castHom (dvd_refl p) F c
  have hcF0 : cF ≠ 0 := by
    intro h
    exact hc0 ((injective_iff_map_eq_zero _).mp (ZMod.castHom (dvd_refl p) F).injective c h)
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  set m := ∑ i ∈ range p, p ^ i
  have hm : Odd m := odd_geom_sum hpodd
  have hq : p ^ p / 2 = (p / 2) * m := by
    have h1 := pow_self_sub_one_eq hp.out.one_le
    have hp1 : p - 1 = 2 * (p / 2) := by
      obtain ⟨k, hk⟩ := hpodd
      omega
    have hq1 : 1 ≤ p ^ p := Nat.one_le_pow _ _ hp.out.pos
    rw [hp1, mul_assoc] at h1
    generalize p ^ p = Q at h1 hq1 ⊢
    generalize (p / 2) * m = K at h1 ⊢
    omega
  intro hsq
  have h := (FiniteField.isSquare_iff hcharF hcF0).mp hsq
  rw [hcard, hq, pow_mul] at h
  have hcF : cF ^ (p / 2) = -1 := by
    simp only [cF, ← map_pow, hcZ, map_neg, map_one]
  rw [hcF, hm.neg_one_pow] at h
  have h2 : (2 : F) = 0 := by
    have := congrArg (· + 1) h
    simp only [neg_add_cancel] at this
    rw [one_add_one_eq_two] at this
    exact this.symm
  exact hcharF (ringChar.eq_iff.mpr (by
    have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
    exact (CharP.cast_eq_zero_iff F p 2).mp this |> fun hdvd => absurd
      ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hdvd) hp2))

theorem exists_sq_mul_eq_cast_mul {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [CharP F p]
    (hcard : Fintype.card F = p ^ p) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ s : F, s ≠ 0 ∧ ∃ c : ZMod p, c ≠ 0 ∧ s ^ 2 * a = ZMod.castHom (dvd_refl p) F c * b := by
  have hcharF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hcharZ : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hx0 : b * a⁻¹ ≠ 0 := mul_ne_zero hb (inv_ne_zero ha)
  by_cases hx : IsSquare (b * a⁻¹)
  · obtain ⟨s, hs⟩ := hx
    refine ⟨s, fun h => hx0 (by rw [hs, h, mul_zero]), 1, one_ne_zero, ?_⟩
    rw [map_one, one_mul, pow_two, ← hs, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  · obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hcharZ
    have hcF := not_isSquare_cast_of_not_isSquare hp2 hcard hc
    set cF := ZMod.castHom (dvd_refl p) F c
    have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by simp⟩
    have hcF0 : cF ≠ 0 := by
      intro h
      exact hc0 ((injective_iff_map_eq_zero _).mp (ZMod.castHom (dvd_refl p) F).injective c h)
    have hy0 : cF * (b * a⁻¹) ≠ 0 := mul_ne_zero hcF0 hx0
    have hy : IsSquare (cF * (b * a⁻¹)) := by
      rw [FiniteField.isSquare_iff hcharF hy0, mul_pow]
      have h1 := FiniteField.pow_dichotomy hcharF hcF0
      have h2 := FiniteField.pow_dichotomy hcharF hx0
      have h1' : cF ^ (Fintype.card F / 2) = -1 :=
        h1.resolve_left fun h => hcF ((FiniteField.isSquare_iff hcharF hcF0).mpr h)
      have h2' : (b * a⁻¹) ^ (Fintype.card F / 2) = -1 :=
        h2.resolve_left fun h => hx ((FiniteField.isSquare_iff hcharF hx0).mpr h)
      rw [h1', h2', neg_one_mul, neg_neg]
    obtain ⟨s, hs⟩ := hy
    refine ⟨s, fun h => hy0 (by rw [hs, h, mul_zero]), c, hc0, ?_⟩
    rw [pow_two, ← hs, mul_assoc, mul_assoc, inv_mul_cancel₀ ha, mul_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free
