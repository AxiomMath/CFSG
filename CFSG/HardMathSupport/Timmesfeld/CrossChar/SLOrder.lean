module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix

section Counting

variable {E : Type*} [Field E] [Finite E]

theorem dvd_card_SL_of_dvd_pow_sub_one {p m e : ℕ} (hp : p.Prime) (hQ : ¬ p ∣ Nat.card E - 1)
    (he : 1 ≤ e) (hem : e ≤ m) (h : p ∣ Nat.card E ^ e - 1) :
    p ∣ Nat.card (SpecialLinearGroup (Fin m) E) := by
  have : Fintype E := Fintype.ofFinite E
  have hm : NeZero m := ⟨by omega⟩
  have h1 := Matrix.card_SL_mul_card_units (n := Fin m) (R := E)
  rw [Matrix.card_GL_field, Nat.card_units] at h1
  have hmem : (⟨m - e, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  have hfac : p ∣ Fintype.card E ^ m - Fintype.card E ^ (m - e) := by
    have : Fintype.card E ^ m - Fintype.card E ^ (m - e) =
        Fintype.card E ^ (m - e) * (Fintype.card E ^ e - 1) := by
      have hpow : Fintype.card E ^ m = Fintype.card E ^ (m - e) * Fintype.card E ^ e := by
        rw [← pow_add]; congr 1; omega
      rw [Nat.mul_sub, mul_one, ← hpow]
    rw [this]
    exact Dvd.dvd.mul_left (by rwa [Nat.card_eq_fintype_card] at h) _
  have hprod : p ∣ ∏ i : Fin m, (Fintype.card E ^ m - Fintype.card E ^ (i : ℕ)) :=
    hfac.trans (Finset.dvd_prod_of_mem (fun i : Fin m =>
      Fintype.card E ^ m - Fintype.card E ^ (i : ℕ)) hmem)
  have h2 : p ∣ Nat.card (SpecialLinearGroup (Fin m) E) * (Fintype.card E - 1) := by
    rw [← Nat.card_eq_fintype_card] at h1 ⊢
    rw [h1]
    rwa [Nat.card_eq_fintype_card]
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · exact h3
  · exact absurd (by rwa [Nat.card_eq_fintype_card]) hQ

omit [Finite E] in
theorem exists_orderOf_SL {p m : ℕ} [Fact p.Prime] (hp : p.Prime) (hm : 2 ≤ m) {ζ : E}
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ s : SpecialLinearGroup (Fin m) E, orderOf s = p := by
  classical
  have i0 : Fin m := ⟨0, by omega⟩
  have i1 : Fin m := ⟨1, by omega⟩
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  let v : Fin m → E := fun i => if i = ⟨0, by omega⟩ then ζ else
    if i = ⟨1, by omega⟩ then ζ⁻¹ else 1
  have hdet : (Matrix.diagonal v).det = 1 := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ hne]
    · simp [v, hζ0]
    · intro c _ hc
      simp [v, hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  let s : SpecialLinearGroup (Fin m) E := ⟨Matrix.diagonal v, hdet⟩
  refine ⟨s, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    change (Matrix.diagonal v) ^ p = 1
    rw [Matrix.diagonal_pow]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq]
      by_cases h0 : i = ⟨0, by omega⟩
      · simp [v, h0, hζ.pow_eq_one]
      · by_cases h1 : i = ⟨1, by omega⟩
        · simp [v, h1, hne.symm, inv_pow, hζ.pow_eq_one]
        · simp [v, h0, h1]
    · simp [hij]
  · intro h1
    have := congrArg (fun s : SpecialLinearGroup (Fin m) E =>
      (s : Matrix (Fin m) (Fin m) E) ⟨0, by omega⟩ ⟨0, by omega⟩) h1
    simp only [s, v] at this
    simp at this
    exact hζ.ne_one hp.one_lt this

theorem dvd_card_SL_of_dvd_card_sub_one {p m : ℕ} (hp : p.Prime) (hm : 2 ≤ m)
    (h : p ∣ Nat.card E - 1) : p ∣ Nat.card (SpecialLinearGroup (Fin m) E) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Eˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζ : IsPrimitiveRoot (x : E) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)
  obtain ⟨s, hs⟩ := exists_orderOf_SL (E := E) hp hm hζ
  rw [← hs]
  exact orderOf_dvd_natCard s

end Counting

end CFSG.HardMathSupport.Timmesfeld.CrossChar
