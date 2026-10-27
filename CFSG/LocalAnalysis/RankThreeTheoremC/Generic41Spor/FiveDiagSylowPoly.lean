module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

open Polynomial

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagAux

theorem not_dvd_pow_sub_one {Q : ℕ} (hQ : 2 ≤ Q) (h5 : 5 ∣ Q - 1) (h25 : ¬ 25 ∣ Q - 1) {d : ℕ}
    (hd1 : 1 ≤ d) :
    (d ≤ 4 → ¬ 25 ∣ Q ^ d - 1) ∧ (d = 5 → ¬ 125 ∣ Q ^ d - 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hodd : Odd 5 := by decide
  have hQ1 : Q - 1 ≠ 0 := by omega
  have hv1 : padicValNat 5 (Q - 1) = 1 := by
    have h1 : 1 ≤ padicValNat 5 (Q - 1) := (padicValNat_dvd_iff_le hQ1).1 (by simpa using h5)
    have h2 : ¬ 2 ≤ padicValNat 5 (Q - 1) := fun h =>
      h25 (by simpa using (padicValNat_dvd_iff_le hQ1).2 h)
    omega
  have hLTE : padicValNat 5 (Q ^ d - 1) = 1 + padicValNat 5 d := by
    have := padicValNat.pow_sub_pow (p := 5) hodd (x := Q) (y := 1) (by omega) h5 (by omega)
      (n := d) (by omega)
    simpa [hv1] using this
  have hne : Q ^ d - 1 ≠ 0 := by
    have : 1 < Q ^ d := Nat.one_lt_pow (by omega) (by omega)
    omega
  constructor
  · intro hd4
    have hv : padicValNat 5 d = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    intro h
    have := (padicValNat_dvd_iff_le (p := 5) (n := 2) hne).1 (by simpa using h)
    omega
  · rintro rfl
    have hv : padicValNat 5 5 = 1 := padicValNat_self
    intro h
    have := (padicValNat_dvd_iff_le (p := 5) (n := 3) hne).1 (by simpa using h)
    omega

theorem pow_eq_one_of_isIntegral {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]
    (h5 : 5 ∣ Nat.card F - 1) (h25 : ¬ 25 ∣ Nat.card F - 1) {r : L} (hr : IsIntegral F r)
    {m : ℕ} (hrm : r ^ 5 ^ m = 1) :
    ((minpoly F r).natDegree ≤ 4 → r ^ 5 = 1) ∧ ((minpoly F r).natDegree = 5 → r ^ 25 = 1) := by
  have hirr : Irreducible (minpoly F r) := minpoly.irreducible hr
  have hdpos : 0 < (minpoly F r).natDegree := minpoly.natDegree_pos hr
  have hQ : 2 ≤ Nat.card F := Finite.one_lt_card
  have hdvd : minpoly F r ∣ (X ^ (Nat.card F) ^ (minpoly F r).natDegree - X : F[X]) :=
    hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.1 dvd_rfl
  have hrQ : r ^ (Nat.card F) ^ (minpoly F r).natDegree = r := by
    obtain ⟨c, hc⟩ := hdvd
    have h0 : aeval r (X ^ (Nat.card F) ^ (minpoly F r).natDegree - X : F[X]) = 0 := by
      rw [hc, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h0
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ (by norm_num))] at hrm
    exact zero_ne_one hrm
  have hN : r ^ (Nat.card F ^ (minpoly F r).natDegree - 1) = 1 := by
    have hpos : 0 < Nat.card F ^ (minpoly F r).natDegree := pow_pos (by omega) _
    have : r ^ (Nat.card F ^ (minpoly F r).natDegree - 1) * r = 1 * r := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hpos]
      exact hrQ
    exact mul_right_cancel₀ hr0 this
  have hord1 : orderOf r ∣ 5 ^ m := orderOf_dvd_of_pow_eq_one hrm
  have hord2 : orderOf r ∣ Nat.card F ^ (minpoly F r).natDegree - 1 :=
    orderOf_dvd_of_pow_eq_one hN
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hord1
  constructor
  · intro hd4
    have hn25 := ((not_dvd_pow_sub_one hQ h5 h25 hdpos).1 hd4)
    have hj1 : j ≤ 1 := by
      by_contra hcon
      apply hn25
      have : (5 : ℕ) ^ 2 ∣ orderOf r := by
        rw [hj]; exact pow_dvd_pow 5 (by omega)
      simpa using this.trans hord2
    have : orderOf r ∣ 5 := by
      rw [hj]
      exact (pow_dvd_pow 5 hj1).trans (by simp)
    exact orderOf_dvd_iff_pow_eq_one.1 this
  · intro hd5
    have hn125 := ((not_dvd_pow_sub_one hQ h5 h25 hdpos).2 hd5)
    have hj2 : j ≤ 2 := by
      by_contra hcon
      apply hn125
      have : (5 : ℕ) ^ 3 ∣ orderOf r := by
        rw [hj]; exact pow_dvd_pow 5 (by omega)
      simpa using this.trans hord2
    have : orderOf r ∣ 25 := by
      rw [hj]
      exact (pow_dvd_pow 5 hj2).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.1 this

theorem exists_algebraMap_eq_of_pow_five {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]
    (h5 : 5 ∣ Nat.card F - 1) {x : L} (hx : x ^ 5 = 1) : ∃ c : F, algebraMap F L c = x := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : 5 ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 5 hcard
  have hprim : IsPrimitiveRoot (ζ : F) 5 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  have hprim' : IsPrimitiveRoot (algebraMap F L (ζ : F)) 5 :=
    hprim.map_of_injective (algebraMap F L).injective
  obtain ⟨i, -, hi⟩ := hprim'.eq_pow_of_pow_eq_one hx
  exact ⟨(ζ : F) ^ i, by rw [map_pow]; exact hi⟩

theorem exists_scalar_pow_five {F : Type} [Field F] [Finite F] (h5 : 5 ∣ Nat.card F - 1)
    (h25 : ¬ 25 ∣ Nat.card F - 1) (g : Matrix (Fin 5) (Fin 5) F) {m : ℕ} (hg : g ^ 5 ^ m = 1) :
    ∃ c : F, g ^ 5 = c • (1 : Matrix (Fin 5) (Fin 5) F) := by
  classical
  have h5F : (5 : F) ≠ 0 := by
    intro h0
    haveI := Fintype.ofFinite F
    have hQ0 : ((Nat.card F : ℕ) : F) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero F
    obtain ⟨k, hk⟩ := h5
    have hQ1 : Nat.card F = 5 * k + 1 := by
      have := Nat.card_pos (α := F)
      omega
    rw [hQ1] at hQ0
    push_cast at hQ0
    rw [h0, zero_mul, zero_add] at hQ0
    exact one_ne_zero hQ0
  have hint : IsIntegral F g := Matrix.isIntegral g
  set μ := minpoly F g with hμ
  have hmon : μ.Monic := minpoly.monic hint
  have hμ0 : μ ≠ 0 := hmon.ne_zero
  have hdeg : μ.natDegree ≤ 5 := by
    have h := natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly g) (Matrix.charpoly_monic g).ne_zero
    simpa [Matrix.charpoly_natDegree_eq_dim] using h
  have hdvd : μ ∣ (X ^ 5 ^ m - 1 : F[X]) := minpoly.dvd F g (by simp [hg])
  have hsep : μ.Separable := by
    have h1 : ((5 ^ m : ℕ) : F) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ h5F
    have h2 := separable_X_pow_sub_C (F := F) (n := 5 ^ m) 1 h1 one_ne_zero
    rw [C_1] at h2
    exact h2.of_dvd hdvd
  let L := AlgebraicClosure F
  have hroot1 : ∀ r : L, aeval r μ = 0 → r ^ 5 ^ m = 1 := by
    intro r hr
    obtain ⟨c, hc⟩ := hdvd
    have h0 : aeval r (X ^ 5 ^ m - 1 : F[X]) = 0 := by rw [hc, map_mul, hr, zero_mul]
    simpa [sub_eq_zero] using h0
  have hrint : ∀ r : L, aeval r μ = 0 → IsIntegral F r := fun r hr =>
    ⟨μ, hmon, by rwa [← aeval_def]⟩
  by_cases hB : ∃ r : L, aeval r μ = 0 ∧ (minpoly F r).natDegree = 5
  · obtain ⟨r, hr, hr5⟩ := hB
    have hmin : μ = minpoly F r :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hrint r hr)) hmon (minpoly.dvd F r hr)
        (by rw [hr5]; exact hdeg)
    have h25r : r ^ 25 = 1 :=
      (pow_eq_one_of_isIntegral h5 h25 (hrint r hr) (hroot1 r hr)).2 hr5
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_pow_five (L := L) h5 (x := r ^ 5)
      (by rw [← pow_mul]; exact h25r)
    refine ⟨c, ?_⟩
    have hrc : aeval r (X ^ 5 - C c : F[X]) = 0 := by
      simp [hc]
    have hdc : μ ∣ (X ^ 5 - C c : F[X]) := hmin ▸ minpoly.dvd F r hrc
    obtain ⟨q, hq⟩ := hdc
    have h0 : aeval g (X ^ 5 - C c : F[X]) = 0 := by
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero, Algebra.algebraMap_eq_smul_one] using h0
  · push Not at hB
    have hall : ∀ r : L, aeval r μ = 0 → r ^ 5 = 1 := by
      intro r hr
      have hle : (minpoly F r).natDegree ≤ 5 :=
        (natDegree_le_of_dvd (minpoly.dvd F r hr) hμ0).trans hdeg
      have hne : (minpoly F r).natDegree ≠ 5 := hB r hr
      exact (pow_eq_one_of_isIntegral h5 h25 (hrint r hr) (hroot1 r hr)).1 (by omega)
    have hdvd5 : μ ∣ (X ^ 5 - 1 : F[X]) := by
      rw [← Polynomial.map_dvd_map' (algebraMap F L)]
      have hP0 : μ.map (algebraMap F L) ≠ 0 := (Polynomial.map_ne_zero_iff
        (algebraMap F L).injective).2 hμ0
      have hX0 : ((X ^ 5 - 1 : F[X]).map (algebraMap F L)) ≠ 0 := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, ← C_1]
        exact X_pow_sub_C_ne_zero (by norm_num) 1
      rw [IsAlgClosed.dvd_iff_roots_le_roots hP0 hX0,
        Multiset.le_iff_subset (nodup_roots (hsep.map (f := algebraMap F L)))]
      intro r hr
      have hr' : aeval r μ = 0 := (mem_aroots'.1 hr).2
      exact (mem_aroots').2 ⟨hX0, by simp [hall r hr', sub_eq_zero]⟩
    refine ⟨1, ?_⟩
    obtain ⟨q, hq⟩ := hdvd5
    have h0 : aeval g (X ^ 5 - 1 : F[X]) = 0 := by
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h0

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagAux
