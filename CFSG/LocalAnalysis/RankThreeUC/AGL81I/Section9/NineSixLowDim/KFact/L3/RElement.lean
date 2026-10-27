module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix Polynomial

private lemma exists_prime_dvd_cube_sub_one {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    ∃ r : ℕ, r.Prime ∧ Nat.Coprime r 6 ∧ r ∣ q ^ 3 - 1 ∧ Nat.Coprime r (q - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 1 := ⟨q / 3, by omega⟩
  have hk : 1 ≤ k := by
    rcases k with _ | k
    · exact absurd hq Nat.not_prime_one
    · omega
  have hm1 : 3 * k ^ 2 + 3 * k + 1 ≠ 1 := by
    have : 0 < 3 * k ^ 2 + 3 * k := by positivity
    omega
  set m := 3 * k ^ 2 + 3 * k + 1 with hm
  have hr := Nat.minFac_prime hm1
  have hrm := Nat.minFac_dvd m
  set r := m.minFac
  have h2 : ¬ 2 ∣ m := by
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
    have : m = 3 * (k * (k + 1)) + 1 := by rw [hm]; ring
    rw [this, hj]; omega
  have h3 : ¬ 3 ∣ m := by
    have : m = 3 * (k ^ 2 + k) + 1 := by rw [hm]; ring
    rw [this]; omega
  have hr2 : Nat.Coprime r 2 := (Nat.coprime_primes hr Nat.prime_two).mpr
    (by rintro h; exact h2 (h ▸ hrm))
  have hr3 : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).mpr
    (by rintro h; exact h3 (h ▸ hrm))
  have hrk : Nat.Coprime r k := by
    refine (Nat.Prime.coprime_iff_not_dvd hr).mpr fun hrk => hr.not_dvd_one ?_
    refine (Nat.dvd_add_right ?_).mp hrm
    exact (dvd_mul_of_dvd_right (dvd_pow hrk two_ne_zero) 3).add (dvd_mul_of_dvd_right hrk 3)
  refine ⟨r, hr, by simpa using hr2.mul_right hr3, ?_, ?_⟩
  · have : (3 * k + 1) ^ 3 = 3 * k * (3 * m) + 1 := by rw [hm]; ring
    rw [this, Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hrm 3) _
  · rw [show 3 * k + 1 - 1 = 3 * k by omega]
    exact hr3.mul_right hrk

private lemma eq_one_of_pow_eq_one {q : ℕ} [Fact q.Prime] {r : ℕ} (hr0 : r ≠ 0)
    (hr : Nat.Coprime r (q - 1)) {x : ZMod q} (hx : x ^ r = 1) : x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hr0] at hx
  have h := pow_gcd_eq_one.mpr ⟨hx, ZMod.pow_card_sub_one_eq_one hx0⟩
  rwa [hr, pow_one] at h

private lemma irreducible_cube_sub {q : ℕ} [Fact q.Prime] {μ : (ZMod q)ˣ}
    (hμ : ∀ ν : (ZMod q)ˣ, ν ^ 3 ≠ μ) : Irreducible (X ^ 3 - C (μ : ZMod q)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_sub_C]; decide
  · intro x hx
    have hx3 : x ^ 3 = μ := by simpa [sub_eq_zero] using hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx3; exact μ.ne_zero hx3.symm
    exact hμ (Units.mk0 x hx0) (Units.ext (by simp [hx3]))

private lemma cycMatrix_pow_three {F : Type} [Field F] (μ : F) :
    cycMatrix μ ^ 3 = algebraMap F (Matrix (Fin 3) (Fin 3) F) μ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMatrix, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.algebraMap_eq_diagonal]

private noncomputable def cycHom {F : Type} [Field F] (μ : F) :
    AdjoinRoot (X ^ 3 - C μ) →+* Matrix (Fin 3) (Fin 3) F :=
  Ideal.Quotient.lift _ (aeval (cycMatrix μ)).toRingHom fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [cycMatrix_pow_three]

private lemma cycHom_mk {F : Type} [Field F] (μ : F) (p : F[X]) :
    cycHom μ (AdjoinRoot.mk _ p) = aeval (cycMatrix μ) p := rfl

private lemma cycHom_root {F : Type} [Field F] (μ : F) :
    cycHom μ (AdjoinRoot.root _) = cycMatrix μ := by
  rw [← AdjoinRoot.mk_X, cycHom_mk, aeval_X]

private lemma cycHom_of {F : Type} [Field F] (μ : F) (a : F) :
    cycHom μ (AdjoinRoot.of _ a) = algebraMap F _ a := by
  rw [← AdjoinRoot.mk_C, cycHom_mk, aeval_C]

private lemma natCard_adjoinRoot {q : ℕ} [Fact q.Prime] (μ : ZMod q) :
    Nat.card (AdjoinRoot (X ^ 3 - C μ)) = q ^ 3 := by
  have hf : (X ^ 3 - C μ : (ZMod q)[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) μ
  rw [Nat.card_congr (AdjoinRoot.powerBasis hf).basis.equivFun.toEquiv, Nat.card_fun,
    Nat.card_zmod, Nat.card_fin]
  simp [AdjoinRoot.powerBasis]

private lemma cycMat_not_mem_center {q : ℕ} [Fact q.Prime] {μ : (ZMod q)ˣ} (hμ : μ ≠ 1) :
    cycMat μ ∉ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  intro h
  have := congrArg (fun g : GL (Fin 3) (ZMod q) => (g : Matrix (Fin 3) (Fin 3) (ZMod q)) 1 2)
    (Subgroup.mem_center_iff.mp h (cycMat 1))
  change (cycMatrix (1 : ZMod q) * cycMatrix (μ : ZMod q)) 1 2 =
    (cycMatrix (μ : ZMod q) * cycMatrix (1 : ZMod q)) 1 2 at this
  simp [cycMatrix, Matrix.mul_apply, Fin.sum_univ_three] at this
  exact hμ this

private lemma cycHom_noEigen {q : ℕ} [Fact q.Prime] {μ : (ZMod q)ˣ}
    [Fact (Irreducible (X ^ 3 - C (μ : ZMod q)))] {r : ℕ} (hr : r.Prime)
    (hrq : Nat.Coprime r (q - 1)) (u : (AdjoinRoot (X ^ 3 - C (μ : ZMod q)))ˣ) (hu : orderOf u = r)
    (v : Fin 3 → ZMod q) (c : ZMod q) (hv : cycHom (μ : ZMod q) u *ᵥ v = c • v) : v = 0 := by
  set f : (ZMod q)[X] := X ^ 3 - C (μ : ZMod q)
  set φ := cycHom (μ : ZMod q)
  have hur : (u : AdjoinRoot f) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  by_cases hc : (u : AdjoinRoot f) = AdjoinRoot.of f c
  · exfalso
    have hc1 : c ^ r = 1 := (AdjoinRoot.of f).injective (by rw [map_pow, ← hc, hur, map_one])
    have hu1 : u = 1 := Units.ext (by rw [hc, eq_one_of_pow_eq_one hr.ne_zero hrq hc1]; simp)
    rw [hu1, orderOf_one] at hu
    exact hr.one_lt.ne hu
  · have hw : (u : AdjoinRoot f) - AdjoinRoot.of f c ≠ 0 := sub_ne_zero.mpr hc
    set w := (u : AdjoinRoot f) - AdjoinRoot.of f c with hw'
    have h1 : φ w⁻¹ * φ w = 1 := by rw [← map_mul, inv_mul_cancel₀ hw, map_one]
    have h2 : φ w *ᵥ v = 0 := by
      rw [hw', map_sub, cycHom_of, Algebra.algebraMap_eq_smul_one]
      erw [Matrix.sub_mulVec]
      rw [hv, Matrix.smul_mulVec, one_mulVec, sub_self]
    calc v = (φ w⁻¹ * φ w) *ᵥ v := by rw [h1, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, h2, mulVec_zero]

theorem exists_noEigen_mem_fixSetThree {q : ℕ} [Fact q.Prime] (hq3 : q % 3 = 1)
    {A : Subgroup (GL (Fin 3) (ZMod q))} {μ : (ZMod q)ˣ} (hμ : ∀ ν : (ZMod q)ˣ, ν ^ 3 ≠ μ)
    (hb : cycMat μ ∈ A) :
    ∃ y ∈ fixSetThree 3 A, ∃ r : ℕ, r.Prime ∧ Nat.Coprime r 6 ∧ orderOf y = r ∧
      ∀ (v : Fin 3 → ZMod q) (c : ZMod q),
        (y : Matrix (Fin 3) (Fin 3) (ZMod q)) *ᵥ v = c • v → v = 0 := by
  have hqp : q.Prime := Fact.out
  set f : (ZMod q)[X] := X ^ 3 - C (μ : ZMod q)
  have : Fact (Irreducible f) := ⟨irreducible_cube_sub hμ⟩
  obtain ⟨r, hr, hr6, hrd, hrq⟩ := exists_prime_dvd_cube_sub_one hqp hq3
  have : Fact r.Prime := ⟨hr⟩
  have hK : Nat.card (AdjoinRoot f) = q ^ 3 := natCard_adjoinRoot _
  have : Finite (AdjoinRoot f) :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hqp.ne_zero)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (AdjoinRoot f)ˣ) r
    (by rw [Nat.card_units, hK]; exact hrd)
  have hur : (u : AdjoinRoot f) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  set φ := cycHom (μ : ZMod q)
  let y : GL (Fin 3) (ZMod q) := Units.map φ.toMonoidHom u
  have hy : (y : Matrix (Fin 3) (Fin 3) (ZMod q)) = φ u := rfl
  have hyo : orderOf y = r := by
    rw [← hu]; exact orderOf_injective _ (Units.map_injective φ.injective) u
  refine ⟨y, ⟨?_, ?_, cycMat μ, hb, cycMat_not_mem_center fun h => hμ 1 (by simp [h]), ?_⟩,
    r, hr, hr6, hyo, ?_⟩
  · apply eq_one_of_pow_eq_one hr.ne_zero hrq
    rw [hy, ← Matrix.det_pow, ← map_pow, hur, map_one, det_one]
  · rw [hyo]
    intro h3
    have := Nat.dvd_gcd h3 (by norm_num : 3 ∣ 6)
    rw [Nat.Coprime.gcd_eq_one hr6] at this
    norm_num at this
  · ext1
    change cycMatrix (μ : ZMod q) * φ u = φ u * cycMatrix (μ : ZMod q)
    rw [← cycHom_root, ← map_mul, ← map_mul, mul_comm]
  · exact fun v c hv => cycHom_noEigen hr hrq u hu v c hv

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
