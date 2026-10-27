module

public import CFSG.HardMathSupport.U4FF.ClassUminusA

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

abbrev G4 (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Type :=
  ↥(SU (unitaryInvolution K 2 n) 4)

@[expose] def Fq (K : Type) [Field K] [CharP K 2] (n : ℕ) : Subfield K where
  carrier := {c | c ^ 2 ^ n = c}
  zero_mem' := by
    show (0 : K) ^ 2 ^ n = 0
    exact zero_pow (pow_ne_zero n two_ne_zero)
  one_mem' := one_pow _
  add_mem' {a b} ha hb := by
    show (a + b) ^ 2 ^ n = a + b
    rw [add_pow_char_pow, (ha : a ^ 2 ^ n = a), (hb : b ^ 2 ^ n = b)]
  neg_mem' {a} ha := by
    show (-a) ^ 2 ^ n = -a
    rw [CharTwo.neg_eq]
    exact ha
  mul_mem' {a b} ha hb := by
    show (a * b) ^ 2 ^ n = a * b
    rw [mul_pow, (ha : a ^ 2 ^ n = a), (hb : b ^ 2 ^ n = b)]
  inv_mem' {a} ha := by
    show a⁻¹ ^ 2 ^ n = a⁻¹
    rw [inv_pow, (ha : a ^ 2 ^ n = a)]

theorem mem_Fq {K : Type} [Field K] [CharP K 2] {n : ℕ} {c : K} : c ∈ Fq K n ↔ c ^ 2 ^ n = c :=
  Iff.rfl

abbrev Fs (K : Type) [Field K] [CharP K 2] (n : ℕ) : Fin 2 → Type := ![K, ↥(Fq K n)]

instance instFieldFs (K : Type) [Field K] [CharP K 2] (n : ℕ) : ∀ s, Field (Fs K n s)
  | 0 => inferInstanceAs (Field K)
  | 1 => inferInstanceAs (Field ↥(Fq K n))

instance instFiniteFs (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    ∀ s, Finite (Fs K n s)
  | 0 => inferInstanceAs (Finite K)
  | 1 => inferInstanceAs (Finite ↥(Fq K n))

namespace Datum

theorem rev0 : Fin.rev (0 : Fin 4) = 3 := rfl
theorem rev1 : Fin.rev (1 : Fin 4) = 2 := rfl
theorem rev2 : Fin.rev (2 : Fin 4) = 1 := rfl
theorem rev3 : Fin.rev (3 : Fin 4) = 0 := rfl

end Datum

section Basic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def gm (g : G4 K n) : Matrix (Fin 4) (Fin 4) K :=
  ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

theorem gm_mul (g h : G4 K n) : gm (g * h) = gm g * gm h := rfl

theorem gm_one : gm (1 : G4 K n) = 1 := rfl

theorem gm_inv_mul (g : G4 K n) : gm g⁻¹ * gm g = 1 := Units.inv_mul (g : GL (Fin 4) K)

theorem gm_mul_inv (g : G4 K n) : gm g * gm g⁻¹ = 1 := Units.mul_inv (g : GL (Fin 4) K)

theorem gm_injective : Function.Injective (gm : G4 K n → Matrix (Fin 4) (Fin 4) K) :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem gm_det (g : G4 K n) : (gm g).det = 1 := (mem_SU.mp g.2).1

theorem gm_conj (g : G4 K n) :
    conjTr (unitaryInvolution K 2 n) (gm g) * antidiag 4 * gm g = antidiag 4 :=
  (mem_SU.mp g.2).2

theorem eq_of_gm_eq {g h : G4 K n} (e : gm g = gm h) : g = h := gm_injective e

theorem gm_inv_eq_of_sq {g : G4 K n} (h : gm g * gm g = 1) : gm g⁻¹ = gm g := by
  calc gm g⁻¹ = gm g⁻¹ * (gm g * gm g) := by rw [h, Matrix.mul_one]
    _ = (gm g⁻¹ * gm g) * gm g := by rw [Matrix.mul_assoc]
    _ = gm g := by rw [gm_inv_mul, Matrix.one_mul]

end Basic

section Diagonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def diagGL (d : Fin 4 → K) (hd : ∀ i, d i ≠ 0) : GL (Fin 4) K :=
  ⟨diagonal d, diagonal fun i => (d i)⁻¹,
    by
      rw [diagonal_mul_diagonal]
      have : (fun i => d i * (d i)⁻¹) = fun _ => (1 : K) := by
        funext i
        exact mul_inv_cancel₀ (hd i)
      rw [this, diagonal_one],
    by
      rw [diagonal_mul_diagonal]
      have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : K) := by
        funext i
        exact inv_mul_cancel₀ (hd i)
      rw [this, diagonal_one]⟩

theorem conjTr_diagonal (d : Fin 4 → K) :
    conjTr (unitaryInvolution K 2 n) (diagonal d) = diagonal fun i => d i ^ 2 ^ n := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [conjTr, unitaryInvolution_apply, iterateFrobenius_def]
  · simp [conjTr, diagonal_apply_ne _ hij, diagonal_apply_ne _ (Ne.symm hij)]

theorem diagonal_mul_antidiag_mul_diagonal (a b : Fin 4 → K) (i j : Fin 4) :
    (diagonal a * antidiag 4 * diagonal b : Matrix (Fin 4) (Fin 4) K) i j =
      if j = Fin.rev i then a i * b j else 0 := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [antidiag, of_apply]
  by_cases hj : j = Fin.rev i <;> simp [hj]

theorem diagGL_mem_SU (d : Fin 4 → K) (hd : ∀ i, d i ≠ 0)
    (h1 : ∀ i, d i ^ 2 ^ n * d (Fin.rev i) = 1) (h2 : d 0 * d 1 * d 2 * d 3 = 1) :
    diagGL d hd ∈ SU (unitaryInvolution K 2 n) 4 := by
  refine mem_SU.mpr ⟨?_, ?_⟩
  · show (diagonal d).det = 1
    rw [det_diagonal, Fin.prod_univ_four]
    exact h2
  · show conjTr (unitaryInvolution K 2 n) (diagonal d) * antidiag 4 * diagonal d = antidiag 4
    rw [conjTr_diagonal]
    ext i j
    rw [diagonal_mul_antidiag_mul_diagonal]
    by_cases hj : j = Fin.rev i
    · subst hj
      simpa [antidiag] using h1 i
    · simp [hj, antidiag]

@[expose] def diagG (d : Fin 4 → K) (hd : ∀ i, d i ≠ 0)
    (h1 : ∀ i, d i ^ 2 ^ n * d (Fin.rev i) = 1) (h2 : d 0 * d 1 * d 2 * d 3 = 1) : G4 K n :=
  ⟨diagGL d hd, diagGL_mem_SU d hd h1 h2⟩

end Diagonal

section Tori

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def tor0Vec (n : ℕ) (u : K) : Fin 4 → K := ![u, u⁻¹, u ^ 2 ^ n, (u ^ 2 ^ n)⁻¹]

@[expose] def tor1Vec (v : K) : Fin 4 → K := ![1, v, v⁻¹, 1]

theorem tor0Vec_ne (n : ℕ) {u : K} (hu : u ≠ 0) : ∀ i, tor0Vec n u i ≠ 0 := by
  intro i
  fin_cases i <;> simp [tor0Vec, hu]

theorem tor1Vec_ne {v : K} (hv : v ≠ 0) : ∀ i, tor1Vec v i ≠ 0 := by
  intro i
  fin_cases i <;> simp [tor1Vec, hv]

variable (hK : Nat.card K = (2 ^ n) ^ 2)

include hK in
theorem tor0Vec_h1 {u : K} (hu : u ≠ 0) :
    ∀ i, tor0Vec n u i ^ 2 ^ n * tor0Vec n u (Fin.rev i) = 1 := by
  intro i
  have hq : ∀ x : K, (x ^ 2 ^ n) ^ 2 ^ n = x := pow_pow_of_card hK
  fin_cases i <;>
    simp [tor0Vec, Datum.rev0, Datum.rev1, Datum.rev2, Datum.rev3, hq, inv_pow, hu]

theorem tor0Vec_h2 {u : K} (hu : u ≠ 0) : tor0Vec n u 0 * tor0Vec n u 1 * tor0Vec n u 2 *
    tor0Vec n u 3 = 1 := by
  simp [tor0Vec, hu]

include hK in
theorem tor1Vec_h1 {v : K} (hv : v ≠ 0) (hvq : v ^ 2 ^ n = v) :
    ∀ i, tor1Vec v i ^ 2 ^ n * tor1Vec v (Fin.rev i) = 1 := by
  intro i
  fin_cases i <;>
    simp [tor1Vec, Datum.rev0, Datum.rev1, Datum.rev2, Datum.rev3, inv_pow, hvq, hv]

theorem tor1Vec_h2 {v : K} (hv : v ≠ 0) : tor1Vec v 0 * tor1Vec v 1 * tor1Vec v 2 *
    tor1Vec v 3 = 1 := by
  simp [tor1Vec, hv]

@[expose] noncomputable def hTor0 (hK : Nat.card K = (2 ^ n) ^ 2) (u : Kˣ) : G4 K n :=
  diagG (tor0Vec n (u : K)) (tor0Vec_ne n u.ne_zero) (tor0Vec_h1 hK u.ne_zero)
    (tor0Vec_h2 u.ne_zero)

theorem fq_ne_zero {n : ℕ} (v : (Fq K n)ˣ) : ((v : Fq K n) : K) ≠ 0 := fun h =>
  v.ne_zero (Subtype.ext h)

@[expose] noncomputable def hTor1 (hK : Nat.card K = (2 ^ n) ^ 2) (v : (Fq K n)ˣ) : G4 K n :=
  diagG (tor1Vec ((v : Fq K n) : K)) (tor1Vec_ne (fq_ne_zero v))
    (tor1Vec_h1 hK (fq_ne_zero v) v.1.2) (tor1Vec_h2 (fq_ne_zero v))

theorem gm_hTor0 (u : Kˣ) : gm (hTor0 hK u) = diagonal (tor0Vec n (u : K)) := rfl

theorem gm_hTor1 (v : (Fq K n)ˣ) : gm (hTor1 hK v) = diagonal (tor1Vec ((v : Fq K n) : K)) := rfl

end Tori

section HdSection

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem diag_ne_zero {g : G4 K n} (hg : ∀ i j, i ≠ j → gm g i j = 0) (j : Fin 4) :
    gm g j j ≠ 0 := by
  intro h0
  have h4 : (gm g * gm g⁻¹) j j = 1 := by rw [gm_mul_inv]; exact Matrix.one_apply_eq j
  rw [Matrix.mul_apply, Finset.sum_eq_single j] at h4
  · rw [h0, zero_mul] at h4
    exact zero_ne_one h4
  · intro k _ hkj
    rw [hg j k (Ne.symm hkj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

@[expose] def Hd (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Subgroup (G4 K n) where
  carrier := {g | ∀ i j, i ≠ j → gm g i j = 0}
  one_mem' := fun i j hij => by
    show (1 : Matrix (Fin 4) (Fin 4) K) i j = 0
    exact Matrix.one_apply_ne hij
  mul_mem' {g h} hg hh := by
    intro i j hij
    rw [gm_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k = i
    · subst hki
      rw [(hh : ∀ i j, i ≠ j → gm h i j = 0) k j hij, mul_zero]
    · rw [(hg : ∀ i j, i ≠ j → gm g i j = 0) i k (Ne.symm hki), zero_mul]
  inv_mem' {g} hg := by
    intro i j hij
    have hg' : ∀ i j, i ≠ j → gm g i j = 0 := hg
    have h1 : (gm g⁻¹ * gm g) i j = 0 := by rw [gm_inv_mul]; exact Matrix.one_apply_ne hij
    have h2 : (gm g⁻¹ * gm g) i j = gm g⁻¹ i j * gm g j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro k _ hkj
        rw [hg' k j hkj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_right (diag_ne_zero hg' j)

theorem mem_Hd {g : G4 K n} :
    g ∈ Hd K n ↔
      ∀ i j, i ≠ j → ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0 :=
  Iff.rfl

theorem gm_eq_diagonal {g : G4 K n} (hg : g ∈ Hd K n) :
    gm g = diagonal fun i => gm g i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · have h0 := mem_Hd.mp hg i j hij
    rw [diagonal_apply_ne _ hij]
    exact h0

theorem exists_diag {g : G4 K n} (hg : g ∈ Hd K n) :
    ∃ d : Fin 4 → K, gm g = diagonal d ∧ ∀ i, gm g i i = d i := by
  refine ⟨fun i => gm g i i, gm_eq_diagonal hg, fun i => rfl⟩

theorem Hd_diag_ne {g : G4 K n} (hg : g ∈ Hd K n) (i : Fin 4) : gm g i i ≠ 0 :=
  diag_ne_zero (mem_Hd.mp hg) i

theorem gm_inv_of_mem_Hd {g : G4 K n} (hg : g ∈ Hd K n) :
    gm g⁻¹ = diagonal fun i => (gm g i i)⁻¹ := by
  obtain ⟨d, hd, hdi⟩ := exists_diag hg
  have hne : ∀ i, d i ≠ 0 := fun i => by rw [← hdi]; exact Hd_diag_ne hg i
  have h1 : (diagonal fun i => (d i)⁻¹ : Matrix (Fin 4) (Fin 4) K) * gm g = 1 := by
    rw [hd, diagonal_mul_diagonal]
    have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : K) := by
      funext i
      exact inv_mul_cancel₀ (hne i)
    rw [this, diagonal_one]
  have h2 : gm g⁻¹ = diagonal fun i => (d i)⁻¹ := by
    calc gm g⁻¹ = ((diagonal fun i => (d i)⁻¹ : Matrix (Fin 4) (Fin 4) K) * gm g) * gm g⁻¹ := by
          rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, gm_mul_inv, Matrix.mul_one]
  rw [h2]
  simp only [hdi]

theorem gm_conj_diag {h : G4 K n} (hh : h ∈ Hd K n) (g : G4 K n) (i j : Fin 4) :
    gm (h * g * h⁻¹) i j = gm h i i * gm g i j * (gm h j j)⁻¹ := by
  obtain ⟨d, hd, hdi⟩ := exists_diag hh
  rw [gm_mul, gm_mul, gm_inv_of_mem_Hd hh]
  simp only [hdi]
  rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem Hd_rel {g : G4 K n} (hg : g ∈ Hd K n) (i : Fin 4) :
    gm g i i ^ 2 ^ n * gm g (Fin.rev i) (Fin.rev i) = 1 := by
  obtain ⟨d, hd, hdi⟩ := exists_diag hg
  have h := congrFun (congrFun (gm_conj g) i) (Fin.rev i)
  rw [hd, conjTr_diagonal, diagonal_mul_antidiag_mul_diagonal] at h
  simp only [antidiag, of_apply] at h
  simpa [hdi] using h

theorem Hd_det {g : G4 K n} (hg : g ∈ Hd K n) :
    gm g 0 0 * gm g 1 1 * gm g 2 2 * gm g 3 3 = 1 := by
  obtain ⟨d, hd, hdi⟩ := exists_diag hg
  have h := gm_det g
  rw [hd, det_diagonal, Fin.prod_univ_four] at h
  simpa [hdi] using h

theorem hTor0_mem (hK : Nat.card K = (2 ^ n) ^ 2) (u : Kˣ) : hTor0 hK u ∈ Hd K n := by
  intro i j hij
  show (diagonal (tor0Vec n (u : K))) i j = 0
  exact diagonal_apply_ne _ hij

theorem hTor1_mem (hK : Nat.card K = (2 ^ n) ^ 2) (v : (Fq K n)ˣ) : hTor1 hK v ∈ Hd K n := by
  intro i j hij
  show (diagonal (tor1Vec ((v : Fq K n) : K))) i j = 0
  exact diagonal_apply_ne _ hij

theorem Hd_eq_hTor (hK : Nat.card K = (2 ^ n) ^ 2) {g : G4 K n} (hg : g ∈ Hd K n) :
    ∃ (u : Kˣ) (v : (Fq K n)ˣ), g = hTor0 hK u * hTor1 hK v := by
  obtain ⟨d, hd, hdi⟩ := exists_diag hg
  have hd0 : ∀ i, d i ≠ 0 := fun i => by rw [← hdi]; exact Hd_diag_ne hg i
  have r0 : d 0 ^ 2 ^ n * d 3 = 1 := by simpa [hdi, Datum.rev0] using Hd_rel hg 0
  have r1 : d 1 ^ 2 ^ n * d 2 = 1 := by simpa [hdi, Datum.rev1] using Hd_rel hg 1
  have hdet : d 0 * d 1 * d 2 * d 3 = 1 := by simpa [hdi] using Hd_det hg
  have hv : (d 0 * d 1) ^ 2 ^ n = d 0 * d 1 := by
    rw [mul_pow]
    refine mul_right_cancel₀ (mul_ne_zero (hd0 2) (hd0 3)) ?_
    linear_combination (d 1 ^ 2 ^ n * d 2) * r0 + r1 - hdet
  have hv0 : d 0 * d 1 ≠ 0 := mul_ne_zero (hd0 0) (hd0 1)
  refine ⟨Units.mk0 (d 0) (hd0 0), Units.mk0 (⟨d 0 * d 1, hv⟩ : Fq K n) (fun h => hv0 ?_), ?_⟩
  · exact congrArg Subtype.val h
  · apply eq_of_gm_eq
    rw [gm_mul, gm_hTor0 hK, gm_hTor1 hK, diagonal_mul_diagonal, hd]
    congr 1
    funext i
    have e0 : d 0 ≠ 0 := hd0 0
    have e1 : d 1 ≠ 0 := hd0 1
    have e2 : d 2 ≠ 0 := hd0 2
    have e3 : d 3 ≠ 0 := hd0 3
    have eq0 : (d 0) ^ 2 ^ n ≠ 0 := pow_ne_zero _ e0
    have eq1 : (d 1) ^ 2 ^ n ≠ 0 := pow_ne_zero _ e1
    fin_cases i
    · simp [tor0Vec, tor1Vec]
    · simp only [Fin.mk_one, tor0Vec, tor1Vec, Units.val_mk0]
      simp
      field_simp
    · simp only [Fin.reduceFinMk, tor0Vec, tor1Vec, Units.val_mk0]
      simp
      field_simp
      refine mul_right_cancel₀ e3 ?_
      linear_combination hdet - r0
    · simp only [Fin.reduceFinMk, tor0Vec, tor1Vec, Units.val_mk0]
      simp
      field_simp
      linear_combination r0

end HdSection

section ToriHom

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)

theorem hTor0_mul (u u' : Kˣ) : hTor0 hK (u * u') = hTor0 hK u * hTor0 hK u' := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_hTor0 hK, gm_hTor0 hK, gm_hTor0 hK, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [tor0Vec, mul_pow, mul_inv] <;> ring

theorem hTor0_one : hTor0 hK (1 : Kˣ) = 1 := by
  apply eq_of_gm_eq
  rw [gm_hTor0 hK, gm_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [tor0Vec]

theorem hTor1_mul (v v' : (Fq K n)ˣ) : hTor1 hK (v * v') = hTor1 hK v * hTor1 hK v' := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_hTor1 hK, gm_hTor1 hK, gm_hTor1 hK, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [tor1Vec, mul_inv] <;> ring

theorem hTor1_one : hTor1 hK (1 : (Fq K n)ˣ) = 1 := by
  apply eq_of_gm_eq
  rw [gm_hTor1 hK, gm_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [tor1Vec]

end ToriHom

section JElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem gm_jSU : gm (jSU K n) = antidiag 4 := rfl

theorem jSU_mul_self : jSU K n * jSU K n = 1 :=
  eq_of_gm_eq (by rw [gm_mul, gm_jSU, gm_one]; exact J_mul_J)

theorem jSU_inv : (jSU K n)⁻¹ = jSU K n := inv_eq_of_mul_eq_one_right jSU_mul_self

theorem gm_jconj (g : G4 K n) (i j : Fin 4) :
    gm (jSU K n * g * jSU K n) i j = gm g (Fin.rev i) (Fin.rev j) := by
  rw [gm_mul, gm_mul, gm_jSU]
  exact J_mul_mul_J_apply _ i j

theorem jconj_mem_Hd {h : G4 K n} (hh : h ∈ Hd K n) : jSU K n * h * jSU K n ∈ Hd K n := by
  intro i j hij
  rw [gm_jconj]
  exact mem_Hd.mp hh _ _ (fun e => hij (Fin.rev_injective e))

end JElement

end CFSG.HardMathSupport.U4FF
