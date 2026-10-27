module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix

variable {F : Type*} [Field F]

@[expose] def antidiag (n : ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if j = Fin.rev i then 1 else 0

variable (σ : F ≃+* F)

@[expose] def conjTr {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (A.map σ)ᵀ

theorem conjTr_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) F) :
    conjTr σ (A * B) = conjTr σ B * conjTr σ A := by
  simp only [conjTr, Matrix.map_mul, transpose_mul]

theorem conjTr_one {n : ℕ} : conjTr σ (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  simp [conjTr]

@[expose] def SU (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) F).det = 1 ∧
    conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F) =
      antidiag n}
  mul_mem' {A B} hA hB := by
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], ?_⟩
    have e : conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
        antidiag n * ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [Units.val_mul, e, hA.2, hB.2]
  one_mem' := ⟨by simp, by simp [conjTr_one]⟩
  inv_mem' {A} hA := by
    have hAB : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.det hAB
      rw [det_mul, det_one, hA.1, one_mul] at this
      exact this
    · have key : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix _ _ F)) *
            ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) =
          conjTr σ ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) * antidiag n *
            ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) := by
        rw [conjTr_mul]
        simp only [Matrix.mul_assoc]
      rw [hA.2, hAB, conjTr_one, Matrix.one_mul, Matrix.mul_one] at key
      exact key

variable {σ}

theorem mem_SU {n : ℕ} {A : GL (Fin n) F} :
    A ∈ SU σ n ↔ (A : Matrix (Fin n) (Fin n) F).det = 1 ∧
      conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F) =
        antidiag n :=
  Iff.rfl

variable (σ)

theorem antidiag_mul_single {n : ℕ} (i j : Fin n) (c : F) :
    antidiag n * single i j c = single (Fin.rev i) j c := by
  ext a b
  simp only [antidiag, mul_apply, of_apply, single_apply]
  rw [Finset.sum_eq_single i]
  · by_cases ha : a = Fin.rev i
    · subst ha; simp
    · have : ¬ Fin.rev i = a := fun h => ha h.symm
      have h2 : i ≠ Fin.rev a := fun h => ha (by rw [h, Fin.rev_rev])
      simp [this, h2]
  · intro k _ hki
    simp [Ne.symm hki]
  · simp

theorem single_mul_antidiag {n : ℕ} (i j : Fin n) (c : F) :
    single i j c * antidiag n = single i (Fin.rev j) c := by
  ext a b
  simp only [antidiag, mul_apply, of_apply, single_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hb : b = Fin.rev j
    · subst hb; simp
    · have : ¬ Fin.rev j = b := fun h => hb h.symm
      simp [hb, this]
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

theorem conjTr_single {n : ℕ} (i j : Fin n) (c : F) :
    conjTr σ (single i j c) = single j i (σ c) := by
  ext a b
  simp only [conjTr, transpose_apply, map_apply, single_apply]
  by_cases h : j = a ∧ i = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have h' : ¬ (i = b ∧ j = a) := fun h'' => h ⟨h''.2, h''.1⟩
    simp [h, h']

theorem conjTr_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) F) :
    conjTr σ (A + B) = conjTr σ A + conjTr σ B := by
  ext a b; simp [conjTr]

theorem conjTr_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) F) :
    conjTr σ (A - B) = conjTr σ A - conjTr σ B := by
  ext a b; simp [conjTr]

@[expose] def rootMatrix {n : ℕ} (i j : Fin n) (c : F) : Matrix (Fin n) (Fin n) F :=
  1 + single i j c - single (Fin.rev j) (Fin.rev i) (σ c)

@[expose] def longRootMatrix {n : ℕ} (i : Fin n) (c : F) : Matrix (Fin n) (Fin n) F :=
  1 + single i (Fin.rev i) c

@[expose] def heisenbergMatrix {n : ℕ} (i k : Fin n) (a b : F) : Matrix (Fin n) (Fin n) F :=
  1 + single i k a - single k (Fin.rev i) (σ a) + single i (Fin.rev i) b

variable (hσ : ∀ c, σ (σ c) = c)
include hσ

theorem conjTr_rootMatrix {n : ℕ} (i j : Fin n) (c : F) :
    conjTr σ (rootMatrix σ i j c) = 1 + single j i (σ c) - single (Fin.rev i) (Fin.rev j) c := by
  rw [rootMatrix, conjTr_sub, conjTr_add, conjTr_one, conjTr_single, conjTr_single, hσ]

theorem rootMatrix_isometry {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (c : F) :
    conjTr σ (rootMatrix σ i j c) * antidiag n * rootMatrix σ i j c = antidiag n := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  have h2 : Fin.rev i ≠ Fin.rev j := fun h => hij (Fin.rev_injective h)
  have h3 : j ≠ i := fun h => hij h.symm
  rw [conjTr_rootMatrix σ hσ i j c, rootMatrix]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, antidiag_mul_single, single_mul_antidiag, Fin.rev_rev,
    single_mul_single_of_ne _ _ _ _ h1, single_mul_single_of_ne _ _ _ _ h2,
    single_mul_single_of_ne _ _ _ _ h3, single_mul_single_of_ne _ _ _ _ hj]
  abel

omit hσ in
theorem conjTr_longRootMatrix {n : ℕ} (i : Fin n) (c : F) :
    conjTr σ (longRootMatrix i c) = 1 + single (Fin.rev i) i (σ c) := by
  rw [longRootMatrix, conjTr_add, conjTr_one, conjTr_single]

omit hσ in
theorem longRootMatrix_isometry {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) {c : F}
    (hc : c + σ c = 0) :
    conjTr σ (longRootMatrix i c) * antidiag n * longRootMatrix i c = antidiag n := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  rw [conjTr_longRootMatrix σ, longRootMatrix]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    antidiag_mul_single, single_mul_antidiag, single_mul_single_of_ne _ _ _ _ h1]
  calc _ = antidiag n + (single (Fin.rev i) (Fin.rev i) (σ c) +
        single (Fin.rev i) (Fin.rev i) c) := by abel
    _ = antidiag n := by
      rw [← Matrix.single_add, add_comm (σ c), hc, Matrix.single_zero, add_zero]

theorem conjTr_heisenbergMatrix {n : ℕ} (i k : Fin n) (a b : F) :
    conjTr σ (heisenbergMatrix σ i k a b) =
      1 + single k i (σ a) - single (Fin.rev i) k a + single (Fin.rev i) i (σ b) := by
  rw [heisenbergMatrix, conjTr_add, conjTr_sub, conjTr_add, conjTr_one, conjTr_single,
    conjTr_single, conjTr_single, hσ]

theorem heisenbergMatrix_isometry {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) {a b : F} (hab : b + σ b + σ a * a = 0) :
    conjTr σ (heisenbergMatrix σ i k a b) * antidiag n * heisenbergMatrix σ i k a b =
      antidiag n := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  have h2 : k ≠ i := fun h => hik h.symm
  have h3 : Fin.rev i ≠ k := fun h => hik (by rw [← Fin.rev_rev i, h, hk])
  rw [conjTr_heisenbergMatrix σ hσ, heisenbergMatrix]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, antidiag_mul_single, single_mul_antidiag, hk,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ h1,
    single_mul_single_of_ne _ _ _ _ h2, single_mul_single_of_ne _ _ _ _ h3]
  have hz : single (Fin.rev i) (Fin.rev i) (σ b) + single (Fin.rev i) (Fin.rev i) (a * σ a) +
      single (Fin.rev i) (Fin.rev i) b = (0 : Matrix (Fin n) (Fin n) F) := by
    rw [← Matrix.single_add, ← Matrix.single_add]
    have : σ b + a * σ a + b = 0 := by
      calc σ b + a * σ a + b = b + σ b + σ a * a := by ring
        _ = 0 := hab
    rw [this, Matrix.single_zero]
  calc _ = antidiag n + (single (Fin.rev i) (Fin.rev i) (σ b) +
        single (Fin.rev i) (Fin.rev i) (a * σ a) + single (Fin.rev i) (Fin.rev i) b) := by abel
    _ = antidiag n := by rw [hz, add_zero]

omit hσ

theorem rootMatrix_eq_mul {n : ℕ} {i j : Fin n} (hj : j ≠ Fin.rev j) (c : F) :
    rootMatrix σ i j c =
      transvection i j c * transvection (Fin.rev j) (Fin.rev i) (-σ c) := by
  rw [rootMatrix, transvection, transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, single_mul_single_of_ne _ _ _ _ hj,
    add_zero, ← single_neg]
  abel

theorem det_rootMatrix {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hj : j ≠ Fin.rev j) (c : F) :
    (rootMatrix σ i j c).det = 1 := by
  have h' : Fin.rev j ≠ Fin.rev i := fun h => hij (Fin.rev_injective h).symm
  rw [rootMatrix_eq_mul σ hj, det_mul, det_transvection_of_ne _ _ hij,
    det_transvection_of_ne _ _ h', one_mul]

theorem det_longRootMatrix {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) (c : F) :
    (longRootMatrix i c).det = 1 := by
  rw [longRootMatrix, ← transvection, det_transvection_of_ne _ _ hi]

theorem heisenbergMatrix_eq_mul {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (a b : F) :
    heisenbergMatrix σ i k a b = transvection i k a * transvection k (Fin.rev i) (-σ a) *
      transvection i (Fin.rev i) (b + a * σ a) := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  have h2 : k ≠ i := fun h => hik h.symm
  rw [heisenbergMatrix, transvection, transvection, transvection]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ h1,
    single_mul_single_of_ne _ _ _ _ h2, add_zero]
  rw [mul_neg, ← single_neg, ← single_neg]
  have : single i (Fin.rev i) (b + a * σ a) = single i (Fin.rev i) b +
      single i (Fin.rev i) (a * σ a) := Matrix.single_add _ _ _ _
  rw [this]
  abel

theorem det_heisenbergMatrix {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) :
    (heisenbergMatrix σ i k a b).det = 1 := by
  have h3 : k ≠ Fin.rev i := fun h => hik (by rw [← Fin.rev_rev i, ← h, hk])
  rw [heisenbergMatrix_eq_mul σ hi hik, det_mul, det_mul, det_transvection_of_ne _ _ hik,
    det_transvection_of_ne _ _ h3, det_transvection_of_ne _ _ hi, one_mul, one_mul]

theorem rootMatrix_mul {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (c d : F) :
    rootMatrix σ i j c * rootMatrix σ i j d = rootMatrix σ i j (c + d) := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  have h2 : Fin.rev i ≠ Fin.rev j := fun h => hij (Fin.rev_injective h)
  have h3 : j ≠ i := fun h => hij h.symm
  rw [rootMatrix, rootMatrix, rootMatrix]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_of_ne _ _ _ _ h1, single_mul_single_of_ne _ _ _ _ h2,
    single_mul_single_of_ne _ _ _ _ h3, single_mul_single_of_ne _ _ _ _ hj, map_add,
    Matrix.single_add]
  abel

theorem rootMatrix_zero {n : ℕ} (i j : Fin n) : rootMatrix σ i j 0 = 1 := by
  simp [rootMatrix]

theorem longRootMatrix_mul {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) (c d : F) :
    longRootMatrix i c * longRootMatrix i d = longRootMatrix i (c + d) := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  rw [longRootMatrix, longRootMatrix, longRootMatrix]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_of_ne _ _ _ _ h1, Matrix.single_add]
  abel

theorem longRootMatrix_zero {n : ℕ} (i : Fin n) : longRootMatrix (F := F) i 0 = 1 := by
  simp [longRootMatrix]

theorem heisenbergMatrix_mul {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b a' b' : F) :
    heisenbergMatrix σ i k a b * heisenbergMatrix σ i k a' b' =
      heisenbergMatrix σ i k (a + a') (b + b' - a * σ a') := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  have h2 : k ≠ i := fun h => hik h.symm
  have h3 : Fin.rev i ≠ k := fun h => hik (by rw [← Fin.rev_rev i, h, hk])
  rw [heisenbergMatrix, heisenbergMatrix, heisenbergMatrix, sub_eq_add_neg (b + b') (a * σ a'),
    Matrix.single_add, Matrix.single_add, ← single_neg]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_same, single_mul_single_of_ne _ _ _ _ h1,
    single_mul_single_of_ne _ _ _ _ h2, single_mul_single_of_ne _ _ _ _ h3, map_add,
    Matrix.single_add]
  abel

theorem heisenbergMatrix_zero {n : ℕ} (i k : Fin n) : heisenbergMatrix σ i k 0 0 = 1 := by
  simp [heisenbergMatrix]

@[expose] def traceZero : AddSubgroup F where
  carrier := {c | c + σ c = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    calc a + b + (σ a + σ b) = (a + σ a) + (b + σ b) := by ring
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_neg] at *
    rw [← neg_add, ha, neg_zero]

theorem mem_traceZero {c : F} : c ∈ traceZero σ ↔ c + σ c = 0 := Iff.rfl

include hσ

@[expose] noncomputable def rootHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) : Multiplicative F →* SU σ n where
  toFun c := ⟨⟨rootMatrix σ i j c.toAdd, rootMatrix σ i j (-c.toAdd),
      by rw [rootMatrix_mul σ hij hi hj, add_neg_cancel, rootMatrix_zero],
      by rw [rootMatrix_mul σ hij hi hj, neg_add_cancel, rootMatrix_zero]⟩,
    det_rootMatrix σ hij hj _, rootMatrix_isometry σ hσ hij hi hj _⟩
  map_one' := Subtype.ext (Units.ext (rootMatrix_zero σ i j))
  map_mul' c d := Subtype.ext (Units.ext (by
    change rootMatrix σ i j (c.toAdd + d.toAdd) =
      rootMatrix σ i j c.toAdd * rootMatrix σ i j d.toAdd
    rw [rootMatrix_mul σ hij hi hj]))

theorem coe_rootHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (c : Multiplicative F) :
    ((rootHom σ hσ hij hi hj c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      rootMatrix σ i j c.toAdd :=
  rfl

omit hσ in
@[expose] noncomputable def longRootHom {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    Multiplicative (traceZero σ) →* SU σ n where
  toFun c := ⟨⟨longRootMatrix i (c.toAdd : F), longRootMatrix i (-(c.toAdd : F)),
      by rw [longRootMatrix_mul hi, add_neg_cancel, longRootMatrix_zero],
      by rw [longRootMatrix_mul hi, neg_add_cancel, longRootMatrix_zero]⟩,
    det_longRootMatrix hi _, longRootMatrix_isometry σ hi c.toAdd.2⟩
  map_one' := Subtype.ext (Units.ext (longRootMatrix_zero i))
  map_mul' c d := Subtype.ext (Units.ext (by
    change longRootMatrix i ((c.toAdd : F) + d.toAdd) =
      longRootMatrix i (c.toAdd : F) * longRootMatrix i (d.toAdd : F)
    rw [longRootMatrix_mul hi]))

omit hσ in
theorem coe_longRootHom {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i)
    (c : Multiplicative (traceZero σ)) :
    ((longRootHom σ hi c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      longRootMatrix i (c.toAdd : F) :=
  rfl

@[expose] noncomputable def heisenbergSubgroup {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i)
    (hik : i ≠ k) (hk : Fin.rev k = k) : Subgroup (SU σ n) where
  carrier := {g | ∃ a b : F, b + σ b + σ a * a = 0 ∧
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = heisenbergMatrix σ i k a b}
  mul_mem' := by
    rintro g g' ⟨a, b, hab, hg⟩ ⟨a', b', hab', hg'⟩
    refine ⟨a + a', b + b' - a * σ a', ?_, ?_⟩
    · rw [map_sub, map_add, map_add, map_mul, hσ]
      calc b + b' - a * σ a' + (σ b + σ b' - σ a * a') + (σ a + σ a') * (a + a')
          = (b + σ b + σ a * a) + (b' + σ b' + σ a' * a') := by ring
        _ = 0 := by rw [hab, hab', add_zero]
    · change ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((g' : GL (Fin n) F) : Matrix _ _ F)
        = _
      rw [hg, hg', heisenbergMatrix_mul σ hi hik hk]
  one_mem' := ⟨0, 0, by simp, by rw [heisenbergMatrix_zero]; rfl⟩
  inv_mem' := by
    rintro g ⟨a, b, hab, hg⟩
    refine ⟨-a, -b - a * σ a, ?_, ?_⟩
    · rw [map_sub, map_neg, map_neg, map_mul, hσ]
      calc -b - a * σ a + (-σ b - σ a * a) + -σ a * -a = -(b + σ b + σ a * a) := by ring
        _ = 0 := by rw [hab, neg_zero]
    · have hmul : heisenbergMatrix σ i k a b * heisenbergMatrix σ i k (-a) (-b - a * σ a) = 1 := by
        rw [heisenbergMatrix_mul σ hi hik hk, map_neg]
        have h1 : a + -a = 0 := add_neg_cancel a
        have h2 : b + (-b - a * σ a) - a * -σ a = 0 := by ring
        rw [h1, h2, heisenbergMatrix_zero]
      have hinv : ((g⁻¹ : SU σ n) : GL (Fin n) F) = (g : GL (Fin n) F)⁻¹ := rfl
      rw [hinv, Matrix.coe_units_inv, hg]
      exact Matrix.inv_eq_right_inv hmul

end CFSG.LieType.Universal.Unitary
