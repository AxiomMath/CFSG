module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionHermitian

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r : ℕ}

@[expose] def IsRad (x : Fin r → K) (C : Matrix (Fin r) (Fin r) K) : Prop :=
  C + (C.map h.bar)ᵀ = -vecMulVec x fun j => h.bar (x j)

theorem barInvT_one : barInvT h (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [barInvT, Matrix.map_one _ (map_zero _) (map_one _), inv_one, transpose_one]

theorem oddDiag_one : oddDiag h (1 : Matrix (Fin r) (Fin r) K) 1 = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp [oddDiag, blk3, barInvT_one, one_apply]
  exact Subsingleton.elim k l

theorem oddUni_zero : oddUni h (0 : Fin r → K) 0 = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> simp [oddUni, blk3, one_apply]

theorem isRad_zero : IsRad h (0 : Fin r → K) 0 := by
  simp [IsRad]

variable {h}

theorem oddUni_gram {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) :
    ((oddUni h x C).map h.bar)ᵀ * hypGram r 1 K * oddUni h x C = hypGram r 1 K := by
  have := oddProd_gram (h := h) (A := 1) (d := 1) (by rw [det_one]; exact isUnit_one)
    (by rw [map_one, one_mul]) hC
  rwa [oddDiag_one, Matrix.one_mul] at this

variable (h) in
theorem det_oddUni (x : Fin r → K) (C : Matrix (Fin r) (Fin r) K) : (oddUni h x C).det = 1 := by
  have := det_oddProd (h := h) (A := 1) (by rw [det_one]; exact isUnit_one) 1 x C
  rwa [oddDiag_one, Matrix.one_mul, det_one, map_one, one_mul, div_one] at this

theorem isRad_of_gram {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K}
    (hg : ((oddUni h x C).map h.bar)ᵀ * hypGram r 1 K * oddUni h x C = hypGram r 1 K) :
    IsRad h x C := by
  obtain ⟨-, -, -, h4⟩ := (blk3_gram_iff h _ _ _ _ _ _).mp hg
  unfold IsRad
  ext i j
  have e := congrFun (congrFun h4 i) j
  simp only [Matrix.add_apply, mul_apply, transpose_apply, map_apply, replicateRow_apply,
    Finset.univ_unique, Finset.sum_singleton, Matrix.zero_apply, map_neg, h.bar_bar,
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, Matrix.one_mul,
    Matrix.mul_one] at e
  simp only [Matrix.add_apply, Matrix.neg_apply, transpose_apply, map_apply, vecMulVec_apply]
  linear_combination e

@[expose] def nElt {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) :
    hypSU h r 1 :=
  mkHypSU h (oddUni h x C) (oddUni_gram hC) (det_oddUni h x C)

theorem coe_nElt {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) :
    (((nElt hC : hypSU h r 1) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      oddUni h x C :=
  rfl

theorem nElt_ext {x y : Fin r → K} {C D : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C)
    (hD : IsRad h y D) (hxy : x = y) (hCD : C = D) : nElt hC = nElt hD := by
  subst hxy
  subst hCD
  rfl

theorem exists_eq_nElt {g : hypSU h r 1} {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K}
    (hg : ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = oddUni h x C) :
    ∃ hC : IsRad h x C, g = nElt hC := by
  have hC : IsRad h x C := isRad_of_gram (by rw [← hg]; exact (mem_hypSU.mp g.2).1)
  exact ⟨hC, Subtype.ext (Units.ext hg)⟩

theorem eq_of_nElt_eq {x y : Fin r → K} {C D : Matrix (Fin r) (Fin r) K} {hC : IsRad h x C}
    {hD : IsRad h y D} (he : nElt hC = nElt hD) : x = y ∧ C = D := by
  have hm := congrArg (fun g : hypSU h r 1 =>
    ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)) he
  simp only [coe_nElt] at hm
  refine ⟨funext fun i => ?_, ?_⟩
  · simpa [oddUni] using congrFun (congrFun hm (.inl i)) (.inr (.inl 0))
  · ext i j
    simpa [oddUni] using congrFun (congrFun hm (.inl i)) (.inr (.inr j))

variable (h) in
theorem oddUni_mul (x y : Fin r → K) (C D : Matrix (Fin r) (Fin r) K) :
    oddUni h x C * oddUni h y D =
      oddUni h (x + y) (C + D - vecMulVec x fun j => h.bar (y j)) := by
  rw [oddUni, oddUni, oddUni, blk3_mul]
  congr 1
  · rw [Matrix.one_mul]
  · ext i k
    simp [add_comm]
  · ext i j
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.sub_apply, mul_apply,
      replicateCol_apply, replicateRow_apply, Finset.univ_unique, Finset.sum_singleton,
      vecMulVec_apply]
    ring
  · rw [Matrix.one_mul]
  · ext k j
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, replicateRow_apply, Pi.add_apply,
      map_add]
    ring
  · rw [Matrix.one_mul]

theorem isRad_mul {x y : Fin r → K} {C D : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C)
    (hD : IsRad h y D) : IsRad h (x + y) (C + D - vecMulVec x fun j => h.bar (y j)) := by
  unfold IsRad at hC hD ⊢
  ext i j
  have h1 := congrFun (congrFun hC i) j
  have h2 := congrFun (congrFun hD i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, transpose_apply, map_apply,
    vecMulVec_apply, Pi.add_apply, map_add, map_sub, map_mul, h.bar_bar] at h1 h2 ⊢
  linear_combination h1 + h2

theorem nElt_mul {x y : Fin r → K} {C D : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C)
    (hD : IsRad h y D) : nElt hC * nElt hD = nElt (isRad_mul hC hD) :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_nElt, coe_nElt, coe_nElt, oddUni_mul]))

variable (h) in
theorem nElt_zero : nElt (isRad_zero h (r := r)) = 1 :=
  Subtype.ext (Units.ext (oddUni_zero h))

theorem isRad_inv {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) :
    IsRad h (-x) (-C - vecMulVec x fun j => h.bar (x j)) := by
  unfold IsRad at hC ⊢
  ext i j
  have h1 := congrFun (congrFun hC i) j
  have h2 := congrFun (congrFun hC j) i
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, transpose_apply, map_apply,
    vecMulVec_apply, Pi.neg_apply, map_neg, map_sub, map_mul, h.bar_bar] at h1 h2 ⊢
  linear_combination -h1

theorem nElt_inv {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) :
    (nElt hC)⁻¹ = nElt (isRad_inv hC) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [nElt_mul, ← nElt_zero h]
  refine nElt_ext _ _ (add_neg_cancel x) ?_
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, vecMulVec_apply, Pi.neg_apply,
    map_neg, Matrix.zero_apply]
  ring

variable (h) in
theorem isRad_comm (x y : Fin r → K) :
    IsRad h 0 (vecMulVec y (fun j => h.bar (x j)) - vecMulVec x fun j => h.bar (y j)) := by
  unfold IsRad
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, transpose_apply, map_apply, vecMulVec_apply,
    map_sub, map_mul, h.bar_bar, Matrix.neg_apply, Pi.zero_apply, zero_mul, neg_zero]
  ring

theorem nElt_mul_comm {x y : Fin r → K} {C D : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C)
    (hD : IsRad h y D) : nElt hC * nElt hD = nElt (isRad_comm h x y) * (nElt hD * nElt hC) := by
  rw [nElt_mul, nElt_mul, nElt_mul]
  refine nElt_ext _ _ (by rw [zero_add, add_comm]) ?_
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.zero_apply, zero_mul,
    sub_zero]
  ring

variable (h) in
theorem nElt_zero_mul_comm {B : Matrix (Fin r) (Fin r) K} (hB : IsRad h 0 B) {x : Fin r → K}
    {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) : nElt hB * nElt hC = nElt hC * nElt hB := by
  rw [nElt_mul, nElt_mul]
  refine nElt_ext _ _ (by rw [zero_add, add_zero]) ?_
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.zero_apply, zero_mul,
    mul_zero, map_zero, sub_zero]
  ring

variable (h r) in
@[expose] def radN : Subgroup (hypSU h r 1) where
  carrier := {g | ∃ (x : Fin r → K) (C : Matrix (Fin r) (Fin r) K) (hC : IsRad h x C),
    nElt hC = g}
  one_mem' := ⟨0, 0, isRad_zero h, nElt_zero h⟩
  mul_mem' := by
    rintro _ _ ⟨x, C, hC, rfl⟩ ⟨y, D, hD, rfl⟩
    exact ⟨_, _, _, (nElt_mul hC hD).symm⟩
  inv_mem' := by
    rintro _ ⟨x, C, hC, rfl⟩
    exact ⟨_, _, _, (nElt_inv hC).symm⟩

variable (h r) in
@[expose] def radV : Subgroup (hypSU h r 1) where
  carrier := {g | ∃ (B : Matrix (Fin r) (Fin r) K) (hB : IsRad h 0 B), nElt hB = g}
  one_mem' := ⟨0, isRad_zero h, nElt_zero h⟩
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
    exact ⟨_, add_zero (0 : Fin r → K) ▸ isRad_mul hB hB', by
      rw [nElt_mul]
      exact nElt_ext _ _ (add_zero 0).symm rfl⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨_, neg_zero (G := Fin r → K) ▸ isRad_inv hB, by
      rw [nElt_inv]
      exact nElt_ext _ _ neg_zero.symm rfl⟩

theorem mem_radN {g : hypSU h r 1} :
    g ∈ radN h r ↔ ∃ (x : Fin r → K) (C : Matrix (Fin r) (Fin r) K) (hC : IsRad h x C),
      nElt hC = g :=
  Iff.rfl

theorem mem_radV {g : hypSU h r 1} :
    g ∈ radV h r ↔ ∃ (B : Matrix (Fin r) (Fin r) K) (hB : IsRad h 0 B), nElt hB = g :=
  Iff.rfl

theorem radV_le_radN : radV h r ≤ radN h r := by
  rintro _ ⟨B, hB, rfl⟩
  exact ⟨0, B, hB, rfl⟩

theorem nElt_mem_radN {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) :
    nElt hC ∈ radN h r :=
  ⟨x, C, hC, rfl⟩

theorem nElt_mem_radV {B : Matrix (Fin r) (Fin r) K} (hB : IsRad h 0 B) : nElt hB ∈ radV h r :=
  ⟨B, hB, rfl⟩

theorem commutatorElement_mem_radV {g g' : hypSU h r 1} (hg : g ∈ radN h r)
    (hg' : g' ∈ radN h r) : ⁅g, g'⁆ ∈ radV h r := by
  obtain ⟨x, C, hC, rfl⟩ := hg
  obtain ⟨y, D, hD, rfl⟩ := hg'
  rw [commutatorElement_def, nElt_mul_comm hC hD,
    show ∀ a b c : hypSU h r 1, a * (b * c) * c⁻¹ * b⁻¹ = a from fun a b c => by group]
  exact nElt_mem_radV _

theorem mul_comm_of_mem_radV {g g' : hypSU h r 1} (hg : g ∈ radV h r) (hg' : g' ∈ radN h r) :
    g * g' = g' * g := by
  obtain ⟨B, hB, rfl⟩ := hg
  obtain ⟨x, C, hC, rfl⟩ := hg'
  exact nElt_zero_mul_comm h hB hC

theorem exists_isRad (x : Fin r → K) : ∃ C : Matrix (Fin r) (Fin r) K, IsRad h x C := by
  classical
  have hfix : ∀ i, -(x i * h.bar (x i)) ∈ h.fixedField := fun i => by
    rw [UnitaryFieldData.mem_fixedField, map_neg, map_mul, h.bar_bar, mul_comm]
  choose c hc using fun i => h.traceLin_surjective ⟨_, hfix i⟩
  refine ⟨of fun i j => if i < j then -(x i * h.bar (x j)) else if i = j then c i else 0, ?_⟩
  unfold IsRad
  ext i j
  have hci : h.trace (c i) = -(x i * h.bar (x i)) := by
    have := congrArg Subtype.val (hc i)
    rwa [UnitaryFieldData.coe_traceLin] at this
  simp only [Matrix.add_apply, transpose_apply, map_apply, of_apply, Matrix.neg_apply,
    vecMulVec_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [ite_eq_left hij, ite_eq_right (lt_asymm hij), ite_eq_right hij.ne', map_zero, add_zero]
  · rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl]
    exact hci
  · rw [ite_eq_right (lt_asymm hij), ite_eq_right hij.ne', ite_eq_left hij, zero_add, map_neg,
      map_mul, h.bar_bar, mul_comm]

variable (h) in
@[expose] def dval (A : Matrix (Fin r) (Fin r) K) : K :=
  h.bar A.det / A.det

variable (h) in
@[expose] def lMat (A : Matrix (Fin r) (Fin r) K) : Matrix (HypIndex r 1) (HypIndex r 1) K :=
  oddDiag h A (dval h A)

theorem dval_mul (A B : Matrix (Fin r) (Fin r) K) : dval h (A * B) = dval h A * dval h B := by
  rw [dval, dval, dval, det_mul, map_mul, mul_div_mul_comm]

theorem dval_of_det_eq_one {A : Matrix (Fin r) (Fin r) K} (hA : A.det = 1) : dval h A = 1 := by
  rw [dval, hA, map_one, div_one]

theorem bar_dval_mul_self {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    h.bar (dval h A) * dval h A = 1 :=
  bar_mul_self_of_eq_div hA rfl

theorem dval_ne_zero {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) : dval h A ≠ 0 :=
  right_ne_zero_of_mul_eq_one (bar_dval_mul_self hA)

theorem lMat_gram {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    ((lMat h A).map h.bar)ᵀ * hypGram r 1 K * lMat h A = hypGram r 1 K := by
  have := oddProd_gram (h := h) (C := 0) (x := 0) hA (bar_dval_mul_self hA) (isRad_zero h)
  rwa [oddUni_zero, Matrix.mul_one] at this

theorem det_lMat {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) : (lMat h A).det = 1 := by
  have := det_oddProd (h := h) hA (dval h A) 0 0
  rw [oddUni_zero, Matrix.mul_one] at this
  rw [lMat, this, dval]
  have h0 : A.det ≠ 0 := hA.ne_zero
  have h0' : h.bar A.det ≠ 0 := (map_ne_zero h.bar).mpr h0
  field_simp

variable (h) in
theorem lMat_one : lMat h (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [lMat, dval_of_det_eq_one det_one, oddDiag_one]

variable (h) in
theorem lMat_mul (A B : Matrix (Fin r) (Fin r) K) : lMat h (A * B) = lMat h A * lMat h B := by
  rw [lMat, lMat, lMat, oddDiag, oddDiag, oddDiag, blk3_mul, barInvT_mul, dval_mul]
  congr 1
  · simp
  · simp
  · ext k l
    simp [mul_apply]
  · simp

variable (h r) in
@[expose] def lHom : GL (Fin r) K →* hypSU h r 1 where
  toFun A := mkHypSU h (lMat h A) (lMat_gram (isUnits_det_units A)) (det_lMat (isUnits_det_units A))
  map_one' := Subtype.ext (Units.ext (by
    rw [coe_mkHypSU, Units.val_one]
    exact lMat_one h))
  map_mul' A B := Subtype.ext (Units.ext (by
    change lMat h ((A : Matrix (Fin r) (Fin r) K) * (B : Matrix (Fin r) (Fin r) K)) =
      lMat h (A : Matrix (Fin r) (Fin r) K) * lMat h (B : Matrix (Fin r) (Fin r) K)
    exact lMat_mul h _ _))

theorem coe_lHom (A : GL (Fin r) K) :
    (((lHom h r A : hypSU h r 1) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      lMat h A :=
  rfl

theorem lMat_mul_oddUni {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) (x : Fin r → K)
    (C : Matrix (Fin r) (Fin r) K) :
    lMat h A * oddUni h x C =
      oddUni h ((dval h A)⁻¹ • (A *ᵥ x)) (A * C * (A.map h.bar)ᵀ) * lMat h A := by
  have hd0 : dval h A ≠ 0 := dval_ne_zero hA
  have hbd : (h.bar (dval h A))⁻¹ = dval h A := inv_eq_of_mul_eq_one_right (bar_dval_mul_self hA)
  have hrow : (replicateRow (Fin 1) fun j => -h.bar (((dval h A)⁻¹ • (A *ᵥ x)) j)) =
      (-(h.bar (dval h A))⁻¹) •
        ((replicateRow (Fin 1) fun j => h.bar (x j)) * (A.map h.bar)ᵀ) := by
    ext k j
    simp only [replicateRow_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
      map_mul, map_sum, map_inv₀, Matrix.smul_apply, mul_apply, transpose_apply, map_apply,
      Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun l _ => ?_)
    ring
  rw [lMat, oddDiag_mul_oddUni, oddUni, oddDiag, blk3_mul]
  congr 1
  · rw [Matrix.one_mul]
  · ext i k
    simp only [mul_apply, replicateCol_apply, of_apply, Finset.univ_unique, Finset.sum_singleton,
      Matrix.mul_zero, zero_add, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
    field_simp
  · rw [Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc,
      conjTranspose_mul_barInvT hA, Matrix.mul_one]
  · rw [Matrix.one_mul]
  · rw [Matrix.mul_zero, zero_add, hrow, Matrix.smul_mul, Matrix.mul_assoc,
      conjTranspose_mul_barInvT hA, Matrix.mul_one]
    ext k j
    rw [of_apply, Matrix.smul_apply, replicateRow_apply, smul_eq_mul, hbd, neg_mul]
  · rw [Matrix.one_mul]

theorem exists_lHom_mul_nElt (A : GL (Fin r) K) {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K}
    (hC : IsRad h x C) :
    ∃ hC' : IsRad h ((dval h (A : Matrix (Fin r) (Fin r) K))⁻¹ •
        ((A : Matrix (Fin r) (Fin r) K) *ᵥ x))
        (A * C * ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ),
      lHom h r A * nElt hC * (lHom h r A)⁻¹ = nElt hC' := by
  refine exists_eq_nElt ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
    coe_lHom, coe_nElt, lMat_mul_oddUni (isUnits_det_units A), Matrix.mul_assoc,
    ← coe_lHom (h := h), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem nElt_mem_hypUnitriangular {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K}
    (hC : IsRad h x C) : nElt hC ∈ hypUnitriangular h r 1 := by
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_odd_iff (h := h) (oddUni h x C)).mpr
    ⟨1, C, x, ⟨blockTriangular_one, fun i => one_apply_eq i⟩, hC, by
      rw [oddDiag_one, Matrix.one_mul]⟩
  obtain ⟨hC', hge⟩ := exists_eq_nElt hgm
  exact hge ▸ hg

theorem radN_le_hypUnitriangular : radN h r ≤ hypUnitriangular h r 1 := by
  rintro _ ⟨x, C, hC, rfl⟩
  exact nElt_mem_hypUnitriangular hC

theorem lMat_eq_oddDiag {A : Matrix (Fin r) (Fin r) K} (hA : A.det = 1) :
    lMat h A = oddDiag h A 1 := by
  rw [lMat, dval_of_det_eq_one hA]

theorem lHom_mem_hypUnitriangular {A : GL (Fin r) K}
    (hA : IsUnitriangular (A : Matrix (Fin r) (Fin r) K)) :
    lHom h r A ∈ hypUnitriangular h r 1 := by
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_odd_iff (h := h)
    (lMat h (A : Matrix (Fin r) (Fin r) K))).mpr ⟨(A : Matrix (Fin r) (Fin r) K), 0, 0, hA,
      isRad_zero h, by rw [oddUni_zero, Matrix.mul_one, lMat_eq_oddDiag hA.det_eq_one]⟩
  have : g = lHom h r A := Subtype.ext (Units.ext hgm)
  rwa [← this]

theorem exists_lHom_mul_nElt_of_mem {g : hypSU h r 1} (hg : g ∈ hypUnitriangular h r 1) :
    ∃ (A : GL (Fin r) K) (_ : IsUnitriangular (A : Matrix (Fin r) (Fin r) K)) (x : Fin r → K)
      (C : Matrix (Fin r) (Fin r) K) (hC : IsRad h x C), g = lHom h r A * nElt hC := by
  obtain ⟨A, C, x, hA, hC, hgm⟩ :=
    (exists_mem_hypUnitriangular_odd_iff (h := h) _).mp ⟨g, hg, rfl⟩
  have hC' : IsRad h x C := hC
  let A' : GL (Fin r) K := ⟨A, A⁻¹, mul_nonsing_inv A hA.isUnit_det,
    nonsing_inv_mul A hA.isUnit_det⟩
  refine ⟨A', hA, x, C, hC', Subtype.ext (Units.ext ?_)⟩
  rw [hgm, Subgroup.coe_mul, Units.val_mul, coe_lHom, coe_nElt, lMat_eq_oddDiag hA.det_eq_one]

theorem eq_one_of_nElt_eq_lHom {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K}
    {hC : IsRad h x C} {A : GL (Fin r) K} (he : nElt hC = lHom h r A) : A = 1 := by
  have hm := congrArg (fun g : hypSU h r 1 =>
    ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)) he
  simp only [coe_nElt, coe_lHom] at hm
  refine Units.ext ?_
  ext i j
  simpa [oddUni, lMat, oddDiag] using (congrFun (congrFun hm (.inl i)) (.inl j)).symm

theorem eq_one_of_hypProj_lHom {A : GL (Fin r) K} (hA : (A : Matrix (Fin r) (Fin r) K).det = 1)
    (h1 : hypProj h r 1 (lHom h r A) = 1) : A = 1 := by
  rw [← MonoidHom.mem_ker, ker_hypProj] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  have hm := congrArg Units.val hc
  rw [coe_lHom, GeneralLinearGroup.coe_scalar, lMat_eq_oddDiag hA] at hm
  have hc1 : (c : K) = 1 := by
    have := congrFun (congrFun hm (.inr (.inl 0))) (.inr (.inl 0))
    simpa [oddDiag] using this.symm
  refine Units.ext ?_
  ext i j
  have := congrFun (congrFun hm (.inl i)) (.inl j)
  simpa [oddDiag, hc1, one_apply] using this

section FieldTwo

open MatrixExtension

theorem bar_eq_sq (h : UnitaryFieldData 2 1 K) (c : K) : h.bar c = c ^ 2 := by
  rw [h.bar_apply, pow_one]

theorem card_eq_four (h : UnitaryFieldData 2 1 K) : Nat.card K = 4 := by
  rw [h.card]
  norm_num

theorem map_bar_transpose (h : UnitaryFieldData 2 1 K) (A : Matrix (Fin r) (Fin r) K) :
    (A.map h.bar)ᵀ = hconj A := by
  ext i j
  rw [transpose_apply, map_apply, bar_eq_sq, hconj_apply]

theorem vecMulVec_bar (h : UnitaryFieldData 2 1 K) (x y : Fin r → K) :
    (vecMulVec x fun j => h.bar (y j)) = vecMulVec x fun j => y j ^ 2 := by
  ext i j
  rw [vecMulVec_apply, vecMulVec_apply, bar_eq_sq]

theorem dval_eq_det (h : UnitaryFieldData 2 1 K) (A : Matrix (Fin r) (Fin r) K) :
    dval h A = A.det := by
  rw [dval, bar_eq_sq]
  rcases eq_or_ne A.det 0 with h0 | h0
  · rw [h0]
    simp
  · field_simp

variable [CharP K 2]

theorem isRad_iff {h : UnitaryFieldData 2 1 K} {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} :
    IsRad h x C ↔ C + hconj C = hermQ x := by
  rw [IsRad, map_bar_transpose, vecMulVec_bar, show (-vecMulVec x fun j => x j ^ 2) = hermQ x by
    ext i j
    exact CharTwo.neg_eq _]

theorem isRad_zero_iff {h : UnitaryFieldData 2 1 K} {B : Matrix (Fin r) (Fin r) K} :
    IsRad h 0 B ↔ hconj B = B := by
  rw [isRad_iff, show hermQ (0 : Fin r → K) = 0 by ext i j; simp [hermQ]]
  constructor
  · intro hB
    rw [eq_neg_of_add_eq_zero_right hB]
    ext i j
    exact CharTwo.neg_eq _
  · intro hB
    rw [hB]
    ext i j
    exact CharTwo.add_self_eq_zero _

theorem commMat_eq_hermH (h : UnitaryFieldData 2 1 K) (x y : Fin r → K) :
    (vecMulVec y (fun j => h.bar (x j)) - vecMulVec x fun j => h.bar (y j)) = hermH x y := by
  rw [vecMulVec_bar, vecMulVec_bar, hermH, sub_eq_add_neg, add_comm]
  congr 1
  ext i j
  exact CharTwo.neg_eq _

omit [CharP K 2] in
theorem exists_lHom_mul_nElt_two {h : UnitaryFieldData 2 1 K} (A : GL (Fin r) K)
    {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) :
    ∃ hC' : IsRad h (((A : Matrix (Fin r) (Fin r) K).det)⁻¹ • ((A : Matrix (Fin r) (Fin r) K) *ᵥ x))
        (A * C * hconj (A : Matrix (Fin r) (Fin r) K)),
      lHom h r A * nElt hC * (lHom h r A)⁻¹ = nElt hC' := by
  obtain ⟨hC', he⟩ := exists_lHom_mul_nElt A hC
  have e1 : (dval h (A : Matrix (Fin r) (Fin r) K))⁻¹ • ((A : Matrix (Fin r) (Fin r) K) *ᵥ x) =
      ((A : Matrix (Fin r) (Fin r) K).det)⁻¹ • ((A : Matrix (Fin r) (Fin r) K) *ᵥ x) := by
    rw [dval_eq_det]
  have e2 : (A : Matrix (Fin r) (Fin r) K) * C * ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ =
      A * C * hconj (A : Matrix (Fin r) (Fin r) K) := by
    rw [map_bar_transpose]
  rw [e1, e2] at hC'
  exact ⟨hC', he.trans (nElt_ext _ _ e1 e2)⟩

end FieldTwo

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
