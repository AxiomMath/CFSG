module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoMatrices

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.SpecialLinear

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r : ℕ}

@[expose] def IsHerm (B : Matrix (Fin r) (Fin r) K) : Prop :=
  B + (B.map h.bar)ᵀ = 0

theorem isHerm_zero : IsHerm h (0 : Matrix (Fin r) (Fin r) K) := by
  simp [IsHerm]

variable {h}

theorem isHerm_add {B B' : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) (hB' : IsHerm h B') :
    IsHerm h (B + B') := by
  unfold IsHerm at hB hB' ⊢
  rw [Matrix.map_add _ (map_add h.bar), transpose_add,
    show B + B' + ((B.map h.bar)ᵀ + (B'.map h.bar)ᵀ) =
      (B + (B.map h.bar)ᵀ) + (B' + (B'.map h.bar)ᵀ) by abel, hB, hB', add_zero]

theorem isHerm_neg {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) : IsHerm h (-B) := by
  unfold IsHerm at hB ⊢
  rw [Matrix.map_neg _ (map_neg h.bar), transpose_neg, ← neg_add, hB, neg_zero]

variable (h) in
theorem barInvT_one : barInvT h (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [barInvT, Matrix.map_one _ (map_zero _) (map_one _), inv_one, transpose_one]

variable (h) in
theorem evenMat_one_zero : evenMat h (1 : Matrix (Fin r) (Fin r) K) 0 = 1 := by
  rw [evenMat, barInvT_one, Matrix.mul_zero]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  all_goals try exact isEmptyElim ‹Fin 0›
  all_goals simp [blk3, one_apply]

theorem det_evenMat_one (B : Matrix (Fin r) (Fin r) K) : (evenMat h 1 B).det = 1 := by
  rw [det_evenMat (by rw [det_one]; exact isUnit_one), det_one, map_one, div_one]

@[expose] def nElt {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) : hypSU h r 0 :=
  mkHypSU h (evenMat h 1 B) (evenMat_gram (by rw [det_one]; exact isUnit_one) hB)
    (det_evenMat_one B)

theorem coe_nElt {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) :
    (((nElt hB : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      evenMat h 1 B :=
  rfl

theorem nElt_ext {B B' : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) (hB' : IsHerm h B')
    (he : B = B') : nElt hB = nElt hB' := by
  subst he
  rfl

variable (h) in
theorem evenMat_one_mul (B B' : Matrix (Fin r) (Fin r) K) :
    evenMat h 1 B * evenMat h 1 B' = evenMat h 1 (B + B') := by
  rw [evenMat_mul (by rw [det_one]; exact isUnit_one), Matrix.one_mul, inv_one, Matrix.one_mul,
    barInvT_one, Matrix.mul_one, add_comm]

theorem nElt_mul {B B' : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) (hB' : IsHerm h B') :
    nElt hB * nElt hB' = nElt (isHerm_add hB hB') :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_nElt, coe_nElt, coe_nElt, evenMat_one_mul]))

variable (h) in
theorem nElt_zero : nElt (isHerm_zero h (r := r)) = 1 :=
  Subtype.ext (Units.ext (evenMat_one_zero h))

theorem nElt_inv {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) :
    (nElt hB)⁻¹ = nElt (isHerm_neg hB) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [nElt_mul, ← nElt_zero h]
  exact nElt_ext _ _ (add_neg_cancel B)

theorem nElt_mul_comm {B B' : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) (hB' : IsHerm h B') :
    nElt hB * nElt hB' = nElt hB' * nElt hB := by
  rw [nElt_mul, nElt_mul]
  exact nElt_ext _ _ (add_comm B B')

variable (h r) in
@[expose] def radN : Subgroup (hypSU h r 0) where
  carrier := {g | ∃ (B : Matrix (Fin r) (Fin r) K) (hB : IsHerm h B), nElt hB = g}
  one_mem' := ⟨0, isHerm_zero h, nElt_zero h⟩
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
    exact ⟨_, _, (nElt_mul hB hB').symm⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨_, _, (nElt_inv hB).symm⟩

theorem nElt_mem_radN {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) : nElt hB ∈ radN h r :=
  ⟨B, hB, rfl⟩

theorem mul_comm_of_mem_radN {g g' : hypSU h r 0} (hg : g ∈ radN h r) (hg' : g' ∈ radN h r) :
    g * g' = g' * g := by
  obtain ⟨B, hB, rfl⟩ := hg
  obtain ⟨B', hB', rfl⟩ := hg'
  exact nElt_mul_comm hB hB'

theorem eq_of_nElt_eq {B B' : Matrix (Fin r) (Fin r) K} {hB : IsHerm h B} {hB' : IsHerm h B'}
    (he : nElt hB = nElt hB') : B = B' := by
  have hm := congrArg (fun g : hypSU h r 0 =>
    ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K)) he
  simp only [coe_nElt] at hm
  ext i j
  simpa [evenMat] using congrFun (congrFun hm (.inl i)) (.inr (.inr j))

theorem isUnitriangular_one : IsUnitriangular (1 : Matrix (Fin r) (Fin r) K) :=
  ⟨blockTriangular_one, fun i => one_apply_eq i⟩

theorem nElt_mem_hypUnitriangular {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) :
    nElt hB ∈ hypUnitriangular h r 0 := by
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_even_iff (h := h) (evenMat h 1 B)).mpr
    ⟨1, B, isUnitriangular_one, hB, rfl⟩
  have : g = nElt hB := Subtype.ext (Units.ext hgm)
  rwa [← this]

variable (h r) in
@[expose] def detFixed : Subgroup (GL (Fin r) K) where
  carrier := {A | h.bar (A : Matrix (Fin r) (Fin r) K).det = (A : Matrix (Fin r) (Fin r) K).det}
  one_mem' := by
    change h.bar ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).det = _
    rw [Units.val_one, det_one, map_one]
  mul_mem' := by
    intro A B hA hB
    have hA' : h.bar (A : Matrix (Fin r) (Fin r) K).det = (A : Matrix (Fin r) (Fin r) K).det := hA
    have hB' : h.bar (B : Matrix (Fin r) (Fin r) K).det = (B : Matrix (Fin r) (Fin r) K).det := hB
    change h.bar ((A * B : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).det = _
    rw [Units.val_mul, det_mul, map_mul, hA', hB']
  inv_mem' := by
    intro A hA
    have hA' : h.bar (A : Matrix (Fin r) (Fin r) K).det = (A : Matrix (Fin r) (Fin r) K).det := hA
    change h.bar ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).det = _
    rw [coe_units_inv, det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hA']

theorem mem_detFixed {A : GL (Fin r) K} :
    A ∈ detFixed h r ↔
      h.bar (A : Matrix (Fin r) (Fin r) K).det = (A : Matrix (Fin r) (Fin r) K).det :=
  Iff.rfl

theorem det_ne_zero_of_GL (A : GL (Fin r) K) : (A : Matrix (Fin r) (Fin r) K).det ≠ 0 :=
  (isUnits_det_units A).ne_zero

theorem lMat_gram (A : GL (Fin r) K) :
    ((evenMat h (A : Matrix (Fin r) (Fin r) K) 0).map h.bar)ᵀ * hypGram r 0 K *
      evenMat h (A : Matrix (Fin r) (Fin r) K) 0 = hypGram r 0 K :=
  evenMat_gram (isUnits_det_units A) (by simp)

theorem det_lMat {A : GL (Fin r) K} (hA : A ∈ detFixed h r) :
    (evenMat h (A : Matrix (Fin r) (Fin r) K) 0).det = 1 := by
  rw [det_evenMat (isUnits_det_units A), mem_detFixed.mp hA, div_self (det_ne_zero_of_GL A)]

theorem evenMat_mul_evenMat_zero (A B : GL (Fin r) K) :
    evenMat h (A : Matrix (Fin r) (Fin r) K) 0 * evenMat h (B : Matrix (Fin r) (Fin r) K) 0 =
      evenMat h ((A * B : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 := by
  rw [evenMat_mul (isUnits_det_units B), Matrix.mul_zero, Matrix.zero_mul, add_zero,
    Units.val_mul]

variable (h r) in
@[expose] def lHom : detFixed h r →* hypSU h r 0 where
  toFun A := mkHypSU h (evenMat h ((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0)
    (lMat_gram (A : GL (Fin r) K)) (det_lMat A.2)
  map_one' := Subtype.ext (Units.ext (by
    change evenMat h ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 = 1
    rw [Units.val_one, evenMat_one_zero]))
  map_mul' A B := Subtype.ext (Units.ext (by
    change evenMat h (((A : GL (Fin r) K) * (B : GL (Fin r) K) : GL (Fin r) K) :
      Matrix (Fin r) (Fin r) K) 0 = evenMat h ((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 *
        evenMat h ((B : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0
    exact (evenMat_mul_evenMat_zero _ _).symm))

theorem coe_lHom (A : detFixed h r) :
    (((lHom h r A : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      evenMat h ((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 :=
  rfl

variable (h r) in
@[expose] def slHom : SpecialLinearGroup (Fin r) K →* detFixed h r where
  toFun A := ⟨SpecialLinearGroup.toGL A, mem_detFixed.mpr (by
    change h.bar (A : Matrix (Fin r) (Fin r) K).det = (A : Matrix (Fin r) (Fin r) K).det
    rw [A.2, map_one])⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ A B)

theorem coe_slHom (A : SpecialLinearGroup (Fin r) K) :
    (((slHom h r A : detFixed h r) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = A :=
  rfl

theorem isHerm_conj (A : Matrix (Fin r) (Fin r) K) {B : Matrix (Fin r) (Fin r) K}
    (hB : IsHerm h B) : IsHerm h (A * B * (A.map h.bar)ᵀ) := by
  unfold IsHerm at hB ⊢
  have e : ((A * B * (A.map h.bar)ᵀ).map h.bar)ᵀ = A * (B.map h.bar)ᵀ * (A.map h.bar)ᵀ := by
    rw [conjTranspose_mul', conjTranspose_mul', conjTranspose_conjTranspose', Matrix.mul_assoc]
  rw [e, ← Matrix.add_mul, ← Matrix.mul_add, hB, Matrix.mul_zero, Matrix.zero_mul]

theorem lHom_mul_nElt (A : detFixed h r) {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) :
    lHom h r A * nElt hB * (lHom h r A)⁻¹ = nElt (isHerm_conj (A : GL (Fin r) K) hB) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lHom, coe_nElt,
    coe_nElt]
  set A' := ((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)
  have hA := isUnits_det_units (A : GL (Fin r) K)
  rw [evenMat_mul (by rw [det_one]; exact isUnit_one), evenMat_mul hA]
  simp only [Matrix.mul_one, Matrix.one_mul, inv_one, Matrix.mul_zero, zero_add, add_zero,
    barInvT_one]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, conjTranspose_mul_barInvT hA, Matrix.mul_one,
    ← Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.one_mul]

theorem lHom_mem_hypUnitriangular {A : detFixed h r}
    (hA : IsUnitriangular ((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) :
    lHom h r A ∈ hypUnitriangular h r 0 := by
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_even_iff (h := h)
    (evenMat h ((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0)).mpr ⟨_, 0, hA, by simp, rfl⟩
  have : g = lHom h r A := Subtype.ext (Units.ext hgm)
  rwa [← this]

theorem exists_lHom_mul_nElt_of_mem {g : hypSU h r 0} (hg : g ∈ hypUnitriangular h r 0) :
    ∃ A ∈ LinearFlag.unitriangular r K, ∃ (B : Matrix (Fin r) (Fin r) K) (hB : IsHerm h B),
      g = lHom h r (slHom h r A) * nElt hB := by
  obtain ⟨A, B, hA, hB, hgm⟩ :=
    (exists_mem_hypUnitriangular_even_iff (h := h) _).mp ⟨g, hg, rfl⟩
  have hB' : IsHerm h B := hB
  refine ⟨(⟨A, hA.det_eq_one⟩ : SpecialLinearGroup (Fin r) K), ⟨fun i j hij => hA.1 hij, hA.2⟩,
    B, hB', Subtype.ext (Units.ext ?_)⟩
  rw [hgm, Subgroup.coe_mul, Units.val_mul, coe_lHom, coe_nElt]
  change evenMat h A B = evenMat h A 0 * evenMat h 1 B
  rw [evenMat_mul (by rw [det_one]; exact isUnit_one)]
  simp

theorem eq_one_of_hypProj_nElt_mul_lHom (hr : 1 ≤ r) {B : Matrix (Fin r) (Fin r) K}
    (hB : IsHerm h B) {A : SpecialLinearGroup (Fin r) K} (hA : A ∈ LinearFlag.unitriangular r K)
    (h1 : hypProj h r 0 (nElt hB) * hypProj h r 0 (lHom h r (slHom h r A)) = 1) : A = 1 := by
  have hAU : IsUnitriangular (((slHom h r A : detFixed h r) : GL (Fin r) K) :
      Matrix (Fin r) (Fin r) K) := ⟨fun i j hij => hA.1 i j hij, hA.2⟩
  have hU : nElt hB * lHom h r (slHom h r A) ∈ hypUnitriangular h r 0 :=
    mul_mem (nElt_mem_hypUnitriangular hB) (lHom_mem_hypUnitriangular hAU)
  have hinj := hypProj_injective_on h hr (Nat.zero_le 1)
  have he : (⟨nElt hB * lHom h r (slHom h r A), hU⟩ : hypUnitriangular h r 0) = 1 :=
    hinj (Subtype.ext (by
      simp only [MonoidHom.subgroupMap_apply_coe, map_mul, map_one]
      exact h1))
  have hm := congrArg (fun g : hypSU h r 0 =>
    ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K)) (congrArg Subtype.val he)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_nElt, coe_lHom, coe_slHom,
    OneMemClass.coe_one, Units.val_one] at hm
  rw [evenMat_mul (by rw [A.2]; exact isUnit_one : IsUnit (A : Matrix (Fin r) (Fin r) K).det),
    Matrix.one_mul] at hm
  refine Subtype.ext ?_
  ext i j
  simpa [evenMat, one_apply] using congrFun (congrFun hm (.inl i)) (.inl j)

theorem eq_one_of_hypProj_lHom (hr : 1 ≤ r) {A : SpecialLinearGroup (Fin r) K}
    (hA : A ∈ LinearFlag.unitriangular r K) (h1 : hypProj h r 0 (lHom h r (slHom h r A)) = 1) :
    A = 1 := by
  refine eq_one_of_hypProj_nElt_mul_lHom hr (isHerm_zero h) hA ?_
  rw [nElt_zero, map_one, one_mul, h1]

section Swap

variable [CharP K 2]

variable (h) in
@[expose] def offH (i j : Fin r) (a : K) : Matrix (Fin r) (Fin r) K :=
  single i j a + single j i (h.bar a)

theorem isHerm_offH (i j : Fin r) (a : K) : IsHerm h (offH h i j a) := by
  have e : ((offH h i j a).map h.bar)ᵀ = offH h i j a := by
    rw [offH, Matrix.map_add _ (map_add h.bar), map_single, map_single, transpose_add,
      transpose_single, transpose_single, h.bar_bar, add_comm]
  unfold IsHerm
  rw [e]
  ext x y
  exact CharTwo.add_self_eq_zero _

variable (h) in
theorem one_mem_traceZero' : (1 : K) ∈ h.traceZero := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
  exact CharTwo.add_self_eq_zero 1

variable (h) in
@[expose] def swapElt (j : Fin r) : hypSU h r 0 :=
  weylElt h (one_mem_traceZero' h) one_ne_zero (UnitarySixFieldTwo.swapSet_mem_hypWeyl {j})

theorem coe_swapElt (j : Fin r) :
    (((swapElt h j : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      signedPerm (weylPerm (swapSet ({j} : Finset (Fin r)))) fun _ => 1 := by
  rw [swapElt, coe_weylElt, weylMat, UnitarySixFieldTwo.weylCoeff_one]

theorem barInvT_one_add_single {i j : Fin r} (hij : i ≠ j) (a : K) :
    barInvT h (1 + single i j a) = 1 + single j i (h.bar a) := by
  refine (eq_barInvT_of_mul_eq_one ?_).symm
  have e1 : ((1 + single i j a).map h.bar)ᵀ = 1 + single j i (h.bar a) := by
    rw [Matrix.map_add _ (map_add h.bar), Matrix.map_one _ (map_zero _) (map_one _),
      transpose_add, transpose_one, map_single, transpose_single]
  have hX : single j i (h.bar a) * single j i (h.bar a) = (0 : Matrix (Fin r) (Fin r) K) := by
    simp [hij]
  rw [e1, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hX, add_zero, add_assoc,
    show single j i (h.bar a) + single j i (h.bar a) = (0 : Matrix (Fin r) (Fin r) K) from by
      ext x y
      exact CharTwo.add_self_eq_zero _, add_zero]

theorem evenMat_one_add_single {i j : Fin r} (hij : i ≠ j) (a : K) :
    evenMat h (1 + single i j a) 0 = 1 + single (Sum.inl i : HypIndex r 0) (.inl j) a +
      single (Sum.inr (.inr j) : HypIndex r 0) (.inr (.inr i)) (h.bar a) := by
  rw [evenMat, barInvT_one_add_single hij, Matrix.mul_zero]
  ext x y
  rcases x with k | l | k <;> rcases y with m | n | m
  all_goals try exact isEmptyElim ‹Fin 0›
  all_goals simp [blk3, single_apply, one_apply]

omit [CharP K 2] in
theorem evenMat_offH (i j : Fin r) (a : K) :
    evenMat h 1 (offH h i j a) = 1 + single (Sum.inl i : HypIndex r 0) (.inr (.inr j)) a +
      single (Sum.inl j : HypIndex r 0) (.inr (.inr i)) (h.bar a) := by
  rw [evenMat, barInvT_one, Matrix.one_mul, offH]
  ext x y
  rcases x with k | l | k <;> rcases y with m | n | m
  all_goals try exact isEmptyElim ‹Fin 0›
  all_goals simp [blk3, single_apply, one_apply]

theorem swapElt_mul_evenMat {i j : Fin r} (hij : i ≠ j) (a : K) :
    (((swapElt h j : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) * evenMat h (1 + single i j a) 0 =
      evenMat h 1 (offH h i j a) * (((swapElt h j : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) := by
  rw [coe_swapElt, evenMat_one_add_single hij, UnitarySixFieldTwo.signedPerm_mul_one_add_single,
    evenMat_offH]
  simp [UnitarySixFieldTwo.swapSet_inl, UnitarySixFieldTwo.swapSet_inr, lineCoord, hij]

theorem swapElt_mul_lHom {i j : Fin r} (hij : i ≠ j) {A : SpecialLinearGroup (Fin r) K} {a : K}
    (hA : (A : Matrix (Fin r) (Fin r) K) = 1 + single i j a) :
    swapElt h j * lHom h r (slHom h r A) * (swapElt h j)⁻¹ = nElt (isHerm_offH i j a) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lHom, coe_nElt]
  change _ * evenMat h (A : Matrix (Fin r) (Fin r) K) 0 = _
  rw [hA]
  exact swapElt_mul_evenMat hij a

end Swap

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover
