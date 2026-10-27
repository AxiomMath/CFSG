module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicWeyl
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryFourFieldTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionHermitian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement

variable {F : Type} [Field F]

section FieldFacts

variable (h : UnitaryFieldData 2 1 F)

include h in
theorem card_eq_four : Nat.card F = 4 := by
  rw [h.card]
  norm_num

theorem map_bar (A : Matrix (Fin 3) (Fin 3) F) : A.map h.bar = A.map (· ^ 2) := by
  ext i j
  exact UnitaryFourCover.bar_apply_two h _

theorem bar_transpose (A : Matrix (Fin 3) (Fin 3) F) : (A.map h.bar)ᵀ = hconj A := by
  rw [map_bar h]
  rfl

theorem one_mem_traceZero : (1 : F) ∈ h.traceZero := by
  have := h.charP
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
  exact CharTwo.add_self_eq_zero 1

end FieldFacts

section Model

variable (h : UnitaryFieldData 2 1 F)

@[expose] def nMat (B : Matrix (Fin 3) (Fin 3) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F :=
  blk3 1 0 B 0 0 1

@[expose] noncomputable def lMat (A : Matrix (Fin 3) (Fin 3) F) :
    Matrix (HypIndex 3 0) (HypIndex 3 0) F :=
  blk3 A 0 0 0 0 (barInvT h A)

theorem barInvT_one : barInvT h (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [barInvT, Matrix.map_one _ (map_zero _) (map_one _), inv_one, transpose_one]

theorem nMat_eq_evenMat (B : Matrix (Fin 3) (Fin 3) F) : nMat B = evenMat h 1 B := by
  rw [nMat, evenMat, barInvT_one, Matrix.one_mul]

theorem lMat_eq_evenMat (A : Matrix (Fin 3) (Fin 3) F) : lMat h A = evenMat h A 0 := by
  rw [lMat, evenMat, Matrix.mul_zero]

theorem nMat_mul (B B' : Matrix (Fin 3) (Fin 3) F) : nMat B * nMat B' = nMat (B + B') := by
  rw [nMat, nMat, nMat, blk3_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero]
  rw [add_comm]

theorem det_nMat (B : Matrix (Fin 3) (Fin 3) F) : (nMat B).det = 1 := by
  rw [nMat, det_blk3]
  simp

theorem nMat_zero : nMat (0 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  all_goals try exact isEmptyElim ‹Fin 0›
  all_goals simp [nMat, one_apply]

theorem lMat_one : lMat h (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [lMat_eq_evenMat, ← nMat_eq_evenMat, nMat_zero]

theorem lMat_mul {A A' : Matrix (Fin 3) (Fin 3) F} (hA' : IsUnit A'.det) :
    lMat h A * lMat h A' = lMat h (A * A') := by
  rw [lMat_eq_evenMat, lMat_eq_evenMat, lMat_eq_evenMat, evenMat_mul hA', Matrix.mul_zero,
    Matrix.zero_mul, add_zero]

theorem lMat_mul_nMat {A : Matrix (Fin 3) (Fin 3) F} (hA : IsUnit A.det)
    (B : Matrix (Fin 3) (Fin 3) F) :
    lMat h A * nMat B = nMat (A * B * hconj A) * lMat h A := by
  rw [lMat_eq_evenMat, nMat_eq_evenMat h, nMat_eq_evenMat h,
    evenMat_mul (by rw [det_one]; exact isUnit_one), evenMat_mul hA, Matrix.mul_one,
    Matrix.one_mul, inv_one, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add,
    ← bar_transpose h]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [conjTranspose_mul_barInvT hA, Matrix.mul_one, ← Matrix.mul_assoc, nonsing_inv_mul _ hA,
    Matrix.one_mul]

theorem lMat_gram {A : Matrix (Fin 3) (Fin 3) F} (hA : IsUnit A.det) :
    ((lMat h A).map h.bar)ᵀ * hypGram 3 0 F * lMat h A = hypGram 3 0 F := by
  rw [lMat_eq_evenMat]
  exact evenMat_gram hA (by rw [Matrix.map_zero _ (map_zero _), transpose_zero, add_zero])

theorem det_lMat {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det = 1) : (lMat h A).det = 1 := by
  rw [lMat_eq_evenMat, det_evenMat (by rw [hA]; exact isUnit_one), hA, map_one, div_one]

@[expose] noncomputable def lHom : SpecialLinearGroup (Fin 3) F →* hypSU h 3 0 where
  toFun A := mkHypSU h (lMat h A) (lMat_gram h (by rw [A.2]; exact isUnit_one)) (det_lMat h A.2)
  map_one' := Subtype.ext (Units.ext (by
    rw [coe_mkHypSU]
    exact lMat_one h))
  map_mul' A A' := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_mkHypSU, coe_mkHypSU, coe_mkHypSU]
    exact (lMat_mul h (by rw [A'.2]; exact isUnit_one)).symm))

theorem coe_lHom (A : SpecialLinearGroup (Fin 3) F) :
    (((lHom h A : hypSU h 3 0) : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) =
      lMat h A :=
  rfl

variable [CharP F 2]

theorem herm_add_self {B : Matrix (Fin 3) (Fin 3) F} (hB : hconj B = B) :
    B + (B.map h.bar)ᵀ = 0 := by
  rw [bar_transpose h, hB]
  ext i j
  exact CharTwo.add_self_eq_zero _

theorem nMat_gram {B : Matrix (Fin 3) (Fin 3) F} (hB : hconj B = B) :
    ((nMat B).map h.bar)ᵀ * hypGram 3 0 F * nMat B = hypGram 3 0 F := by
  rw [nMat_eq_evenMat h]
  exact evenMat_gram (by rw [det_one]; exact isUnit_one) (herm_add_self h hB)

@[expose] noncomputable def nElt {B : Matrix (Fin 3) (Fin 3) F} (hB : hconj B = B) :
    hypSU h 3 0 :=
  mkHypSU h (nMat B) (nMat_gram h hB) (det_nMat B)

theorem coe_nElt {B : Matrix (Fin 3) (Fin 3) F} (hB : hconj B = B) :
    (((nElt h hB : hypSU h 3 0) : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) =
      nMat B :=
  rfl

end Model

section RankOne

variable (h : UnitaryFieldData 2 1 F)

include h in
theorem hconj_hermQ (u : Fin 3 → F) : hconj (hermQ u) = hermQ u := by
  ext i j
  simp only [hconj_apply, hermQ, vecMulVec_apply]
  rw [mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl, four_pow_four (card_eq_four h), mul_comm]

theorem hermQ_smul (c : F) (u : Fin 3 → F) : hermQ (c • u) = c ^ 3 • hermQ u := by
  ext i j
  simp only [hermQ, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

include h in
theorem hermQ_smul_of_ne_zero {c : F} (hc : c ≠ 0) (u : Fin 3 → F) : hermQ (c • u) = hermQ u := by
  rw [hermQ_smul, four_pow_three (card_eq_four h) hc, one_smul]

variable [CharP F 2]

theorem herm_mem_closure_hermQ {B : Matrix (Fin 3) (Fin 3) F} (hB : hconj B = B) :
    B ∈ AddSubgroup.closure (Set.range fun u : Fin 3 → F => hermQ u) := by
  refine herm_mem (fun k => ?_) (fun i j _ u => ?_) hB
  · rw [hermD_eq_hermQ]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
  · have e : hermO i j u = hermQ (Pi.single i u + Pi.single j 1) - hermQ (Pi.single i u) -
        hermQ (Pi.single j 1) := by
      rw [hermO_eq_hermH, hermQ_add]
      abel
    rw [e]
    exact sub_mem (sub_mem (AddSubgroup.subset_closure ⟨_, rfl⟩)
      (AddSubgroup.subset_closure ⟨_, rfl⟩)) (AddSubgroup.subset_closure ⟨_, rfl⟩)

theorem five_point {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    hermQ (![0, 1, 0] : Fin 3 → F) + hermQ ![0, 0, 1] + hermQ ![0, 1, 1] + hermQ ![0, 1, ω] +
      hermQ ![0, 1, ω ^ 2] = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  ext i j
  simp only [Matrix.add_apply, hermQ, vecMulVec_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination 2 * h2
  · linear_combination (ω ^ 2 - ω + 1) * hω
  · linear_combination hω
  · linear_combination (ω ^ 3 + 2) * h3 + 2 * h2

end RankOne

section Transitivity

theorem exists_SL_mulVec_pair {u v : Fin 3 → F} (huv : crossProduct u v ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = u ∧
      (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 = v := by
  obtain ⟨k, hk⟩ : ∃ k, crossProduct u v k ≠ 0 := Function.ne_iff.mp huv
  set w : Fin 3 → F := Pi.single k 1 with hw
  have hd : Matrix.det ![u, v, w] = crossProduct u v k := by
    rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation, hw,
      single_dotProduct, one_mul]
  set d := Matrix.det ![u, v, w] with hddef
  have hd0 : d ≠ 0 := hd ▸ hk
  have hdet : Matrix.det ![u, v, d⁻¹ • w] = 1 := by
    rw [← triple_product_eq_det, map_smul, dotProduct_smul, smul_eq_mul, triple_product_eq_det,
      ← hddef, inv_mul_cancel₀ hd0]
  refine ⟨⟨(Matrix.of ![u, v, d⁻¹ • w])ᵀ, by rw [det_transpose]; exact hdet⟩,
    ?_, ?_⟩
  · rw [mulVec_single_one]
    funext i
    rfl
  · rw [mulVec_single_one]
    funext i
    rfl

theorem exists_cross_ne_zero {u : Fin 3 → F} (hu : u ≠ 0) : ∃ v, crossProduct u v ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := F) (M := Fin 3 → F)
    (by simp) hu
  exact ⟨v, crossProduct_ne_zero_iff_linearIndependent.mpr hv⟩

theorem exists_SL_mulVec {u : Fin 3 → F} (hu : u ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = u := by
  obtain ⟨v, hv⟩ := exists_cross_ne_zero hu
  obtain ⟨A, hA, -⟩ := exists_SL_mulVec_pair hv
  exact ⟨A, hA⟩

theorem eq_zero_or_eq_smul_of_cross_eq_zero {u v : Fin 3 → F} (huv : crossProduct u v = 0) :
    u = 0 ∨ ∃ c : F, v = c • u := by
  by_cases hu : u = 0
  · exact Or.inl hu
  · right
    have hli : ¬LinearIndependent F ![u, v] := fun h =>
      (crossProduct_ne_zero_iff_linearIndependent.mpr h) huv
    rw [LinearIndependent.pair_iff' hu] at hli
    simp only [not_forall, not_not] at hli
    obtain ⟨c, hc⟩ := hli
    exact ⟨c, hc.symm⟩

end Transitivity

section Unitriangular

@[expose] def utMat (a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a, c; 0, 1, b; 0, 0, 1]

theorem det_utMat (a b c : F) : (utMat a b c).det = 1 := by
  simp [utMat, det_fin_three]

@[expose] def ut (a b c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨utMat a b c, det_utMat a b c⟩

theorem coe_ut (a b c : F) :
    ((ut a b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = utMat a b c :=
  rfl

theorem ut_congr {a b c a' b' c' : F} (ha : a = a') (hb : b = b') (hc : c = c') :
    ut a b c = ut a' b' c' := by
  rw [ha, hb, hc]

theorem utMat_mul (a b c a' b' c' : F) :
    utMat a b c * utMat a' b' c' = utMat (a + a') (b + b') (c + c' + a * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utMat, mul_apply, Fin.sum_univ_three] <;> ring

theorem ut_mul (a b c a' b' c' : F) :
    ut a b c * ut a' b' c' = ut (a + a') (b + b') (c + c' + a * b') :=
  Subtype.ext (utMat_mul a b c a' b' c')

theorem ut_zero : ut (0 : F) 0 0 = 1 := by
  refine Subtype.ext ?_
  change utMat (0 : F) 0 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utMat]

theorem utMat_a (a : F) : utMat a 0 0 = 1 + single 0 1 a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utMat]

theorem utMat_b (b : F) : utMat 0 b 0 = 1 + single 1 2 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utMat]

theorem utMat_c (c : F) : utMat 0 0 c = 1 + single 0 2 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utMat]

theorem mem_unitriangular_iff {A : SpecialLinearGroup (Fin 3) F} :
    A ∈ LinearFlag.unitriangular 3 F ↔ ∃ a b c : F, A = ut a b c := by
  constructor
  · rintro ⟨hlow, hdiag⟩
    refine ⟨(A : Matrix (Fin 3) (Fin 3) F) 0 1, (A : Matrix (Fin 3) (Fin 3) F) 1 2,
      (A : Matrix (Fin 3) (Fin 3) F) 0 2, Subtype.ext ?_⟩
    change (A : Matrix (Fin 3) (Fin 3) F) = utMat _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [utMat, hdiag, hlow 1 0 (by decide), hlow 2 0 (by decide), hlow 2 1 (by decide)]
  · rintro ⟨a, b, c, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [coe_ut, utMat]
    · fin_cases i <;> simp [coe_ut, utMat]

theorem ut_mem_unitriangular (a b c : F) : ut a b c ∈ LinearFlag.unitriangular 3 F :=
  mem_unitriangular_iff.mpr ⟨a, b, c, rfl⟩

variable [CharP F 2]

theorem ut_inv (a b c : F) : (ut a b c)⁻¹ = ut a b (c + a * b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [ut_mul, ← ut_zero]
  exact ut_congr (by linear_combination a * h2) (by linear_combination b * h2)
    (by linear_combination (c + a * b) * h2)

theorem ut_commutator (a b c a' b' c' : F) :
    ⁅ut a b c, ut a' b' c'⁆ = ut 0 0 (a * b' + a' * b) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [commutatorElement_def, ut_inv, ut_inv, ut_mul, ut_mul, ut_mul]
  exact ut_congr (by linear_combination (a + a') * h2) (by linear_combination (b + b') * h2)
    (by linear_combination (c + c' + a * b' + a * b + a' * b') * h2)

theorem ut_sq (a b c : F) : ut a b c ^ 2 = ut 0 0 (a * b) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [sq, ut_mul]
  exact ut_congr (by linear_combination a * h2) (by linear_combination b * h2)
    (by linear_combination c * h2)

theorem ut_eq_mul (a b c : F) : ut a b c = ut a 0 0 * ut 0 b 0 * ut 0 0 (c + a * b) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [ut_mul, ut_mul]
  exact ut_congr (by ring) (by ring) (by linear_combination (-(a * b)) * h2)

end Unitriangular

section Swaps

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem swapSet_inl (T : Finset (Fin r)) (j : Fin r) :
    swapSet T (.inl j) = if j ∈ T then .inr j else .inl j :=
  rfl

theorem swapSet_inr (T : Finset (Fin r)) (j : Fin r) :
    swapSet T (.inr j) = if j ∈ T then .inl j else .inr j :=
  rfl

theorem swapSet_mem_hypWeyl (T : Finset (Fin r)) : swapSet T ∈ hypWeyl r := by
  rw [mem_hypWeyl]
  intro x
  rcases x with j | j <;> by_cases hj : j ∈ T <;> simp [swapSet_inl, swapSet_inr, hj]

theorem weylPerm_swapSet_inl (T : Finset (Fin r)) (i : Fin r) :
    weylPerm (ε := ε) (swapSet T) (.inl i) = if i ∈ T then .inr (.inr i) else .inl i := by
  rw [weylPerm_inl, swapSet_inl]
  split_ifs <;> rfl

theorem weylPerm_swapSet_inr_inr (T : Finset (Fin r)) (i : Fin r) :
    weylPerm (ε := ε) (swapSet T) (.inr (.inr i)) = if i ∈ T then .inl i else .inr (.inr i) := by
  rw [weylPerm_inr_inr, swapSet_inr]
  split_ifs <;> rfl

theorem weylCoeff_one (h : UnitaryFieldData p f K) (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    weylCoeff (ε := ε) h 1 w = fun _ => 1 := by
  funext a
  rcases a with i | k | i
  · simp only [weylCoeff]
    cases w (.inl i) <;> rfl
  · rfl
  · simp only [weylCoeff]
    cases w (.inl i) <;> simp

theorem signedPerm_mul_one_add_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (a b a' b' : ι) (c c' : F) :
    signedPerm σ (fun _ => (1 : F)) * (1 + single a b c + single a' b' c') =
      (1 + single (σ a) (σ b) c + single (σ a') (σ b') c') * signedPerm σ (fun _ => 1) := by
  simp only [Matrix.mul_add, Matrix.add_mul, signedPerm_mul_single, single_mul_signedPerm,
    Equiv.symm_apply_apply, one_mul, mul_one]

variable (h : UnitaryFieldData 2 1 F)

@[expose] noncomputable def swapElt (T : Finset (Fin 3)) : hypSU h 3 0 :=
  weylElt h (one_mem_traceZero h) one_ne_zero (swapSet_mem_hypWeyl T)

theorem coe_swapElt (T : Finset (Fin 3)) :
    (((swapElt h T : hypSU h 3 0) : GL (HypIndex 3 0) F) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) F) = signedPerm (weylPerm (swapSet T)) fun _ => 1 := by
  rw [swapElt, coe_weylElt, weylMat, weylCoeff_one]

variable [CharP F 2]

theorem barInvT_one_add_single {i j : Fin 3} (hij : i ≠ j) (a : F) :
    barInvT h (1 + single i j a) = 1 + single j i (a ^ 2) := by
  refine (eq_barInvT_of_mul_eq_one ?_).symm
  have h1 : hconj (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hconj, Matrix.map_one _ (by simp) (by simp), transpose_one]
  have hX : single j i (a ^ 2) * single j i (a ^ 2) = (0 : Matrix (Fin 3) (Fin 3) F) := by
    simp [hij]
  rw [bar_transpose h, hconj_add, hconj_single, h1, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_add, Matrix.mul_one, hX, add_zero, add_assoc,
    show single j i (a ^ 2) + single j i (a ^ 2) = (0 : Matrix (Fin 3) (Fin 3) F) from by
      ext x y
      exact CharTwo.add_self_eq_zero _, add_zero]

theorem lMat_one_add_single {i j : Fin 3} (hij : i ≠ j) (a : F) :
    lMat h (1 + single i j a) = 1 + single (Sum.inl i : HypIndex 3 0) (.inl j) a +
      single (Sum.inr (.inr j) : HypIndex 3 0) (.inr (.inr i)) (a ^ 2) := by
  rw [lMat, barInvT_one_add_single h hij]
  ext x y
  rcases x with k | l | k <;> rcases y with m | n | m
  all_goals try exact isEmptyElim ‹Fin 0›
  all_goals simp [single_apply, one_apply]

omit [CharP F 2] in
theorem nMat_hermO (i j : Fin 3) (a : F) :
    nMat (hermO i j a) = 1 + single (Sum.inl i : HypIndex 3 0) (.inr (.inr j)) a +
      single (Sum.inl j : HypIndex 3 0) (.inr (.inr i)) (a ^ 2) := by
  rw [nMat, hermO]
  ext x y
  rcases x with k | l | k <;> rcases y with m | n | m
  all_goals try exact isEmptyElim ‹Fin 0›
  all_goals simp [single_apply, one_apply]

theorem swap_mul_lMat_a (a : F) :
    (((swapElt h {1, 2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) * lMat h (utMat a 0 0) =
      nMat (hermO 0 1 a) * (((swapElt h {1, 2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) := by
  rw [coe_swapElt, utMat_a, lMat_one_add_single h (by decide), signedPerm_mul_one_add_single,
    nMat_hermO]
  simp [swapSet_inl, swapSet_inr, lineCoord]

theorem swap_mul_lMat_c (c : F) :
    (((swapElt h {1, 2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) * lMat h (utMat 0 0 c) =
      nMat (hermO 0 2 c) * (((swapElt h {1, 2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) := by
  rw [coe_swapElt, utMat_c, lMat_one_add_single h (by decide), signedPerm_mul_one_add_single,
    nMat_hermO]
  simp [swapSet_inl, swapSet_inr, lineCoord]

theorem swap'_mul_lMat_b (b : F) :
    (((swapElt h {2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) * lMat h (utMat 0 b 0) =
      nMat (hermO 1 2 b) * (((swapElt h {2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) := by
  rw [coe_swapElt, utMat_b, lMat_one_add_single h (by decide), signedPerm_mul_one_add_single,
    nMat_hermO]
  simp [swapSet_inl, swapSet_inr, lineCoord]

theorem swap'_mul_lMat_c (c : F) :
    (((swapElt h {2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) * lMat h (utMat 0 0 c) =
      nMat (hermO 0 2 c) * (((swapElt h {2} : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) := by
  rw [coe_swapElt, utMat_c, lMat_one_add_single h (by decide), signedPerm_mul_one_add_single,
    nMat_hermO]
  simp [swapSet_inl, swapSet_inr, lineCoord]

end Swaps

section UnitriangularS

variable (h : UnitaryFieldData 2 1 F) [CharP F 2]

theorem exists_lMat_mul_nMat_of_mem {g : hypSU h 3 0} (hg : g ∈ hypUnitriangular h 3 0) :
    ∃ A ∈ LinearFlag.unitriangular 3 F, ∃ B : Matrix (Fin 3) (Fin 3) F, hconj B = B ∧
      ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) =
        lMat h A * nMat B := by
  obtain ⟨A, C, hA, hC, hgAC⟩ := (exists_mem_hypUnitriangular_even_iff (h := h) _).mp ⟨g, hg, rfl⟩
  refine ⟨⟨A, hA.det_eq_one⟩, ⟨fun i j hij => hA.1 hij, hA.2⟩, C, ?_, ?_⟩
  · rw [← bar_transpose h, eq_neg_of_add_eq_zero_right hC]
    ext x y
    exact CharTwo.neg_eq _
  · rw [hgAC, lMat_eq_evenMat, nMat_eq_evenMat h, evenMat_mul (by rw [det_one]; exact isUnit_one),
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem eq_one_of_hypProj_lHom_mul_nElt {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ LinearFlag.unitriangular 3 F) {B : Matrix (Fin 3) (Fin 3) F} (hB : hconj B = B)
    (h1 : hypProj h 3 0 (lHom h A * nElt h hB) = 1) : A = 1 ∧ B = 0 := by
  rw [← MonoidHom.mem_ker, ker_hypProj] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  have hmat := congrArg Units.val hc
  rw [Subgroup.coe_mul, Units.val_mul, coe_lHom, coe_nElt, lMat_eq_evenMat, nMat_eq_evenMat h,
    evenMat_mul (by rw [det_one]; exact isUnit_one), Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, GeneralLinearGroup.coe_scalar] at hmat
  have hc1 : (c : F) = 1 := by
    have := congrFun (congrFun hmat (.inl 0)) (.inl 0)
    rw [evenMat, blk3_inl_inl, scalar_apply, diagonal_apply_eq, hA.2 0] at this
    exact this.symm
  rw [hc1, map_one, ← nMat_zero, nMat_eq_evenMat h] at hmat
  obtain ⟨hA1, hB0⟩ := evenMat_inj (by rw [A.2]; exact isUnit_one) hmat
  exact ⟨Subtype.ext hA1, hB0⟩

end UnitriangularS

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo
