module

public import CFSG.LargeExtraspecial.O62Code

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Code

@[expose] noncomputable def qModel (minus : Bool) : QuadraticForm (ZMod 2) V₀ :=
  if minus then qMinus else qPlus

theorem qModel_false : qModel false = qPlus := rfl

theorem qModel_true : qModel true = qMinus := rfl

theorem polar_qModel (minus : Bool) (x y : V₀) : polar (qModel minus) x y = polar qPlus x y := by
  cases minus
  · rfl
  · exact (polar_qPlus_eq_polar_qMinus x y).symm

theorem qModel_nondegenerate (minus : Bool) : (qModel minus).polarBilin.Nondegenerate := by
  cases minus
  · exact qPlus_nondegenerate
  · exact qMinus_nondegenerate

noncomputable abbrev O₀ (minus : Bool) : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  TauCeti.QuadraticMap.orthogonalGroup (qModel minus)

noncomputable abbrev Ω₀ (minus : Bool) : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  omegaGroup (qModel minus) (qModel_nondegenerate minus)

@[expose] def qB (minus : Bool) (n : ℕ) : Bool :=
  (n.testBit 0 && n.testBit 1) ^^ (n.testBit 2 && n.testBit 3) ^^ (n.testBit 4 && n.testBit 5) ^^
    (minus && (n.testBit 4 ^^ n.testBit 5))

private theorem qB_aux : ∀ minus b₀ b₁ b₂ b₃ b₄ b₅ : Bool,
    (if b₀ then (1 : ZMod 2) else 0) * (if b₁ then 1 else 0) +
        (if b₂ then 1 else 0) * (if b₃ then 1 else 0) +
        (if b₄ then 1 else 0) * (if b₅ then 1 else 0) +
        (if minus then (if b₄ then 1 else 0) * (if b₄ then 1 else 0) +
          (if b₅ then 1 else 0) * (if b₅ then 1 else 0) else 0) =
      if (b₀ && b₁) ^^ (b₂ && b₃) ^^ (b₄ && b₅) ^^ (minus && (b₄ ^^ b₅)) then 1 else 0 := by
  decide

theorem vec_apply_zero (n : ℕ) : vec n 0 = bitZ n 0 := rfl
theorem vec_apply_one (n : ℕ) : vec n 1 = bitZ n 1 := rfl
theorem vec_apply_two (n : ℕ) : vec n 2 = bitZ n 2 := rfl
theorem vec_apply_three (n : ℕ) : vec n 3 = bitZ n 3 := rfl
theorem vec_apply_four (n : ℕ) : vec n 4 = bitZ n 4 := rfl
theorem vec_apply_five (n : ℕ) : vec n 5 = bitZ n 5 := rfl

theorem qModel_vec (minus : Bool) (n : ℕ) :
    qModel minus (vec n) = if qB minus n then 1 else 0 := by
  rw [qB, ← qB_aux minus (n.testBit 0) (n.testBit 1) (n.testBit 2) (n.testBit 3) (n.testBit 4)
    (n.testBit 5)]
  cases minus
  · simp only [qModel, Bool.false_eq_true, ↓reduceIte, qPlus_apply, add_zero, vec_apply_zero,
      vec_apply_one, vec_apply_two, vec_apply_three, vec_apply_four, vec_apply_five, bitZ]
  · simp only [qModel, ↓reduceIte, qMinus_apply, vec_apply_zero, vec_apply_one, vec_apply_two,
      vec_apply_three, vec_apply_four, vec_apply_five, bitZ]
    ring

theorem qModel_vec_eq_one {minus : Bool} {n : ℕ} (h : qB minus n = true) :
    qModel minus (vec n) = 1 := by
  rw [qModel_vec, h, ite_eq_left rfl]

noncomputable def reflLin (v : V₀) : V₀ →ₗ[ZMod 2] V₀ :=
  LinearMap.id + ((polarBilin qPlus).flip v).smulRight v

theorem reflLin_apply (v x : V₀) : reflLin v x = x + polar qPlus x v • v := by
  simp [reflLin, polarBilin_apply_apply]

theorem reflLin_involutive (v : V₀) : Function.Involutive (reflLin v) := by
  intro x
  have hvv : polar qPlus v v = 0 := CFSG.Fischer.Classification.Arf.polar_self_zmod2 qPlus v
  rw [reflLin_apply, reflLin_apply, polar_add_left, polar_smul_left, hvv, smul_eq_mul, mul_zero,
    add_zero, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

noncomputable def refl (v : V₀) : V₀ ≃ₗ[ZMod 2] V₀ :=
  LinearEquiv.ofInvolutive (reflLin v) (reflLin_involutive v)

theorem refl_apply (v x : V₀) : refl v x = x + polar qPlus x v • v :=
  reflLin_apply v x

theorem refl_mul_self (v : V₀) : refl v * refl v = 1 :=
  LinearEquiv.ext fun x => reflLin_involutive v x

theorem refl_mem_orthogonalGroup {minus : Bool} {v : V₀} (hv : qModel minus v = 1) :
    refl v ∈ TauCeti.QuadraticMap.orthogonalGroup (qModel minus) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [refl_apply, QuadraticMap.map_add (qModel minus), QuadraticMap.map_smul (qModel minus),
    hv, polar_smul_right, polar_qModel, smul_eq_mul, smul_eq_mul, mul_one]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (polar qPlus x v * polar qPlus x v) * h2

theorem finrank_commSpace_refl {v : V₀} (hv : v ≠ 0) :
    finrank (ZMod 2) (commSpace (refl v)) = 1 := by
  have hle : commSpace (refl v) ≤ Submodule.span (ZMod 2) {v} := by
    intro y hy
    obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
    rw [refl_apply, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hne : commSpace (refl v) ≠ ⊥ := by
    obtain ⟨x, hx⟩ : ∃ x, polar qPlus x v ≠ 0 := by
      by_contra! h
      exact hv (polar_qPlus_nondeg v fun y => by rw [polar_comm]; exact h y)
    have hx1 : polar qPlus x v = 1 := (zmod2_eq_zero_or_eq_one _).resolve_left hx
    intro hbot
    have hmem := sub_mem_commSpace (refl v) x
    rw [hbot, Submodule.mem_bot, refl_apply, add_sub_cancel_left, hx1, one_smul] at hmem
    exact hv hmem
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_singleton hv] at h1
  have h2 : finrank (ZMod 2) (commSpace (refl v)) ≠ 0 :=
    fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  omega

noncomputable def wordProd (w : List ℕ) : V₀ ≃ₗ[ZMod 2] V₀ := (w.map fun n => refl (vec n)).prod

@[simp] theorem wordProd_nil : wordProd [] = 1 := by simp [wordProd]

theorem wordProd_cons (n : ℕ) (w : List ℕ) : wordProd (n :: w) = refl (vec n) * wordProd w := by
  simp [wordProd]

theorem wordProd_append (a b : List ℕ) : wordProd (a ++ b) = wordProd a * wordProd b := by
  simp [wordProd]

theorem wordProd_inv (w : List ℕ) : (wordProd w)⁻¹ = wordProd w.reverse := by
  induction w with
  | nil => simp
  | cons n w ih =>
    rw [wordProd_cons, mul_inv_rev, ih, List.reverse_cons, wordProd_append, wordProd_cons,
      wordProd_nil, mul_one, inv_eq_of_mul_eq_one_right (refl_mul_self _)]

theorem wordProd_mem_orthogonalGroup {minus : Bool} {w : List ℕ}
    (hw : ∀ n ∈ w, qB minus n = true) :
    wordProd w ∈ TauCeti.QuadraticMap.orthogonalGroup (qModel minus) := by
  induction w with
  | nil => exact one_mem _
  | cons n w ih =>
    rw [wordProd_cons]
    exact mul_mem (refl_mem_orthogonalGroup (qModel_vec_eq_one (hw n (by simp))))
      (ih fun m hm => hw m (by simp [hm]))

theorem vec_ne_zero {minus : Bool} {n : ℕ} (h : qB minus n = true) : vec n ≠ 0 := by
  intro h0
  have := qModel_vec_eq_one h
  rw [h0, QuadraticMap.map_zero] at this
  exact zero_ne_one this

theorem natCast_finrank_commSpace_wordProd {minus : Bool} {w : List ℕ}
    (hw : ∀ n ∈ w, qB minus n = true) :
    (finrank (ZMod 2) (commSpace (wordProd w)) : ZMod 2) = w.length := by
  induction w with
  | nil =>
    rw [wordProd_nil, natCast_finrank_commSpace_one, List.length_nil, Nat.cast_zero]
  | cons n w ih =>
    have hn := hw n (by simp)
    have hw' : ∀ m ∈ w, qB minus m = true := fun m hm => hw m (by simp [hm])
    rw [wordProd_cons, natCast_finrank_commSpace_mul (qModel_nondegenerate minus)
      (refl_mem_orthogonalGroup (qModel_vec_eq_one hn)) (wordProd_mem_orthogonalGroup hw'),
      finrank_commSpace_refl (vec_ne_zero hn), ih hw', List.length_cons, Nat.cast_add,
      Nat.cast_one, add_comm]

theorem wordProd_mem_omegaGroup_iff {minus : Bool} {w : List ℕ}
    (hw : ∀ n ∈ w, qB minus n = true) :
    wordProd w ∈ omegaGroup (qModel minus) (qModel_nondegenerate minus) ↔ Even w.length := by
  rw [mem_omegaGroup, ← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even,
    natCast_finrank_commSpace_wordProd hw]
  exact and_iff_right (wordProd_mem_orthogonalGroup hw)

@[expose] def reflCol (n j : ℕ) : ℕ := 2 ^ j ^^^ (if n.testBit (j ^^^ 1) then n &&& 63 else 0)

@[expose] def reflC (n : ℕ) : ℕ :=
  pack (reflCol n 0) (reflCol n 1) (reflCol n 2) (reflCol n 3) (reflCol n 4) (reflCol n 5)

@[expose] def wordC (w : List ℕ) : ℕ := w.foldr (fun n acc => mul (reflC n) acc) one

theorem reflCol_lt (n : ℕ) {j : ℕ} (hj : j < 6) : reflCol n j < 64 := by
  unfold reflCol
  refine Nat.xor_lt_two_pow (n := 6) (Nat.pow_lt_pow_right (by norm_num) hj) ?_
  split
  · exact Nat.and_lt_two_pow _ (by norm_num)
  · norm_num

theorem bitZ_reflCol (n j : ℕ) {i : ℕ} (hi : i < 6) :
    bitZ (reflCol n j) i = (if j = i then 1 else 0) + bitZ n (j ^^^ 1) * bitZ n i := by
  unfold reflCol
  rw [bitZ_xor]
  congr 1
  · unfold bitZ
    rw [Nat.testBit_two_pow]
    by_cases h : j = i <;> simp [h]
  · unfold bitZ
    by_cases hb : n.testBit (j ^^^ 1)
    · rw [ite_eq_left hb, Nat.testBit_and, show (63 : ℕ) = 2 ^ 6 - 1 from rfl,
        Nat.testBit_two_pow_sub_one]
      simp [hb, hi]
    · simp [hb]

theorem polar_single_vec (j : Fin 6) (n : ℕ) :
    polar qPlus (Pi.single j 1) (vec n) = bitZ n ((j : ℕ) ^^^ 1) := by
  fin_cases j <;> simp [polar_qPlus, vec]

theorem hasCode_refl (n : ℕ) : HasCode (refl (vec n) : V₀ →ₗ[ZMod 2] V₀) (reflC n) := by
  unfold HasCode
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, refl_apply, polar_single_vec, mat,
    Matrix.of_apply]
  have hcol : bitZ (reflC n) (6 * j + i) = bitZ (reflCol n j) i := by
    unfold bitZ reflC
    rw [testBit_pack (reflCol_lt n (by norm_num)) (reflCol_lt n (by norm_num))
      (reflCol_lt n (by norm_num)) (reflCol_lt n (by norm_num)) (reflCol_lt n (by norm_num)) j
      i.isLt]
    fin_cases j <;> rfl
  rw [hcol, bitZ_reflCol n j i.isLt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  congr 1
  simp only [Fin.val_eq_val, eq_comm]

theorem wordC_cons (n : ℕ) (w : List ℕ) : wordC (n :: w) = mul (reflC n) (wordC w) := rfl

theorem wordC_lt (w : List ℕ) : wordC w < 2 ^ 36 := by
  cases w with
  | nil => exact one_lt
  | cons n w => exact mul_lt _ _

theorem hasCode_wordProd (w : List ℕ) :
    HasCode (wordProd w : V₀ →ₗ[ZMod 2] V₀) (wordC w) := by
  induction w with
  | nil => exact hasCode_one
  | cons n w ih =>
    rw [wordProd_cons, wordC_cons]
    exact (hasCode_refl n).mul ih

theorem eq_iff_of_hasCode {g h : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ} (hg : HasCode g a)
    (hh : HasCode h b) (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) : g = h ↔ a = b := by
  constructor
  · rintro rfl
    exact hg.code_eq hh ha hb
  · rintro rfl
    exact hg.eq_of_equiv hh

theorem wordProd_eq_iff (a b : List ℕ) : wordProd a = wordProd b ↔ wordC a = wordC b :=
  eq_iff_of_hasCode (hasCode_wordProd a) (hasCode_wordProd b) (wordC_lt a) (wordC_lt b)

end CFSG.LargeExtraspecial.O62
