module

public import CFSG.LargeExtraspecial.SMod20AutPluck
public import CFSG.LargeExtraspecial.SMod20AutSemi
import all CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module

@[expose] def IsTIPlane (U : Submodule F4 W) : Prop :=
  finrank F4 U = 3 ∧ ∀ x ∈ U, ∀ y ∈ U, hermStd x y = 0

@[expose] def planeSub (i : ℕ) : Submodule F4 W := Submodule.span F4 (Set.range (planeVec i))

theorem planeVec_mem (i : ℕ) (a : Fin 3) : planeVec i a ∈ planeSub i :=
  Submodule.subset_span ⟨a, rfl⟩

theorem mem_planeSub_iff (i : ℕ) (x : W) :
    x ∈ planeSub i ↔ ∃ c : Fin 3 → F4, ∑ a, c a • planeVec i a = x :=
  Submodule.mem_span_range_iff_exists_fun F4

theorem hermStd_swap' (x y : W) : hermStd y x = hermStd x y ^ 2 := hermStd_swap x y

theorem hermStd_span_eq_zero {v : Fin 3 → W} (h : ∀ a b, hermStd (v a) (v b) = 0) {x y : W}
    (hx : x ∈ Submodule.span F4 (Set.range v)) (hy : y ∈ Submodule.span F4 (Set.range v)) :
    hermStd x y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).1 hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).1 hy
  have hl : ∀ (s : Finset (Fin 3)) (f : Fin 3 → W) (z : W),
      hermStd (∑ a ∈ s, f a) z = ∑ a ∈ s, hermStd (f a) z := by
    intro s f z
    induction s using Finset.induction_on with
    | empty => simp [hermStd]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermStd_add_left, ih]
  have hr : ∀ (s : Finset (Fin 3)) (f : Fin 3 → W) (z : W),
      hermStd z (∑ a ∈ s, f a) = ∑ a ∈ s, hermStd z (f a) := by
    intro s f z
    induction s using Finset.induction_on with
    | empty => simp [hermStd]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermStd_add_right, ih]
  rw [hl]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [hr]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hermStd_smul_left, hermStd_smul_right, h, mul_zero, mul_zero]

section Cert


theorem planeVec_orth {i : ℕ} (hi : i < 891) (a b : Fin 3) :
    hermStd (planeVec i a) (planeVec i b) = 0 := by
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := modelOK_parts (chkW_parts.2 i hi)
  have e : ∀ c d : ℕ, hermC c d = 0 → hermStd (vecOfCode c) (vecOfCode d) = 0 := by
    intro c d hcd
    rw [hermC_vecOfCode] at hcd
    exact (code_eq_zero_iff _).1 hcd
  have e' : ∀ c d : ℕ, hermC c d = 0 → hermStd (vecOfCode d) (vecOfCode c) = 0 := by
    intro c d hcd
    rw [hermStd_swap', e c d hcd]
    ring
  fin_cases a <;> fin_cases b
  · exact e _ _ h11
  · exact e _ _ h12
  · exact e _ _ h13
  · exact e' _ _ h12
  · exact e _ _ h22
  · exact e _ _ h23
  · exact e' _ _ h13
  · exact e' _ _ h23
  · exact e _ _ h33

theorem hermStd_planeSub {i : ℕ} (hi : i < 891) {x y : W} (hx : x ∈ planeSub i)
    (hy : y ∈ planeSub i) : hermStd x y = 0 :=
  hermStd_span_eq_zero (planeVec_orth hi) hx hy

theorem planeVec_linearIndependent {i : ℕ} (hi : i < 891) : LinearIndependent F4 (planeVec i) := by
  obtain ⟨t, ht⟩ := exists_pluckMat_det_ne_zero (wB i)
    (modelOK_parts (chkW_parts.2 i hi)).2.2.2.2.2.2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmv : (pluckMat (planeVec i) t) *ᵥ g = 0 := by
    funext a
    have := congrFun hg (triTab t a)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [mulVec, dotProduct, pluckMat, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have := Matrix.eq_zero_of_mulVec_eq_zero ht hmv
  intro a
  exact congrFun this a

theorem finrank_planeSub {i : ℕ} (hi : i < 891) : finrank F4 (planeSub i) = 3 := by
  rw [planeSub, finrank_span_eq_card (planeVec_linearIndependent hi), Fintype.card_fin]

theorem isTIPlane_planeSub {i : ℕ} (hi : i < 891) : IsTIPlane (planeSub i) :=
  ⟨finrank_planeSub hi, fun _ hx _ hy => hermStd_planeSub hi hx hy⟩

theorem planeSub_injective {i j : ℕ} (hi : i < 891) (hj : j < 891)
    (h : planeSub i = planeSub j) : i = j :=
  eq_of_span_eq hi hj h

end Cert

@[expose] def frob4 : F4 ≃+* F4 where
  toFun x := x ^ 2
  invFun x := x ^ 2
  left_inv x := F4.sq_sq x
  right_inv x := F4.sq_sq x
  map_mul' x y := mul_pow x y 2
  map_add' x y := by
    revert x y
    decide

theorem frob4_apply (x : F4) : frob4 x = x ^ 2 := rfl

theorem frob4_frob4 (x : F4) : frob4 (frob4 x) = x := F4.sq_sq x

@[expose] def orthSub (S : Submodule F4 W) : Submodule F4 W where
  carrier := {x | ∀ s ∈ S, hermStd x s = 0}
  add_mem' {a b} ha hb s hs := by rw [hermStd_add_left, ha s hs, hb s hs, add_zero]
  zero_mem' s _ := by simp [hermStd]
  smul_mem' c x hx s hs := by rw [hermStd_smul_left, hx s hs, mul_zero]

theorem mem_orthSub {S : Submodule F4 W} {x : W} : x ∈ orthSub S ↔ ∀ s ∈ S, hermStd x s = 0 :=
  Iff.rfl

@[expose] def conjSub (S : Submodule F4 W) : Submodule F4 W where
  carrier := {v | fvec frob4 v ∈ S}
  add_mem' {a b} ha hb := by
    show fvec frob4 (a + b) ∈ S
    rw [fvec_add]
    exact S.add_mem ha hb
  zero_mem' := by
    show fvec frob4 0 ∈ S
    rw [fvec_zero]
    exact S.zero_mem
  smul_mem' c v hv := by
    show fvec frob4 (c • v) ∈ S
    rw [fvec_smul]
    exact S.smul_mem _ hv

theorem fvec_frob4_fvec_frob4 (v : W) : fvec frob4 (fvec frob4 v) = v := by
  funext i
  exact frob4_frob4 (v i)

theorem finrank_conjSub (S : Submodule F4 W) : finrank F4 (conjSub S) = finrank F4 S := by
  let j : conjSub S ≃+ S :=
    { toFun := fun v => ⟨fvec frob4 v.1, v.2⟩
      invFun := fun s => ⟨fvec frob4 s.1, by
        show fvec frob4 (fvec frob4 s.1) ∈ S
        rw [fvec_frob4_fvec_frob4]
        exact s.2⟩
      left_inv := fun v => Subtype.ext (fvec_frob4_fvec_frob4 v.1)
      right_inv := fun s => Subtype.ext (fvec_frob4_fvec_frob4 s.1)
      map_add' := fun a b => Subtype.ext (fvec_add frob4 a.1 b.1) }
  have h : Module.rank F4 (conjSub S) = Module.rank F4 S := by
    refine rank_eq_of_equiv_equiv (frob4 : F4 → F4) j frob4.bijective ?_
    intro r m
    exact Subtype.ext (fvec_smul frob4 r m.1)
  unfold Module.finrank
  rw [h]

theorem finrank_orthSub_add (S : Submodule F4 W) :
    finrank F4 (orthSub S) + finrank F4 S = 6 := by
  have hnd : (Matrix.toBilin' (1 : Matrix (Fin 6) (Fin 6) F4)).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have h := LinearMap.BilinForm.finrank_orthogonal hnd (conjSub S)
  have hort : orthSub S =
      (Matrix.toBilin' (1 : Matrix (Fin 6) (Fin 6) F4)).orthogonal (conjSub S) := by
    ext v
    rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_orthSub]
    constructor
    · intro hv m hm
      have h1 := hv _ hm
      change (Matrix.toBilin' (1 : Matrix (Fin 6) (Fin 6) F4)) m v = 0
      rw [Matrix.toBilin'_apply', Matrix.one_mulVec]
      rw [← h1]
      unfold hermStd dotProduct
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fvec_apply, frob4_apply, F4.sq_sq, mul_comm]
    · intro hv s hs
      have hm : fvec frob4 s ∈ conjSub S := by
        show fvec frob4 (fvec frob4 s) ∈ S
        rw [fvec_frob4_fvec_frob4]
        exact hs
      have h1 : (Matrix.toBilin' (1 : Matrix (Fin 6) (Fin 6) F4)) (fvec frob4 s) v = 0 :=
        hv _ hm
      rw [Matrix.toBilin'_apply', Matrix.one_mulVec] at h1
      rw [← h1]
      unfold hermStd dotProduct
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fvec_apply, frob4_apply, mul_comm]
  rw [hort, h, finrank_conjSub, Module.finrank_fin_fun]
  have : finrank F4 S ≤ 6 := by
    have := Submodule.finrank_le S
    rwa [Module.finrank_fin_fun] at this
  omega

theorem orthSub_eq_self {U : Submodule F4 W} (hU : IsTIPlane U) : orthSub U = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx s hs
    exact hU.2 x hx s hs
  · have := finrank_orthSub_add U
    rw [hU.1] at this ⊢
    omega

theorem mem_planeSub_iff_orth {i : ℕ} (hi : i < 891) (x : W) :
    x ∈ planeSub i ↔ ∀ a : Fin 3, hermStd x (planeVec i a) = 0 := by
  constructor
  · intro hx a
    exact hermStd_planeSub hi hx (planeVec_mem i a)
  · intro h
    rw [← orthSub_eq_self (isTIPlane_planeSub hi), mem_orthSub]
    intro s hs
    obtain ⟨c, rfl⟩ := (mem_planeSub_iff i s).1 hs
    have hr : ∀ (t : Finset (Fin 3)) (f : Fin 3 → W),
        hermStd x (∑ a ∈ t, f a) = ∑ a ∈ t, hermStd x (f a) := by
      intro t f
      induction t using Finset.induction_on with
      | empty => simp [hermStd]
      | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermStd_add_right, ih]
    rw [hr]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hermStd_smul_right, h, mul_zero]

theorem testBit_foldl_or (f : ℕ → ℕ) (l : List ℕ) (a n : ℕ) :
    (l.foldl (fun acc d => acc ||| 2 ^ f d) a).testBit n = true ↔
      a.testBit n = true ∨ ∃ d ∈ l, f d = n := by
  induction l generalizing a with
  | nil => simp
  | cons d l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem scaleC_eq_scaleC_codeOf (k c : ℕ) : scaleC k c = scaleC k (codeOf (vecOfCode c)) := by
  unfold scaleC
  apply List.foldl_ext
  intro acc i hi
  have hi' : i < 6 := List.mem_range.1 hi
  rw [coord_codeOf (vecOfCode c) ⟨i, hi'⟩]
  rfl

theorem scaleC_code (a : F4) (c : ℕ) : scaleC a.code.val c = codeOf (a • vecOfCode c) := by
  rw [scaleC_eq_scaleC_codeOf, scaleC_codeOf]

theorem scaleC_vecOfCode (k c : ℕ) (hk : k < 4) :
    scaleC k c = codeOf ((⟨⟨k, hk⟩⟩ : F4) • vecOfCode c) := by
  rw [scaleC_eq_scaleC_codeOf, ← scaleC_codeOf]

theorem combo_code (T : ℕ × ℕ × ℕ) {d : ℕ} (hd : d < 64) :
    scaleC (d % 4) T.1 ^^^ scaleC (d / 4 % 4) T.2.1 ^^^ scaleC (d / 16) T.2.2 =
      codeOf ((⟨⟨d % 4, by omega⟩⟩ : F4) • tripleVec T 0 +
        (⟨⟨d / 4 % 4, by omega⟩⟩ : F4) • tripleVec T 1 +
          (⟨⟨d / 16, by omega⟩⟩ : F4) • tripleVec T 2) := by
  rw [scaleC_vecOfCode _ _ (by omega), scaleC_vecOfCode _ _ (by omega),
    scaleC_vecOfCode _ _ (by omega), codeOf_add, codeOf_add]
  rfl

theorem testBit_vecMask_iff (T : ℕ × ℕ × ℕ) (x : W) :
    (vecMask T).testBit (codeOf x) = true ↔
      x ∈ Submodule.span F4 (Set.range (tripleVec T)) := by
  rw [vecMask, testBit_foldl_or, Submodule.mem_span_range_iff_exists_fun]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range]
  constructor
  · rintro ⟨d, hd, hdx⟩
    rw [combo_code T hd] at hdx
    refine ⟨![⟨⟨d % 4, by omega⟩⟩, ⟨⟨d / 4 % 4, by omega⟩⟩, ⟨⟨d / 16, by omega⟩⟩], ?_⟩
    rw [Fin.sum_univ_three]
    exact codeOf_injective hdx
  · rintro ⟨c, rfl⟩
    have h0 := code_lt (c 0)
    have h1 := code_lt (c 1)
    have h2 := code_lt (c 2)
    refine ⟨(c 0).code.val + 4 * (c 1).code.val + 16 * (c 2).code.val, by omega, ?_⟩
    have e0 : ((c 0).code.val + 4 * (c 1).code.val + 16 * (c 2).code.val) % 4 =
        (c 0).code.val := by omega
    have e1 : ((c 0).code.val + 4 * (c 1).code.val + 16 * (c 2).code.val) / 4 % 4 =
        (c 1).code.val := by omega
    have e2 : ((c 0).code.val + 4 * (c 1).code.val + 16 * (c 2).code.val) / 16 =
        (c 2).code.val := by omega
    rw [e0, e1, e2, scaleC_code, scaleC_code, scaleC_code, ← codeOf_add, ← codeOf_add,
      Fin.sum_univ_three]
    rfl

theorem testBit_wMask_iff (i : ℕ) (x : W) :
    (wMask i).testBit (codeOf x) = true ↔ x ∈ planeSub i :=
  testBit_vecMask_iff (wB i) x

end CFSG.LargeExtraspecial.SMod20.Aut
