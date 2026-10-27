module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aDual

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section Irred

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

noncomputable instance : Finite (upperUni F) := Finite.of_equiv _ (upperUniEquiv F)

theorem mixed_hline (hF : Fintype.card F = 2 ^ f) (a b : Fin f → Bool) :
    ∃ n ∈ fixedSub (matRep (tensorRep (F := F) k a b)) (lowerUni F),
      ∀ w ∈ fixedSub (matRep (tensorRep (F := F) k a b)) (lowerUni F), ∃ c : k, w = c • n := by
  obtain ⟨P, Q, h⟩ := (⟨_, _, tensorRep_dual_iso (F := F) k a b⟩ :
    ∃ (P : Matrix (TIdx f b a) (TIdx f a b) k) (Q : Matrix (TIdx f a b) (TIdx f b a) k),
      MatIso (dualMat (tensorRep (F := F) k a b)) (tensorRep k b a) P Q)
  refine hline_of_cocyclic (tensorRep (F := F) k a b) (lowerUni F) (Q.mulVec (hw k b a)) ?_
  exact h.span_orbit_top (lowerUni F) (hw k b a) (mixed_span k hF b a)

theorem tensorRep_fixed_irreducible (hF : Fintype.card F = 2 ^ f) (a b : Fin f → Bool) :
    fixedSub (matRep (tensorRep (F := F) k a b)) (upperUni F) = Submodule.span k {hw k a b} ∧
      (matRep (tensorRep (F := F) k a b)).IsIrreducible := by
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hPp : IsPGroup 2 (upperUni F) := isPGroup_upperUni hcard
  refine fixedSub_eq_span_and_irreducible k Nat.prime_two (matRep (tensorRep (F := F) k a b))
    (lowerUni F) (upperUni F) hPp (wJ : SL(3, F)) (fun u hu => wJ_conj_lowerUni hu)
    (hw k a b) (hw_ne_zero k a b) ?_ (mixed_span k hF a b) (mixed_hline k hF a b)
  intro h hh
  obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hh
  exact tensorRep_up3_fixed k a b x y z

omit [CharP F 2] [Fintype F] [CharP k 2] in
theorem card_TIdx_eq (a b : Fin f → Bool) :
    Fintype.card (TIdx f a b) = 3 ^ cntS a b * 8 ^ cntH a b := by
  rw [card_TIdx]
  have h : ∀ i, locDim (a i) (b i) =
      3 ^ (if a i ≠ b i then 1 else 0) * 8 ^ (if a i = true ∧ b i = true then 1 else 0) := by
    intro i
    cases a i <;> cases b i <;> simp [locDim]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, cntS, cntH,
    Finset.card_filter, Finset.card_filter]

omit [CharP F 2] [Fintype F] in
theorem tensorRepGen_dT_hw {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → Bool × Bool)
    (e : ι → ℕ) (r t : Fˣ) :
    (tensorRepGen (F := F) k τ e (dT r t)).mulVec (hwVec k τ) =
      (∏ i, frK k (e i) (locChar (τ i).1 (τ i).2 r t)) • hwVec k τ := by
  funext x'
  rw [hwVec, Matrix.mulVec_single_one, Matrix.col_apply, tensorRepGen_apply]
  have h1 : ∀ i, locRep k (τ i).1 (τ i).2 (e i) (dT r t) (x' i) (locDist (τ i).1 (τ i).2) =
      if x' i = locDist (τ i).1 (τ i).2 then frK k (e i) (locChar (τ i).1 (τ i).2 r t) else 0 :=
    fun i => locRep_dT_col k _ _ _ _ _ _
  rw [Finset.prod_congr rfl (fun i _ => h1 i)]
  by_cases h : x' = fun i => locDist (τ i).1 (τ i).2
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x' i ≠ locDist (τ i).1 (τ i).2 := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [h]

omit [CharP F 2] [Fintype F] in
theorem prod_frK_locChar (a b : Fin f → Bool) (r t : Fˣ) :
    ∏ i : Fin f, frK k (i : ℕ) (locChar (a i) (b i) r t) =
      algebraMap F k (r : F) ^ (mBits a + mBits b) * algebraMap F k (t : F) ^ mBits b := by
  have h : ∀ i : Fin f, frK k (i : ℕ) (locChar (a i) (b i) r t) =
      algebraMap F k (r : F) ^ (if a i then 2 ^ (i : ℕ) else 0) *
        (algebraMap F k (r : F) ^ (if b i then 2 ^ (i : ℕ) else 0) *
          algebraMap F k (t : F) ^ (if b i then 2 ^ (i : ℕ) else 0)) := by
    intro i
    cases a i <;> cases b i <;> simp [locChar, frK_apply, map_mul, Units.val_mul]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add, mBits, mBits]
  ring

omit [CharP F 2] [Fintype F] in
theorem tensorRep_dT_hw (a b : Fin f → Bool) (r t : Fˣ) :
    (tensorRep (F := F) k a b (dT r t)).mulVec (hw k a b) =
      (algebraMap F k (r : F) ^ (mBits a + mBits b) * algebraMap F k (t : F) ^ mBits b) •
        hw k a b := by
  rw [← prod_frK_locChar k a b r t]
  exact tensorRepGen_dT_hw k (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ)) r t

end Irred

end CFSG.QuasithinUnique.Setup.X7a
