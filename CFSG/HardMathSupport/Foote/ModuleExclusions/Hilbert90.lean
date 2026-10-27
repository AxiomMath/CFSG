module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def Ai (σ : F ≃+* F) (A : Matrix ι ι F) : ℕ → Matrix ι ι F
  | 0 => 1
  | n + 1 => A * (Ai σ A n).map σ

@[expose] def sv (σ : F ≃+* F) (i : ℕ) (w : ι → F) : ι → F := fun j => (σ ^ i) (w j)

@[expose] def tr (σ : F ≃+* F) (A : Matrix ι ι F) (r : ℕ) (w : ι → F) : ι → F :=
  ∑ i ∈ Finset.range r, (Ai σ A i).mulVec (sv σ i w)

@[expose] def σv (σ : F ≃+* F) : (ι → F) →+ (ι → F) :=
  AddMonoidHom.mk' (fun u j => σ (u j)) (by intro a b; ext j; simp)

theorem σv_apply (σ : F ≃+* F) (u : ι → F) (j : ι) : σv σ u j = σ (u j) := rfl

theorem sv_zero (σ : F ≃+* F) (w : ι → F) : sv σ 0 w = w := by
  ext j; simp [sv]

theorem sv_succ (σ : F ≃+* F) (i : ℕ) (w : ι → F) :
    sv σ (i + 1) w = σv σ (sv σ i w) := by
  ext j
  simp only [sv, pow_succ', σv_apply]
  rfl

theorem sv_smul (σ : F ≃+* F) (i : ℕ) (a : F) (w : ι → F) :
    sv σ i (a • w) = (σ ^ i) a • sv σ i w := by
  ext j; simp [sv]

theorem σv_mulVec (σ : F ≃+* F) (M : Matrix ι ι F) (u : ι → F) :
    σv σ (M.mulVec u) = (M.map σ).mulVec (σv σ u) := by
  ext j
  exact RingHom.map_mulVec σ.toRingHom M u j

theorem mulVec_tr_fixed (σ : F ≃+* F) (A : Matrix ι ι F) (r : ℕ)
    (hσ : σ ^ r = 1) (hA : Ai σ A r = 1) (w : ι → F) :
    A.mulVec (σv σ (tr σ A r w)) = tr σ A r w := by
  have hstep : ∀ i : ℕ, A.mulVec (σv σ ((Ai σ A i).mulVec (sv σ i w))) =
      (Ai σ A (i + 1)).mulVec (sv σ (i + 1) w) := by
    intro i
    rw [σv_mulVec, Matrix.mulVec_mulVec, ← sv_succ, Ai]
  have hsum : A.mulVec (σv σ (tr σ A r w)) =
      ∑ i ∈ Finset.range r, (Ai σ A (i + 1)).mulVec (sv σ (i + 1) w) := by
    simp only [tr]
    rw [map_sum, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl (fun i _ => hstep i)
  rw [hsum]
  set f : ℕ → (ι → F) := fun i => (Ai σ A i).mulVec (sv σ i w) with hf
  have hfr : f r = f 0 := by
    simp only [hf, hA, Ai, sv_zero, Matrix.one_mulVec]
    ext j
    simp [sv, hσ]
  have h1 := Finset.sum_range_succ' f r
  have h2 := Finset.sum_range_succ f r
  have : ∑ i ∈ Finset.range r, f (i + 1) = ∑ i ∈ Finset.range r, f i := by
    have := h1.symm.trans h2
    rw [hfr] at this
    exact add_right_cancel this
  simpa [tr, hf] using this

theorem tr_smul (σ : F ≃+* F) (A : Matrix ι ι F) (r : ℕ) (a : F) (w : ι → F) :
    tr σ A r (a • w) = ∑ i ∈ Finset.range r, (σ ^ i) a • (Ai σ A i).mulVec (sv σ i w) := by
  simp only [tr, sv_smul, Matrix.mulVec_smul]

theorem sigma_pow_linearIndependent (σ : F ≃+* F) (r : ℕ) (hr : orderOf σ = r) :
    LinearIndependent F (fun i : Fin r => ((fun u : Fˣ => (σ ^ (i : ℕ)) (u : F)) : Fˣ → F)) := by
  have h := linearIndependent_monoidHom Fˣ F
  let φ : Fin r → (Fˣ →* F) := fun i => (σ ^ (i : ℕ)).toMonoidHom.comp (Units.coeHom F)
  have hφ : Function.Injective φ := by
    intro i j hij
    have h1 : ∀ u : Fˣ, (σ ^ (i : ℕ)) (u : F) = (σ ^ (j : ℕ)) (u : F) := by
      intro u
      exact DFunLike.congr_fun hij u
    have h2 : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
      ext x
      by_cases hx : x = 0
      · subst hx; simp
      · exact h1 (Units.mk0 x hx)
    have := pow_injOn_Iio_orderOf (x := σ) (by rw [hr]; exact i.2) (by rw [hr]; exact j.2) h2
    exact Fin.ext this
  exact h.comp φ hφ

theorem span_tr (σ : F ≃+* F) (A : Matrix ι ι F) (r : ℕ) (hr : orderOf σ = r)
    (hr0 : 0 < r) : Submodule.span F (Set.range (tr σ A r)) = ⊤ := by
  by_contra hne
  have hlt : Submodule.span F (Set.range (tr σ A r)) < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨ℓ, hℓ0, hℓ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  apply hℓ0
  have hvan : ∀ w, ℓ (tr σ A r w) = 0 := fun w => hℓ (Submodule.subset_span ⟨w, rfl⟩)
  refine LinearMap.ext fun w => ?_
  have hli := sigma_pow_linearIndependent σ r hr
  have key := Fintype.linearIndependent_iff.mp hli
    (fun i : Fin r => ℓ ((Ai σ A (i : ℕ)).mulVec (sv σ (i : ℕ) w))) (by
      funext u
      have h1 := hvan ((u : F) • w)
      rw [tr_smul, map_sum] at h1
      simp only [map_smul, smul_eq_mul] at h1
      rw [Finset.sum_range (fun i => (σ ^ i) (u : F) * ℓ ((Ai σ A i).mulVec (sv σ i w)))] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h1]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)) ⟨0, hr0⟩
  simpa [Ai, sv_zero] using key

theorem speiser (σ : F ≃+* F) (A : Matrix ι ι F) (r : ℕ) (hr : orderOf σ = r)
    (hr0 : 0 < r) (hA : Ai σ A r = 1) :
    ∃ B : Matrix ι ι F, B.det ≠ 0 ∧ A * B.map σ = B := by
  have hσ : σ ^ r = 1 := by rw [← hr]; exact pow_orderOf_eq_one σ
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent F (Set.range (tr σ A r))
  have hbtop : Submodule.span F b = ⊤ := by rw [hbspan]; exact span_tr σ A r hr hr0
  let bB : Module.Basis b F (ι → F) :=
    Module.Basis.mk (v := fun x : b => (x : ι → F)) hbli
      (by rw [Subtype.range_coe]; exact hbtop.ge)
  let e : b ≃ ι := bB.indexEquiv (Pi.basisFun F ι)
  have hcol : ∀ j : ι, ∃ w, tr σ A r w = ((e.symm j : b) : ι → F) := fun j => hbS (e.symm j).2
  choose w hw using hcol
  refine ⟨Matrix.of fun i j => ((e.symm j : b) : ι → F) i, ?_, ?_⟩
  · have hli : LinearIndependent F (fun j : ι => ((e.symm j : b) : ι → F)) := by
      have h := bB.linearIndependent.comp e.symm e.symm.injective
      convert h using 1
      funext j
      simp [bB]
    have : IsUnit (Matrix.of fun i j => ((e.symm j : b) : ι → F) i) := by
      rw [← Matrix.linearIndependent_cols_iff_isUnit]
      exact hli
    exact (Matrix.isUnit_iff_isUnit_det _).1 this |>.ne_zero
  · ext i j
    have h1 := congrFun (mulVec_tr_fixed σ A r hσ hA (w j)) i
    rw [hw j] at h1
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, σv_apply] using h1

instance instFiniteRingEquivFoote [Finite F] : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) fun _ _ h => RingEquiv.ext (congrFun h)

theorem pow_succ_apply (σ : F ≃+* F) (n : ℕ) (x : F) : (σ ^ (n + 1)) x = σ ((σ ^ n) x) := by
  rw [pow_succ']; rfl

theorem Ai_succ_right (σ : F ≃+* F) (A : Matrix ι ι F) (n : ℕ) :
    Ai σ A (n + 1) = Ai σ A n * A.map (σ ^ n) := by
  induction n with
  | zero => simp [Ai]
  | succ n ih =>
    have hmap : ∀ M N : Matrix ι ι F, (M * N).map σ = M.map σ * N.map σ :=
      fun M N => Matrix.map_mul (f := σ.toRingHom)
    have e3 : ∀ M : Matrix ι ι F, (M.map (σ ^ n)).map σ = M.map (σ ^ (n + 1)) := by
      intro M
      ext i j
      simp only [Matrix.map_apply]
      rw [pow_succ_apply]
    calc Ai σ A (n + 1 + 1) = A * (Ai σ A (n + 1)).map σ := rfl
      _ = A * (Ai σ A n * A.map (σ ^ n)).map σ := by rw [ih]
      _ = A * ((Ai σ A n).map σ * (A.map (σ ^ n)).map σ) := by rw [hmap]
      _ = (A * (Ai σ A n).map σ) * (A.map (σ ^ n)).map σ := by rw [Matrix.mul_assoc]
      _ = Ai σ A (n + 1) * A.map (σ ^ (n + 1)) := by rw [e3]; rfl

theorem Ai_smul (σ : F ≃+* F) (A : Matrix ι ι F) (l : F) (n : ℕ) :
    Ai σ (l • A) n = (∏ i ∈ Finset.range n, (σ ^ i) l) • Ai σ A n := by
  induction n with
  | zero => simp [Ai]
  | succ n ih =>
    have e1 : Ai σ (l • A) (n + 1) = (l • A) * (Ai σ (l • A) n).map σ := rfl
    have e2 : Ai σ A (n + 1) = A * (Ai σ A n).map σ := rfl
    rw [e1, ih, e2]
    have hP : (∏ i ∈ Finset.range (n + 1), (σ ^ i) l) =
        l * σ (∏ i ∈ Finset.range n, (σ ^ i) l) := by
      rw [Finset.prod_range_succ', map_prod, mul_comm]
      congr 1
      · exact Finset.prod_congr rfl (fun i _ => pow_succ_apply σ i l)
    rw [hP]
    ext i j
    simp [Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem det_Ai_ne_zero (σ : F ≃+* F) (A : Matrix ι ι F) (hA : A.det ≠ 0) (n : ℕ) :
    (Ai σ A n).det ≠ 0 := by
  induction n with
  | zero => simp [Ai]
  | succ n ih =>
    have e2 : Ai σ A (n + 1) = A * (Ai σ A n).map σ := rfl
    rw [e2, Matrix.det_mul]
    refine mul_ne_zero hA ?_
    have : ((Ai σ A n).map σ).det = σ ((Ai σ A n).det) := by
      have := RingHom.map_det σ.toRingHom (Ai σ A n)
      exact this.symm
    rw [this]
    exact fun h => ih ((map_eq_zero_iff σ σ.injective).1 h)

theorem prod_pow_eq_norm [Finite F] (σ : F ≃+* F) (x : F) :
    ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) x =
      algebraMap (FixedPoints.subfield (Subgroup.zpowers σ) F) F
        (Algebra.norm (FixedPoints.subfield (Subgroup.zpowers σ) F) x) := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  let e1 : Fin (orderOf σ) ≃ (Subgroup.zpowers σ) := finEquivZPowers hfin
  let e2 : (Subgroup.zpowers σ) ≃ (F →ₐ[FixedPoints.subfield (Subgroup.zpowers σ) F] F) :=
    FixedPoints.toAlgHomEquiv (Subgroup.zpowers σ) F
  let e3 : (F →ₐ[FixedPoints.subfield (Subgroup.zpowers σ) F] F) ≃
      (F ≃ₐ[FixedPoints.subfield (Subgroup.zpowers σ) F] F) :=
    { toFun := fun φ => AlgEquiv.ofBijective φ (AlgHom.bijective φ)
      invFun := fun τ => τ.toAlgHom
      left_inv := fun φ => by ext; rfl
      right_inv := fun τ => by ext; rfl }
  rw [Finset.prod_range]
  refine Fintype.prod_equiv ((e1.trans e2).trans e3) _ _ ?_
  intro i
  show (σ ^ (i : ℕ)) x = (e3 (e2 (e1 i))) x
  have h1 : (e1 i : Subgroup.zpowers σ) =
      ⟨σ ^ (i : ℕ), Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _⟩ := by
    apply Subtype.ext
    simp [e1, finEquivZPowers_apply]
  rw [h1]
  rfl

theorem mem_fixedPoints_subfield_of_apply_eq (σ : F ≃+* F) (x : F) (h : σ x = x) :
    x ∈ FixedPoints.subfield (Subgroup.zpowers σ) F := by
  intro a
  have hmem : σ ∈ (MulAction.stabilizer (F ≃+* F) x) := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have := (Subgroup.zpowers_le.mpr hmem) a.2
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

theorem exists_prod_pow_eq [Finite F] (σ : F ≃+* F) (c : F) (hc : σ c = c) (hc0 : c ≠ 0) :
    ∃ l : F, l ≠ 0 ∧ ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) l = c := by
  have hmem := mem_fixedPoints_subfield_of_apply_eq σ c hc
  obtain ⟨l, hl⟩ := FiniteField.norm_surjective (FixedPoints.subfield (Subgroup.zpowers σ) F) F
    (⟨c, hmem⟩ : FixedPoints.subfield (Subgroup.zpowers σ) F)
  have hprod : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) l = c := by
    rw [prod_pow_eq_norm, hl]
    rfl
  refine ⟨l, ?_, hprod⟩
  rintro rfl
  have hr : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (0 : F) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hr) (by simp)
  rw [this] at hprod
  exact hc0 hprod.symm

theorem hilbert90_matrix [Finite F] [Nonempty ι] (σ : F ≃+* F) (A : Matrix ι ι F) (hA : A.det ≠ 0)
    (c : F) (hc : Ai σ A (orderOf σ) = c • (1 : Matrix ι ι F)) :
    ∃ (l : F) (B : Matrix ι ι F), l ≠ 0 ∧ B.det ≠ 0 ∧ (l • A) * B.map σ = B := by
  set r := orderOf σ with hr
  have hr0 : 0 < r := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have hσr : σ ^ r = 1 := by rw [hr]; exact pow_orderOf_eq_one σ
  have hc0 : c ≠ 0 := by
    intro h0
    have := det_Ai_ne_zero σ A hA r
    rw [hc, h0] at this
    simp at this
  have hσc : σ c = c := by
    have h1 : Ai σ A (r + 1) = σ c • A := by
      have : Ai σ A (r + 1) = A * (Ai σ A r).map σ := rfl
      rw [this, hc]
      ext i j
      simp [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        apply_ite σ, mul_ite, mul_comm]
    have h2 : Ai σ A (r + 1) = c • A := by
      rw [Ai_succ_right, hc, hσr]
      ext i j
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    rw [h1] at h2
    by_contra hne
    have hdiff : σ c - c ≠ 0 := sub_ne_zero.mpr hne
    have hA' : A = 0 := by
      ext i j
      have := congrFun (congrFun h2 i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      have h3 : (σ c - c) * A i j = 0 := by linear_combination this
      simpa [hdiff] using h3
    rw [hA'] at hA
    simp at hA
  obtain ⟨l, hl0, hl⟩ := exists_prod_pow_eq σ c⁻¹ (by rw [map_inv₀, hσc]) (inv_ne_zero hc0)
  have hAl : Ai σ (l • A) r = 1 := by
    rw [Ai_smul, hl, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨B, hB, hAB⟩ := speiser σ (l • A) r rfl hr0 hAl
  exact ⟨l, B, hl0, hB, hAB⟩

end CFSG.HardMathSupport.Foote.ModuleExclusions
