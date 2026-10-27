module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutI

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem aI_eq {a : K} (ha : a ≠ 0) :
    aI a = fromBlocks (sA a) 0 0 !![0, -1; -a, 0] := by
  simp only [aI, bA, bAinv, kron, fromBlocks_multiply, sA, dA, dAinv]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [ha]

theorem ωJ_similitude {μ : K} {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : Aᵀ * formJ 2 K * A = μ • formJ 2 K) (x y : Fin 2 ⊕ Fin 2 → K) :
    ωJ K (A *ᵥ x) (A *ᵥ y) = μ * ωJ K x y := by
  rw [ωJ_apply, ωJ_apply, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hA,
    Matrix.vecMul_smul, smul_dotProduct, smul_eq_mul, ← Matrix.dotProduct_mulVec]

theorem aI_col_inl0 {a : K} (ha : a ≠ 0) :
    (fun s => aI a s (Sum.inl 0)) = Pi.single (Sum.inl 1) 1 := by
  rw [aI_eq ha]
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp [sA]

theorem aI_col_inl1 {a : K} (ha : a ≠ 0) :
    (fun s => aI a s (Sum.inl 1)) = Pi.single (Sum.inl 0) a := by
  rw [aI_eq ha]
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp [sA]

theorem aI_col_inr0 {a : K} (ha : a ≠ 0) :
    (fun s => aI a s (Sum.inr 0)) = Pi.single (Sum.inr 1) (-a) := by
  rw [aI_eq ha]
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp

theorem aI_col_inr1 {a : K} (ha : a ≠ 0) :
    (fun s => aI a s (Sum.inr 1)) = Pi.single (Sum.inr 0) (-1) := by
  rw [aI_eq ha]
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp

theorem exists_frame_typeI [Finite K] (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0)
    {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : Aᵀ * formJ 2 K * A = (-a) • formJ 2 K) (hAA : A * A = a • 1) :
    ∃ g : StatedSp 2 K,
      A * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * aI a := by
  have hAA' : ∀ v, A *ᵥ (A *ᵥ v) = a • v := fun v => by
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hsim := ωJ_similitude hA
  have hanti : ∀ x y, ωJ K (A *ᵥ x) y = -ωJ K x (A *ᵥ y) := by
    intro x y
    have hy : y = A *ᵥ (a⁻¹ • A *ᵥ y) := by rw [mulVec_smul, hAA', smul_smul, inv_mul_cancel₀ ha,
      one_smul]
    conv_lhs => rw [hy]
    rw [hsim, map_smul, smul_eq_mul]
    field_simp
  have hbsymm : ∀ x y, ωJ K y (A *ᵥ x) = ωJ K x (A *ᵥ y) := by
    intro x y
    rw [ωJ_comm, hanti, neg_neg]
  have hQ0 : ∃ x, ωJ K x (A *ᵥ x) ≠ 0 := by
    by_contra h
    push Not at h
    have hpol : ∀ x y, ωJ K x (A *ᵥ y) = 0 := by
      intro x y
      have h1 := h (x + y)
      rw [mulVec_add] at h1
      simp only [map_add, LinearMap.add_apply] at h1
      rw [h x, h y, hbsymm x y] at h1
      exact (mul_eq_zero.mp (by linear_combination h1 :
        (2 : K) * ωJ K x (A *ᵥ y) = 0)).resolve_left h2
    have he : (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) = 0 := by
      apply ωJ_nondeg
      intro y
      have := hpol (Pi.single (Sum.inl 0) 1) (a⁻¹ • A *ᵥ y)
      rwa [mulVec_smul, hAA', smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    have := congrFun he (Sum.inl 0)
    simp at this
  have hnorm : ∀ c : K, ∃ s t : K, s ^ 2 - a * t ^ 2 = c := by
    intro c
    have : Fintype K := Fintype.ofFinite K
    have hodd : Fintype.card K % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (Fintype.card K) with h | h
      · exfalso
        have hc := FiniteField.even_card_iff_char_two.mpr h
        apply h2
        have := (ringChar.spec K 2).mpr (by rw [hc])
        exact_mod_cast this
      · exact h
    obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic (R := K)
      (f := Polynomial.X ^ 2) (g := Polynomial.C (-a) * Polynomial.X ^ 2 - Polynomial.C c)
      (Polynomial.degree_X_pow 2) (by
        rw [Polynomial.degree_sub_C (by
          rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr ha)]; norm_num),
          Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr ha)]
        norm_num) hodd
    refine ⟨s, t, ?_⟩
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_mul] at hst
    linear_combination hst
  have hscale : ∀ (x : Fin 2 ⊕ Fin 2 → K) (s t : K),
      ωJ K (s • x + t • A *ᵥ x) (A *ᵥ (s • x + t • A *ᵥ x)) =
        (s ^ 2 - a * t ^ 2) * ωJ K x (A *ᵥ x) := by
    intro x s t
    have e1 : ωJ K (A *ᵥ x) (A *ᵥ x) = 0 := ωJ_self _
    have e2 : ωJ K (A *ᵥ x) x = -ωJ K x (A *ᵥ x) := ωJ_comm _ _
    have e3 : ωJ K x x = 0 := ωJ_self _
    rw [mulVec_add, mulVec_smul, mulVec_smul, hAA']
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2,
      e3]
    ring
  obtain ⟨x₀, hx₀⟩ := hQ0
  obtain ⟨s₀, t₀, hst₀⟩ := hnorm (ωJ K x₀ (A *ᵥ x₀))⁻¹
  set x := s₀ • x₀ + t₀ • A *ᵥ x₀ with hxdef
  have hQx : ωJ K x (A *ᵥ x) = 1 := by rw [hxdef, hscale, hst₀, inv_mul_cancel₀ hx₀]
  let InW : (Fin 2 ⊕ Fin 2 → K) → Prop := fun w => ωJ K w x = 0 ∧ ωJ K w (A *ᵥ x) = 0
  have hWadd : ∀ w z, InW w → InW z → InW (w + z) := fun w z hw hz => by
    simp only [InW, map_add, LinearMap.add_apply, hw.1, hz.1, hw.2, hz.2, add_zero, and_self]
  have hWA : ∀ w, InW w → InW (A *ᵥ w) := fun w hw => by
    refine ⟨?_, ?_⟩
    · rw [hanti, hw.2, neg_zero]
    · rw [hsim, hw.1, mul_zero]
  obtain ⟨w₀, hw₀, hw₀ne⟩ : ∃ w ∈ LinearMap.ker (((ωJ K).flip x).prod ((ωJ K).flip (A *ᵥ x))),
      w ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  have hInW₀ : InW w₀ := by
    have := LinearMap.mem_ker.mp hw₀
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hQW : ∃ y : Fin 2 ⊕ Fin 2 → K, InW y ∧ ωJ K y (A *ᵥ y) ≠ 0 := by
    by_contra h
    push Not at h
    have hpol : ∀ w z, InW w → InW z → ωJ K w (A *ᵥ z) = 0 := by
      intro w z hw hz
      have h1 := h (w + z) (hWadd w z hw hz)
      rw [mulVec_add] at h1
      simp only [map_add, LinearMap.add_apply] at h1
      rw [h w hw, h z hz, hbsymm w z] at h1
      exact (mul_eq_zero.mp (by linear_combination h1 :
        (2 : K) * ωJ K w (A *ᵥ z) = 0)).resolve_left h2
    apply hw₀ne
    apply ωJ_nondeg
    intro v
    set α := ωJ K v (A *ᵥ x)
    set β := -ωJ K v x
    set w' := v - α • x - β • A *ᵥ x with hw'
    have hxx : ωJ K x x = 0 := ωJ_self _
    have hAxx : ωJ K (A *ᵥ x) x = -1 := by rw [ωJ_comm, hQx]
    have hAxAx : ωJ K (A *ᵥ x) (A *ᵥ x) = 0 := ωJ_self _
    have hInW' : InW w' := by
      refine ⟨?_, ?_⟩
      · simp only [hw', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          hxx, hAxx, β]
        ring
      · simp only [hw', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          hQx, hAxAx, α]
        ring
    have hv : v = α • x + β • A *ᵥ x + w' := by rw [hw']; abel
    have hww' : ωJ K w₀ w' = 0 := by
      have hz : InW (a⁻¹ • A *ᵥ w') := by
        have := hWA w' hInW'
        exact ⟨by rw [map_smul, LinearMap.smul_apply, this.1, smul_zero],
          by rw [map_smul, LinearMap.smul_apply, this.2, smul_zero]⟩
      have h3 := hpol w₀ _ hInW₀ hz
      rwa [mulVec_smul, hAA', smul_smul, inv_mul_cancel₀ ha, one_smul] at h3
    rw [hv, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hInW₀.1, hInW₀.2,
      hww']
    ring
  obtain ⟨y, hyW, hy⟩ := hQW
  set c := ωJ K y (A *ᵥ y) with hc
  obtain ⟨s, t, hst⟩ := hnorm (-c)
  set e := s • x + t • A *ᵥ x + y with hedef
  set f := c⁻¹ • A *ᵥ y - (2 * c)⁻¹ • A *ᵥ e with hfdef
  have hxy : ωJ K x y = 0 := by rw [ωJ_comm, hyW.1, neg_zero]
  have hAxy : ωJ K (A *ᵥ x) y = 0 := by rw [ωJ_comm, hyW.2, neg_zero]
  have hxAy : ωJ K x (A *ᵥ y) = 0 := by rw [← hbsymm, hyW.2]
  have hAxAy : ωJ K (A *ᵥ x) (A *ᵥ y) = 0 := by rw [hsim, hxy, mul_zero]
  have hyy : ωJ K y y = 0 := ωJ_self _
  have hey : ωJ K e y = 0 := by
    simp only [hedef, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxy, hAxy, hyy]
    ring
  have heAy : ωJ K e (A *ᵥ y) = c := by
    simp only [hedef, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxAy, hAxAy]
    ring
  have hQe : ωJ K e (A *ᵥ e) = 0 := by
    have hAe : A *ᵥ e = s • A *ᵥ x + (t * a) • x + A *ᵥ y := by
      rw [hedef, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hAA', smul_smul]
    have hxx : ωJ K x x = 0 := ωJ_self _
    have hAxx : ωJ K (A *ᵥ x) x = -1 := by rw [ωJ_comm, hQx]
    have hAxAx : ωJ K (A *ᵥ x) (A *ᵥ x) = 0 := ωJ_self _
    rw [hAe]
    simp only [hedef, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxx, hAxx, hAxAx, hQx, hxAy, hAxAy, hyW.1, hyW.2, ← hc]
    linear_combination hst
  have hef : ωJ K e f = 1 := by
    simp only [hfdef, map_sub, map_smul, smul_eq_mul, heAy, hQe]
    field_simp
    ring
  have heAf : ωJ K e (A *ᵥ f) = 0 := by
    simp only [hfdef, mulVec_sub, mulVec_smul, hAA', map_sub, map_smul, smul_eq_mul, hey,
      ωJ_self]
    ring
  have hQf : ωJ K f (A *ᵥ f) = 0 := by
    have hAyy : ωJ K (A *ᵥ y) y = -c := by rw [ωJ_comm, hc]
    have hAye : ωJ K (A *ᵥ y) e = -c := by rw [ωJ_comm, heAy]
    have hAey : ωJ K (A *ᵥ e) y = -c := by rw [hanti, heAy]
    have hAee : ωJ K (A *ᵥ e) e = 0 := by rw [ωJ_comm, hQe, neg_zero]
    simp only [hfdef, mulVec_sub, mulVec_smul, hAA', map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hAyy, hAye, hAey, hAee]
    field_simp
    ring
  let E : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![e, A *ᵥ e]
  let F : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![f, (-a)⁻¹ • A *ᵥ f]
  have hAe_e : ωJ K (A *ᵥ e) e = 0 := by rw [ωJ_comm, hQe, neg_zero]
  have hAfF : ωJ K (A *ᵥ f) f = 0 := by rw [ωJ_comm, hQf, neg_zero]
  have hAe_f : ωJ K (A *ᵥ e) f = 0 := by rw [hanti, heAf, neg_zero]
  have hAeAf : ωJ K (A *ᵥ e) (A *ᵥ f) = -a := by rw [hsim, hef, mul_one]
  have hsymp : (frameMat E F)ᵀ * formJ 2 K * frameMat E F = formJ 2 K := by
    refine frameMat_symplectic ?_ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [E, F, ωJ_self, hQe, hAe_e, hQf, hAfF, heAf, hAe_f, hAeAf, hef, ha]
  refine ⟨toSp (frameMat E F) hsymp, ?_⟩
  rw [coe_toSp]
  have hcomm := mul_eq_of_mulVec_col (N := A) (A := frameMat E F) (N' := aI a)
  apply hcomm
  intro k
  have hcol : ∀ k, (fun r => frameMat E F r k) = Sum.elim E F k := fun k => rfl
  rcases k with (k | k) <;> fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    rw [hcol]
  · rw [aI_col_inl0 ha, mulVec_frameMat_single]
    simp [E]
  · rw [aI_col_inl1 ha, mulVec_frameMat_single]
    simp [E, hAA']
  · rw [aI_col_inr0 ha, mulVec_frameMat_single]
    simp only [F, Sum.elim_inr, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, smul_smul]
    rw [show -a * (-a)⁻¹ = 1 from by field_simp, one_smul]
  · rw [aI_col_inr1 ha, mulVec_frameMat_single]
    simp only [F, Sum.elim_inr, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      mulVec_smul, hAA', smul_smul]
    rw [show (-a)⁻¹ * a = -1 from by field_simp, neg_one_smul]

end CFSG.ComponentClassification.CatFactsSp4
