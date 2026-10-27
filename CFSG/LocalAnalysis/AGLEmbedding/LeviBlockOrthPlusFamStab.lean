module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamAct

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem sl_mulVec_ne_zero (A : SL(2, K)) {p : Fin 2 → K} (hp : p ≠ 0) :
    (A : Matrix (Fin 2) (Fin 2) K) *ᵥ p ≠ 0 := by
  intro h
  apply hp
  have h2 : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p) = p := by
    rw [mulVec_mulVec]
    simp [adjugate_mul, A.2]
  rw [← h2, h, mulVec_zero]

theorem eq_one_of_forall_par (B : SL(2, K))
    (h : ∀ p : Fin 2 → K, p ≠ 0 → ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ p) 0 * p 1 =
      ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ p) 1 * p 0) : B = 1 := by
  have h10 := h ![1, 0] (fun h => by simpa using congrFun h 0)
  have h01 := h ![0, 1] (fun h => by simpa using congrFun h 1)
  have h11 := h ![1, 1] (fun h => by simpa using congrFun h 0)
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add] at h10 h01 h11
  have hdet := B.2
  rw [Matrix.det_fin_two] at hdet
  have hb10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := h10.symm
  have hb01 : (B : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := h01
  have hb : (B : Matrix (Fin 2) (Fin 2) K) 0 0 = B 1 1 := by
    rw [hb01, hb10] at h11
    simpa using h11
  rw [hb10, hb01, mul_zero, sub_zero, hb] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hone : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have : ((B : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ^ 2 = 0 := by
      linear_combination hdet - ((B : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [hb] using hone
  · simpa using hb01
  · simpa using hb10
  · simpa using hone

omit [CharP K 2] in
theorem par_of_plusFamTwo_eq {u v : Fin 2 → K} (h : plusFamTwo u = plusFamTwo v) :
    u 0 * v 1 = u 1 * v 0 := by
  have hu : (Sum.elim u 0 : Fin 2 ⊕ Fin 2 → K) ∈ plusFamTwo u :=
    ⟨by simp [mul_comm], by simp⟩
  rw [h] at hu
  exact hu.1

theorem eq_of_forall_plusFamTwo_eq {A B : SL(2, K)}
    (h : ∀ p : Fin 2 → K, p ≠ 0 → plusFamTwo ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p) =
      plusFamTwo ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ p)) : A = B := by
  have hC : A⁻¹ * B = 1 := by
    refine eq_one_of_forall_par _ fun p hp => ?_
    have h1 : plusIotaTwo K A⁻¹ • plusFamTwo ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p) =
        plusIotaTwo K A⁻¹ • plusFamTwo ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ p) := by
      rw [h p hp]
    have hA : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
        1 := by simp [adjugate_mul, A.2]
    have hAB : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) =
        ((A⁻¹ * B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by simp
    rw [plusIotaTwo_smul_plusFamTwo _ (sl_mulVec_ne_zero A hp),
      plusIotaTwo_smul_plusFamTwo _ (sl_mulVec_ne_zero B hp), mulVec_mulVec, mulVec_mulVec] at h1
    simp only [hA, hAB, one_mulVec] at h1
    exact par_of_plusFamTwo_eq h1.symm
  exact inv_mul_eq_one.mp hC

variable (K) in
@[expose] def plusFamTwoStab : Subgroup ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) where
  carrier := {h | ∃ A : SL(2, K), ∀ p : Fin 2 → K, p ≠ 0 →
    h • plusFamTwo p = plusFamTwo ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p)}
  mul_mem' := by
    rintro a b ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, fun p hp => ?_⟩
    have hAB : ((A * B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) := by simp
    rw [mul_smul, hB p hp, hA _ (sl_mulVec_ne_zero B hp), mulVec_mulVec]
    simp only [hAB]
  one_mem' := ⟨1, fun p _ => by simp⟩
  inv_mem' := by
    rintro a ⟨A, hA⟩
    refine ⟨A⁻¹, fun p hp => ?_⟩
    have h1 := hA _ (sl_mulVec_ne_zero A⁻¹ hp)
    have hAA : (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        1 := by simp [mul_adjugate, A.2]
    rw [mulVec_mulVec] at h1
    simp only [hAA, one_mulVec] at h1
    rw [← h1, smul_smul, inv_mul_cancel, one_smul]

omit [CharP K 2] in
theorem mem_plusFamTwoStab {h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)} :
    h ∈ plusFamTwoStab K ↔ ∃ A : SL(2, K), ∀ p : Fin 2 → K, p ≠ 0 →
      h • plusFamTwo p = plusFamTwo ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p) :=
  Iff.rfl

variable (K) in
@[expose] noncomputable def plusFamTwoHom : ↥(plusFamTwoStab K) →* SL(2, K) where
  toFun h := Classical.choose (mem_plusFamTwoStab.1 h.2)
  map_one' := eq_of_forall_plusFamTwo_eq fun p hp => by
    rw [← Classical.choose_spec (mem_plusFamTwoStab.1 (1 : ↥(plusFamTwoStab K)).2) p hp]
    simp
  map_mul' g h := by
    refine eq_of_forall_plusFamTwo_eq fun p hp => ?_
    rw [← Classical.choose_spec (mem_plusFamTwoStab.1 (g * h).2) p hp, Subgroup.coe_mul,
      mul_smul, Classical.choose_spec (mem_plusFamTwoStab.1 h.2) p hp,
      Classical.choose_spec (mem_plusFamTwoStab.1 g.2) _ (sl_mulVec_ne_zero _ hp),
      mulVec_mulVec]
    simp

theorem plusFamTwoHom_spec (h : ↥(plusFamTwoStab K)) {p : Fin 2 → K} (hp : p ≠ 0) :
    (h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) • plusFamTwo p =
      plusFamTwo (((plusFamTwoHom K h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ p) :=
  Classical.choose_spec (mem_plusFamTwoStab.1 h.2) p hp

theorem plusFamTwoHom_eq (h : ↥(plusFamTwoStab K)) {A : SL(2, K)}
    (hA : ∀ p : Fin 2 → K, p ≠ 0 → (h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) •
      plusFamTwo p = plusFamTwo ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p)) :
    plusFamTwoHom K h = A :=
  eq_of_forall_plusFamTwo_eq fun p hp => by rw [← plusFamTwoHom_spec h hp, hA p hp]

variable (K) in
@[expose] noncomputable def plusIotaOne :
    SL(2, K) →* ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
  (MulAut.conj (swapPair K (1 : Fin 2))).toMonoidHom.comp (plusIotaTwo K)

omit [CharP K 2] in
theorem plusIotaOne_apply (A : SL(2, K)) :
    plusIotaOne K A = swapPair K (1 : Fin 2) * plusIotaTwo K A * swapPair K 1 := by
  have h : (swapPair K (1 : Fin 2))⁻¹ = swapPair K 1 :=
    inv_eq_of_mul_eq_one_right (swapPair_mul_self 1)
  change swapPair K 1 * plusIotaTwo K A * (swapPair K 1)⁻¹ = _
  rw [h]

theorem plusIotaOne_smul_plusFamTwo (A : SL(2, K)) (p : Fin 2 → K) :
    plusIotaOne K A • plusFamTwo p = plusFamTwo p := by
  rw [plusIotaOne_apply, mul_smul, mul_smul, swapPair_smul_plusFamTwo,
    plusIotaTwo_smul_plusFamOne, swapPair_smul_plusFamOne]

theorem plusIotaOne_smul_plusFamOne (A : SL(2, K)) {p : Fin 2 → K} (hp : p ≠ 0) :
    plusIotaOne K A • plusFamOne p = plusFamOne ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p) := by
  rw [plusIotaOne_apply, mul_smul, mul_smul, swapPair_smul_plusFamOne,
    plusIotaTwo_smul_plusFamTwo A hp, swapPair_smul_plusFamTwo]

omit [CharP K 2] in
theorem plusIotaOne_mem_orthogonalGroup (A : SL(2, K)) :
    plusIotaOne K A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) := by
  rw [plusIotaOne_apply]
  exact mul_mem (mul_mem (swapIso K 1).2 (plusIotaTwo_mem_orthogonalGroup A)) (swapIso K 1).2

theorem plusIotaOne_mem_plusFamTwoStab (A : SL(2, K)) : plusIotaOne K A ∈ plusFamTwoStab K :=
  ⟨1, fun p _ => by rw [plusIotaOne_smul_plusFamTwo]; simp⟩

theorem mem_plusFamTwoStab_of_stab [Finite K]
    (g : ↥(MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (flag 2 K 2)))
    (hgO : (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)) :
    (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) ∈ plusFamTwoStab K := by
  set M := ((plusXBlock g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M.det ≠ 0 := (plusXBlock g).isUnit.map Matrix.detMonoidHom |>.ne_zero
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) M.det
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hdet hc
  have hAdet : (c⁻¹ • M).det = 1 := by
    rw [det_smul, Fintype.card_fin, hc, inv_pow, pow_two, inv_mul_cancel₀ (mul_ne_zero hc0 hc0)]
  refine ⟨⟨c⁻¹ • M, hAdet⟩, fun p hp => ?_⟩
  rw [smul_plusFamTwo_of_stab g hgO hp]
  change plusFamTwo (M *ᵥ p) = plusFamTwo ((c⁻¹ • M) *ᵥ p)
  rw [smul_mulVec, plusFamTwo_smul (inv_ne_zero hc0)]

omit [CharP K 2] in
theorem exists_sl_mulVec_one_zero_eq {q : Fin 2 → K} (hq : q ≠ 0) :
    ∃ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (![1, 0] : Fin 2 → K) = q := by
  by_cases h0 : q 0 = 0
  · have h1 : q 1 ≠ 0 := fun h1 => hq (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, -(q 1)⁻¹; q 1, 0], by simp [det_fin_two_of, h1]⟩, funext fun i => ?_⟩
    fin_cases i <;> simp [mulVec, dotProduct, h0]
  · refine ⟨⟨!![q 0, 0; q 1, (q 0)⁻¹], by simp [det_fin_two_of, h0]⟩, funext fun i => ?_⟩
    fin_cases i <;> simp [mulVec, dotProduct]

theorem mem_plusFamTwoStab_of_stab_star [Finite K]
    {h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K))
    (hX : h • plusFamTwo (![1, 0] : Fin 2 → K) = plusFamTwo ![1, 0]) :
    h ∈ plusFamTwoStab K := by
  set σ := swapPair K (1 : Fin 2) with hσ
  have hσσ : σ * σ = 1 := swapPair_mul_self 1
  have hσO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) := (swapIso K 1).2
  have e1 : σ • plusFamTwo (![1, 0] : Fin 2 → K) = flag 2 K 2 := by
    rw [swapPair_smul_plusFamTwo, flag_two_eq_plusFamOne]
  have hX' : (σ * h * σ) • flag 2 K 2 = flag 2 K 2 := by
    rw [← e1, smul_smul, mul_assoc (σ * h), hσσ, mul_one, mul_smul]
    exact congrArg (σ • ·) hX
  set g' : ↥(MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))
    (flag 2 K 2)) := ⟨σ * h * σ, MulAction.mem_stabilizer_iff.2 hX'⟩
  have hg'O : (g' : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) := mul_mem (mul_mem hσO hO) hσO
  set q := ((plusXBlock g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] with hq
  have he : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have hhX : h • plusFamOne ![1, 0] = plusFamOne q := by
    have h1 := smul_plusFamTwo_of_stab g' hg'O he
    change (σ * h * σ) • plusFamTwo ![1, 0] = plusFamTwo q at h1
    rw [← swapPair_smul_plusFamTwo, ← swapPair_smul_plusFamTwo, ← h1, smul_smul, smul_smul,
      ← mul_assoc, ← mul_assoc, hσσ, one_mul]
  have hq0 : q ≠ 0 := fun h0 => by
    have hinv := congrArg (fun M => M *ᵥ ![1, 0]) (show
      ((plusXBlock g'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((plusXBlock g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])
    simp only [← mulVec_mulVec, ← hq, h0, mulVec_zero, one_mulVec] at hinv
    exact he hinv.symm
  obtain ⟨A₁, hA₁⟩ := exists_sl_mulVec_one_zero_eq hq0
  have hgX : ((plusIotaOne K A₁)⁻¹ * h) • flag 2 K 2 = flag 2 K 2 := by
    rw [flag_two_eq_plusFamOne, mul_smul, hhX, ← hA₁, ← plusIotaOne_smul_plusFamOne A₁ he,
      smul_smul, inv_mul_cancel, one_smul]
  have hg := mem_plusFamTwoStab_of_stab
    ⟨(plusIotaOne K A₁)⁻¹ * h, MulAction.mem_stabilizer_iff.2 hgX⟩
    (mul_mem (inv_mem (plusIotaOne_mem_orthogonalGroup A₁)) hO)
  have := mul_mem (plusIotaOne_mem_plusFamTwoStab A₁) hg
  rwa [← mul_assoc, mul_inv_cancel, one_mul] at this

omit [CharP K 2] in
theorem apply_mem_of_fixes {h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)}
    {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hP : h • P = P) {x : Fin 2 ⊕ Fin 2 → K}
    (hx : x ∈ P) : h x ∈ P := by
  rw [← hP]
  exact ⟨x, hx, rfl⟩

theorem eq_one_of_plusFam {h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K))
    (h₁ : ∀ p : Fin 2 → K, p ≠ 0 → h • plusFamOne p = plusFamOne p)
    (h₂ : ∀ p : Fin 2 → K, p ≠ 0 → h • plusFamTwo p = plusFamTwo p) : h = 1 := by
  have n10 : (![1, 0] : Fin 2 → K) ≠ 0 := fun e => by simpa using congrFun e 0
  have n01 : (![0, 1] : Fin 2 → K) ≠ 0 := fun e => by simpa using congrFun e 1
  have n11 : (![1, 1] : Fin 2 → K) ≠ 0 := fun e => by simpa using congrFun e 0
  set m := autMat h with hm
  have e : ∀ w u, h (Pi.single w 1) u = m u w := fun w u => (autMat_apply_eq h u w).symm
  have e2 : ∀ w w' u, h (Pi.single w 1 + Pi.single w' 1) u = m u w + m u w' := fun w w' u => by
    rw [map_add, Pi.add_apply, e, e]
  have A1 := mem_plusFamOne.1 (apply_mem_of_fixes (h₁ _ n10) (x := Pi.single (Sum.inl 0) 1)
    (by simp [mem_plusFamOne]))
  have A2 := mem_plusFamTwo.1 (apply_mem_of_fixes (h₂ _ n10) (x := Pi.single (Sum.inl 0) 1)
    (by simp [mem_plusFamTwo]))
  have B1 := mem_plusFamOne.1 (apply_mem_of_fixes (h₁ _ n10) (x := Pi.single (Sum.inl 1) 1)
    (by simp [mem_plusFamOne]))
  have B2 := mem_plusFamTwo.1 (apply_mem_of_fixes (h₂ _ n01) (x := Pi.single (Sum.inl 1) 1)
    (by simp [mem_plusFamTwo]))
  have C1 := mem_plusFamOne.1 (apply_mem_of_fixes (h₁ _ n01) (x := Pi.single (Sum.inr 0) 1)
    (by simp [mem_plusFamOne]))
  have C2 := mem_plusFamTwo.1 (apply_mem_of_fixes (h₂ _ n01) (x := Pi.single (Sum.inr 0) 1)
    (by simp [mem_plusFamTwo]))
  have D1 := mem_plusFamOne.1 (apply_mem_of_fixes (h₁ _ n01) (x := Pi.single (Sum.inr 1) 1)
    (by simp [mem_plusFamOne]))
  have D2 := mem_plusFamTwo.1 (apply_mem_of_fixes (h₂ _ n10) (x := Pi.single (Sum.inr 1) 1)
    (by simp [mem_plusFamTwo]))
  have Z1 := mem_plusFamOne.1 (apply_mem_of_fixes (h₁ _ n11)
    (x := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 1) 1) (by simp [mem_plusFamOne]))
  have Z2 := mem_plusFamTwo.1 (apply_mem_of_fixes (h₂ _ n11)
    (x := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inl 1) 1) (by simp [mem_plusFamTwo]))
  have Z3 := mem_plusFamOne.1 (apply_mem_of_fixes (h₁ _ n11)
    (x := Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 0) 1) (by simp [mem_plusFamOne]))
  simp only [e, e2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one,
    mul_zero] at A1 A2 B1 B2 C1 C2 D1 D2 Z1 Z2 Z3
  have hQ := map_of_mem hO (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)
  rw [quadPlus_two_apply, quadPlus_two_apply] at hQ
  simp only [e2] at hQ
  have hd : m (Sum.inr 1) (Sum.inr 1) = m (Sum.inl 0) (Sum.inl 0) := by
    have := Z1.1
    rw [D1.1, ← A1.1, add_zero, zero_add] at this
    exact this.symm
  have hb : m (Sum.inl 1) (Sum.inl 1) = m (Sum.inl 0) (Sum.inl 0) := by
    have := Z2.1
    rw [B2.1, ← A2.1, add_zero, zero_add] at this
    exact this.symm
  have hc : m (Sum.inr 0) (Sum.inr 0) = m (Sum.inl 0) (Sum.inl 0) := by
    have := Z3.2
    rw [C1.2, ← B1.2, add_zero, zero_add] at this
    exact this.symm.trans hb
  rw [C1.1, ← A1.2, hc, ← A2.1, C1.2, ← A1.1, C2.2] at hQ
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [add_zero, zero_add, mul_zero, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, ite_true, ite_false, mul_one, h10] at hQ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha : m (Sum.inl 0) (Sum.inl 0) = 1 := by
    have hsq : (m (Sum.inl 0) (Sum.inl 0) - 1) ^ 2 = 0 := by
      linear_combination hQ - (m (Sum.inl 0) (Sum.inl 0) - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  apply autMat_injective
  rw [map_one, ← hm]
  ext u w
  rcases u with i | i <;> rcases w with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ha, hb, hc, hd, ← A1.1, ← A1.2, ← A2.1, ← B1.1, ← B1.2, B2.1, C1.1, C1.2, C2.2,
      D1.1, D1.2, ← D2.2]

end CFSG.AGLEmbedding.LeviBlock
