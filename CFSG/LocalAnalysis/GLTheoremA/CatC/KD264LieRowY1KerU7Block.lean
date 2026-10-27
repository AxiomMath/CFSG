module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Block
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Sym

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def blkU (h : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 7) (Fin 7) K :=
  (Matrix.fromBlocks h 0 0 (1 : Matrix (Fin 4) (Fin 4) K)).submatrix sumEq7 sumEq7

theorem blkU_mul (h h' : Matrix (Fin 3) (Fin 3) K) : blkU (h * h') = blkU h * blkU h' := by
  unfold blkU
  rw [blockDiag_mul, Matrix.mul_one]

theorem blkU_one : blkU (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  unfold blkU
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem det_blkU (h : Matrix (Fin 3) (Fin 3) K) : (blkU h).det = h.det := by
  unfold blkU
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blkU_inj {h h' : Matrix (Fin 3) (Fin 3) K} (hh : blkU h = blkU h') : h = h' := by
  ext a b
  have := congrFun (congrFun hh (sumEq7.symm (Sum.inl a))) (sumEq7.symm (Sum.inl b))
  simpa [blkU] using this

theorem dagI_one {ι : Type} [Fintype ι] [DecidableEq ι] (h : UnitaryFieldData p f K) :
    dagI h (1 : Matrix ι ι K) = 1 := by
  unfold dagI
  rw [Matrix.map_one, Matrix.transpose_one]
  · exact h.bar.map_zero
  · exact h.bar.map_one

theorem dagI_blkU (h : UnitaryFieldData p f K) (M : Matrix (Fin 3) (Fin 3) K) :
    dagI h (blkU M) = blkU (dagI h M) := by
  unfold blkU
  rw [dagI_submatrix, dagI_fromBlocks0, dagI_one]

theorem blkU_comm_D0 (h : Matrix (Fin 3) (Fin 3) K) : blkU h * D0 K = D0 K * blkU h := by
  rw [D0_eq_block]
  unfold blkU
  rw [blockDiag_mul, blockDiag_mul]
  simp

theorem blkU_mulVec_of_ker (h : Matrix (Fin 3) (Fin 3) K) (v : Fin 7 → K)
    (hv : ∀ i : Fin 7, (i : ℕ) < 3 → v i = 0) : blkU h *ᵥ v = v := by
  funext i
  unfold blkU
  rw [Matrix.submatrix_mulVec_equiv]
  have hz : ∀ b : Fin 3, v (sumEq7.symm (Sum.inl b)) = 0 := fun b =>
    hv _ (by rw [sumEq7_symm_inl_val]; exact b.isLt)
  obtain ⟨t, rfl⟩ : ∃ t, i = sumEq7.symm t := ⟨sumEq7 i, by simp⟩
  rcases t with a | b
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, hz]
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

theorem inH0_blkU (h : Matrix (Fin 3) (Fin 3) K) :
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0 (blkU h) := by
  refine ⟨blkU_comm_D0 h, fun v hv => ?_⟩
  apply blkU_mulVec_of_ker
  intro i hi
  have := congrFun hv i
  rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.Dg_eq, Matrix.mulVec_diagonal, Pi.zero_apply] at this
  simpa [hi] using this

@[expose] noncomputable def blkGL (A : GL (Fin 3) K) : GL (Fin 7) K :=
  ⟨blkU (A : Matrix (Fin 3) (Fin 3) K), blkU ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
    by rw [← blkU_mul, Units.mul_inv, blkU_one],
    by rw [← blkU_mul, Units.inv_mul, blkU_one]⟩

theorem blkGL_val (A : GL (Fin 3) K) :
    ((blkGL A : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = blkU (A : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem blkGL_mem (h : UnitaryFieldData p f K) {A : GL (Fin 3) K}
    (hA : A ∈ StatedSU 3 (p ^ f) K) : blkGL A ∈ StatedSU 7 (p ^ f) K := by
  obtain ⟨hdet, hu⟩ := (mem_statedSU_iff h 3 A).mp hA
  rw [mem_statedSU_iff h 7]
  refine ⟨?_, ?_⟩
  · rw [blkGL_val, det_blkU, hdet]
  · have hu' : dagI h (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 := hu
    show dagI h ((blkGL A : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      ((blkGL A : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = 1
    rw [blkGL_val, dagI_blkU, ← blkU_mul, hu', blkU_one]

@[expose] noncomputable def blkHomU (h : UnitaryFieldData p f K) :
    ↥(StatedSU 3 (p ^ f) K) →* ↥(StatedSU 7 (p ^ f) K) where
  toFun x := ⟨blkGL x.1, blkGL_mem h x.2⟩
  map_one' := Subtype.ext (Units.ext (by simp [blkGL_val, blkU_one]))
  map_mul' x y := Subtype.ext (Units.ext (by simp [blkGL_val, blkU_mul]))

@[expose] def H0U (h : UnitaryFieldData p f K) : Subgroup ↥(StatedSU 7 (p ^ f) K) where
  carrier := {g | CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
    ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)}
  mul_mem' := fun {a b} ha hb => by
    show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
      (((a * b : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.inH0_mul ha hb
  one_mem' := by
    show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
      ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
    rw [Units.val_one]
    exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.inH0_one
  inv_mem' := fun {a} ha => by
    show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
      (((a : GL (Fin 7) K)⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
    refine CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.inH0_inv ha ?_ ?_
    · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem blkHomU_mem (h : UnitaryFieldData p f K) (x : ↥(StatedSU 3 (p ^ f) K)) :
    blkHomU h x ∈ H0U h := by
  show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0 (blkU (x.1 : Matrix (Fin 3) (Fin 3) K))
  exact inH0_blkU _

@[expose] noncomputable def blkHomU' (h : UnitaryFieldData p f K) :
    ↥(StatedSU 3 (p ^ f) K) →* ↥(H0U h) :=
  (blkHomU h).codRestrict (H0U h) (blkHomU_mem h)

theorem blkHomU'_injective (h : UnitaryFieldData p f K) : Function.Injective (blkHomU' h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : blkHomU h x = 1 := by
    have := congrArg Subtype.val hx
    exact this
  apply Subtype.ext
  apply Units.ext
  have h1 : blkU ((x.1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = blkU 1 := by
    have := congrArg (fun y : ↥(StatedSU 7 (p ^ f) K) =>
      ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) hx'
    simpa [blkHomU, blkGL_val, blkU_one] using this
  simpa using blkU_inj h1

theorem eq_blkU_of_InH0 {g : Matrix (Fin 7) (Fin 7) K}
    (hg : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0 g) :
    g = blkU (fun a b => g (sumEq7.symm (Sum.inl a)) (sumEq7.symm (Sum.inl b))) := by
  ext i j
  obtain ⟨s, rfl⟩ : ∃ s, i = sumEq7.symm s := ⟨sumEq7 i, by simp⟩
  obtain ⟨t, rfl⟩ : ∃ t, j = sumEq7.symm t := ⟨sumEq7 j, by simp⟩
  rcases s with a | c <;> rcases t with b | d
  · simp only [blkU, Matrix.submatrix_apply, Equiv.apply_symm_apply]
    first | rfl | simp [Matrix.fromBlocks_apply₁₁]
  · have hij : (((sumEq7.symm (Sum.inl a) : Fin 7) : ℕ) < 3) ≠
        (((sumEq7.symm (Sum.inr d) : Fin 7) : ℕ) < 3) := by
      simp [sumEq7_symm_inl_val, sumEq7_symm_inr_val]
    rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0_offblock hg _ _ hij]
    simp only [blkU, Matrix.submatrix_apply, Equiv.apply_symm_apply]
    first | rfl | simp [Matrix.fromBlocks_apply₁₂]
  · have hij : (((sumEq7.symm (Sum.inr c) : Fin 7) : ℕ) < 3) ≠
        (((sumEq7.symm (Sum.inl b) : Fin 7) : ℕ) < 3) := by
      simp [sumEq7_symm_inl_val, sumEq7_symm_inr_val]
    rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0_offblock hg _ _ hij]
    simp only [blkU, Matrix.submatrix_apply, Equiv.apply_symm_apply]
    first | rfl | simp [Matrix.fromBlocks_apply₂₁]
  · have hc : 3 ≤ ((sumEq7.symm (Sum.inr c) : Fin 7) : ℕ) := by
      rw [sumEq7_symm_inr_val]; omega
    have hd : 3 ≤ ((sumEq7.symm (Sum.inr d) : Fin 7) : ℕ) := by
      rw [sumEq7_symm_inr_val]; omega
    rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0_bottom hg _ _ hc hd]
    have hcd : sumEq7.symm (Sum.inr c) = sumEq7.symm (Sum.inr d) ↔ c = d :=
      sumEq7.symm.injective.eq_iff.trans Sum.inr_injective.eq_iff
    by_cases hcd' : c = d
    · subst hcd'
      rw [if_pos rfl]
      simp only [blkU, Matrix.submatrix_apply, Equiv.apply_symm_apply]
      exact (Matrix.one_apply_eq c).symm
    · have hne : sumEq7.symm (Sum.inr c) ≠ sumEq7.symm (Sum.inr d) := fun h' => hcd' (hcd.mp h')
      rw [if_neg hne]
      simp only [blkU, Matrix.submatrix_apply, Equiv.apply_symm_apply]
      exact (Matrix.one_apply_ne hcd').symm

theorem blkHomU'_surjective (h : UnitaryFieldData p f K) : Function.Surjective (blkHomU' h) := by
  rintro ⟨y, hy⟩
  have hyI : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
      ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := hy
  have hyU := (mem_statedSU_iff h 7 (y : GL (Fin 7) K)).mp y.2
  have hyblk := eq_blkU_of_InH0 hyI
  set X : Matrix (Fin 3) (Fin 3) K := fun a b =>
    ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) (sumEq7.symm (Sum.inl a))
      (sumEq7.symm (Sum.inl b)) with hX
  have hdetX : X.det = 1 := by
    have h1 := hyU.1
    rw [hyblk, det_blkU] at h1
    exact h1
  have hunitX : dagI h X * X = 1 := by
    have h2 : dagI h ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
        ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = 1 := hyU.2
    rw [hyblk, dagI_blkU, ← blkU_mul] at h2
    exact blkU_inj (h2.trans blkU_one.symm)
  have hXu : X * dagI h X = 1 := by
    have hinv : X⁻¹ = dagI h X := Matrix.inv_eq_left_inv hunitX
    rw [← hinv]
    exact Matrix.mul_nonsing_inv X (by rw [hdetX]; exact isUnit_one)
  let tlGL : GL (Fin 3) K := ⟨X, dagI h X, hXu, hunitX⟩
  let x : ↥(StatedSU 3 (p ^ f) K) := ⟨tlGL, (mem_statedSU_iff h 3 tlGL).mpr ⟨hdetX, hunitX⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show blkU X = ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
  exact hyblk.symm

@[expose] noncomputable def blkEquivU (h : UnitaryFieldData p f K) :
    ↥(StatedSU 3 (p ^ f) K) ≃* ↥(H0U h) :=
  MulEquiv.ofBijective (blkHomU' h) ⟨blkHomU'_injective h, blkHomU'_surjective h⟩

theorem hF_of (h : UnitaryFieldData p f K) : Nat.card K = (p ^ f) ^ 2 := by
  rw [h.card, ← pow_mul, mul_comm]

theorem hnq_of {p f : ℕ} (hQ : 3 ∣ p ^ f - 1) : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
  intro heq
  have h2 : p ^ f = 2 := (Prod.mk.inj heq).2
  rw [h2] at hQ
  norm_num at hQ

theorem H0U_isQuasisimple (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1) :
    CFSG.Open.IsQuasisimple (H0U h) := by
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hS3 := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := f) (n := 3) (hF_of h) le_rfl (hnq_of hQ)).1
  have hS3' : CFSG.Open.IsQuasisimple ↥(StatedSU 3 (p ^ f) K) := by
    obtain ⟨h1, h2, -⟩ := hS3
    exact ⟨h1.commutator_eq_top, h2⟩
  exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv (blkEquivU h) hS3'

@[expose] def cycM : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cycM' : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cycM_mul : cycM (K := K) * cycM' = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycM, cycM', Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply]

theorem cycM'_mul : cycM' (K := K) * cycM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycM, cycM', Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply]

theorem cycM_cube : cycM (K := K) ^ 3 = 1 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycM, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply]

theorem cycM_map (h : UnitaryFieldData p f K) : cycM.map h.bar = cycM := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycM, h.bar.map_zero, h.bar.map_one]

theorem cycM_unitary (h : UnitaryFieldData p f K) : dagI h (cycM (K := K)) * cycM = 1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  unfold dagI
  rw [cycM_map h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycM, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply]

@[expose] def cycGL : GL (Fin 3) K := ⟨cycM, cycM', cycM_mul, cycM'_mul⟩

@[expose] def cycU (h : UnitaryFieldData p f K) : ↥(StatedSU 3 (p ^ f) K) :=
  ⟨cycGL, (mem_statedSU_iff h 3 cycGL).mpr
    ⟨by simp [cycGL, cycM, Matrix.det_fin_three], cycM_unitary h⟩⟩

theorem cycU_pow_three (h : UnitaryFieldData p f K) : cycU h ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact cycM_cube

theorem cycU_not_central (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1) :
    cycU h ∉ Subgroup.center ↥(StatedSU 3 (p ^ f) K) := by
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro hc
  rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := f) (n := 3) (hF_of h) le_rfl (hnq_of hQ)).2, Subgroup.mem_subgroupOf] at hc
  unfold StatedScalars at hc
  obtain ⟨c, hcs⟩ := MonoidHom.mem_range.mp hc
  have hent := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) hcs
  simp [cycU, cycGL, cycM, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] at hent

theorem H0U_three_dvd (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1) :
    3 ∣ Nat.card (↥(H0U h) ⧸ Subgroup.center ↥(H0U h)) := by
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv (blkEquivU h)]
  exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.three_dvd_quot_of_noncentral (cycU h)
    (cycU_pow_three h) (cycU_not_central h hQ)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
