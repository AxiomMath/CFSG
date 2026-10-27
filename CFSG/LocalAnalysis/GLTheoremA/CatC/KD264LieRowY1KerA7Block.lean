module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Transport
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

open Matrix

variable {K : Type} [Field K]

@[expose] def sumEq7 : Fin 7 ≃ Fin 3 ⊕ Fin 4 :=
  (finCongr (rfl : 7 = 3 + 4)).trans (finSumFinEquiv (m := 3) (n := 4)).symm

@[expose] def Dg (K : Type) [Field K] : Matrix (Fin 7) (Fin 7) K :=
  Matrix.diagonal (fun i : Fin 7 => if (i : ℕ) < 3 then (1 : K) else 0)

@[expose] def blk (h : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 7) (Fin 7) K :=
  (Matrix.fromBlocks h 0 0 (1 : Matrix (Fin 4) (Fin 4) K)).submatrix sumEq7 sumEq7

theorem blk_mul (h h' : Matrix (Fin 3) (Fin 3) K) : blk (h * h') = blk h * blk h' := by
  unfold blk
  rw [Matrix.submatrix_mul_equiv _ _ sumEq7 sumEq7 sumEq7, Matrix.fromBlocks_multiply]
  simp

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem det_blk (h : Matrix (Fin 3) (Fin 3) K) : (blk h).det = h.det := by
  unfold blk
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem sumEq7_isLeft (i : Fin 7) : (sumEq7 i).isLeft = decide ((i : ℕ) < 3) := by
  revert i
  decide

theorem blk_apply (h : Matrix (Fin 3) (Fin 3) K) (i j : Fin 7) :
    blk h i j = Matrix.fromBlocks h 0 0 (1 : Matrix (Fin 4) (Fin 4) K) (sumEq7 i) (sumEq7 j) := by
  simp [blk]

theorem blk_offblock (h : Matrix (Fin 3) (Fin 3) K) (i j : Fin 7)
    (hij : ((i : ℕ) < 3) ≠ ((j : ℕ) < 3)) : blk h i j = 0 := by
  rw [blk_apply]
  have hi : (sumEq7 i).isLeft = decide ((i : ℕ) < 3) := sumEq7_isLeft i
  have hj : (sumEq7 j).isLeft = decide ((j : ℕ) < 3) := sumEq7_isLeft j
  cases hx : sumEq7 i with
  | inl a =>
    cases hy : sumEq7 j with
    | inl b =>
      exfalso
      rw [hx, Sum.isLeft_inl] at hi
      rw [hy, Sum.isLeft_inl] at hj
      have h1 := of_decide_eq_true hi.symm
      have h2 := of_decide_eq_true hj.symm
      exact hij (by simp [h1, h2])
    | inr b => simp [Matrix.fromBlocks_apply₁₂]
  | inr a =>
    cases hy : sumEq7 j with
    | inl b => simp [Matrix.fromBlocks_apply₂₁]
    | inr b =>
      exfalso
      rw [hx, Sum.isLeft_inr] at hi
      rw [hy, Sum.isLeft_inr] at hj
      have h1 := of_decide_eq_false hi.symm
      have h2 := of_decide_eq_false hj.symm
      exact hij (by simp [h1, h2])

@[expose] def InH0 (g : Matrix (Fin 7) (Fin 7) K) : Prop :=
  g * Dg K = Dg K * g ∧ ∀ v : Fin 7 → K, (Dg K) *ᵥ v = 0 → g *ᵥ v = v

theorem inH0_one : InH0 (1 : Matrix (Fin 7) (Fin 7) K) := by
  refine ⟨by rw [Matrix.one_mul, Matrix.mul_one], fun v _ => ?_⟩
  rw [Matrix.one_mulVec]

theorem inH0_mul {g h : Matrix (Fin 7) (Fin 7) K} (hg : InH0 g) (hh : InH0 h) :
    InH0 (g * h) := by
  refine ⟨?_, fun v hv => ?_⟩
  · rw [Matrix.mul_assoc, hh.1, ← Matrix.mul_assoc, hg.1, Matrix.mul_assoc]
  · rw [← Matrix.mulVec_mulVec, hh.2 v hv, hg.2 v hv]

theorem inH0_inv {g : Matrix (Fin 7) (Fin 7) K} {g' : Matrix (Fin 7) (Fin 7) K}
    (hg : InH0 g) (hgg' : g' * g = 1) (hgg'' : g * g' = 1) : InH0 g' := by
  refine ⟨?_, fun v hv => ?_⟩
  · calc g' * Dg K = g' * Dg K * (g * g') := by rw [hgg'', Matrix.mul_one]
      _ = g' * (Dg K * g) * g' := by simp only [Matrix.mul_assoc]
      _ = g' * (g * Dg K) * g' := by rw [← hg.1]
      _ = Dg K * g' := by simp only [← Matrix.mul_assoc, hgg', Matrix.one_mul]
  · have hgv : g *ᵥ v = v := hg.2 v hv
    calc g' *ᵥ v = g' *ᵥ (g *ᵥ v) := by rw [hgv]
      _ = v := by rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]

@[expose] def H0 : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K) where
  carrier := {g | InH0 (g : Matrix (Fin 7) (Fin 7) K)}
  mul_mem' := fun {a b} ha hb => inH0_mul ha hb
  one_mem' := inH0_one
  inv_mem' := fun {a} ha => by
    refine inH0_inv ha (g' := ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K)) ?_ ?_
    · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem Dg_eq : Dg K = Matrix.diagonal (fun i : Fin 7 => if (i : ℕ) < 3 then (1 : K) else 0) :=
  rfl

theorem InH0_offblock {g : Matrix (Fin 7) (Fin 7) K} (hg : InH0 g) (i j : Fin 7)
    (hij : ((i : ℕ) < 3) ≠ ((j : ℕ) < 3)) : g i j = 0 := by
  have hc := congrFun (congrFun hg.1 i) j
  rw [Dg_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  by_cases hi : (i : ℕ) < 3
  · have hj : ¬ (j : ℕ) < 3 := fun h => hij (by simp [hi, h])
    have hc' := hc
    simp [hi, hj] at hc'
    exact hc'.symm
  · have hj : (j : ℕ) < 3 := by
      by_contra hj
      exact hij (by simp [hi, hj])
    simpa [hi, hj] using hc

theorem sumEq7_symm_lt (b : Fin 3) : ((sumEq7.symm (Sum.inl b) : Fin 7) : ℕ) < 3 := by
  revert b
  decide

theorem sumEq7_symm_ge (b : Fin 4) : 3 ≤ ((sumEq7.symm (Sum.inr b) : Fin 7) : ℕ) := by
  revert b
  decide

theorem InH0_bottom {g : Matrix (Fin 7) (Fin 7) K} (hg : InH0 g) (a b : Fin 7)
    (ha : 3 ≤ (a : ℕ)) (hb : 3 ≤ (b : ℕ)) : g a b = if a = b then 1 else 0 := by
  have hcol := hg.2 (Pi.single b 1) (by
    funext i
    rw [Dg_eq, Matrix.mulVec_diagonal, Pi.zero_apply]
    by_cases hi : (i : ℕ) < 3
    · have hib : i ≠ b := by
        intro h
        rw [h] at hi
        omega
      simp [hi, Pi.single_apply, hib]
    · simp [hi])
  have := congrFun hcol a
  rw [Matrix.mulVec, dotProduct] at this
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  rw [this]

theorem blk_commutes_Dg (h : Matrix (Fin 3) (Fin 3) K) : blk h * Dg K = Dg K * blk h := by
  ext i j
  rw [Dg_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : (i : ℕ) < 3 <;> by_cases hj : (j : ℕ) < 3
  · simp [hi, hj]
  · rw [blk_offblock _ i j (by simp [hi, hj])]
    simp [hi, hj]
  · rw [blk_offblock _ i j (by simp [hi, hj])]
    simp [hi, hj]
  · simp [hi, hj]

theorem blk_mulVec_of_ker (h : Matrix (Fin 3) (Fin 3) K) (v : Fin 7 → K)
    (hvi : ∀ i : Fin 7, (i : ℕ) < 3 → v i = 0) : blk h *ᵥ v = v := by
  unfold blk
  rw [Matrix.submatrix_mulVec_equiv]
  funext i
  simp only [Function.comp_apply]
  obtain ⟨x, rfl⟩ : ∃ x, i = sumEq7.symm x := ⟨sumEq7 i, by simp⟩
  rw [Equiv.apply_symm_apply]
  rcases x with a | a
  · have hw : (v ∘ sumEq7.symm) ∘ Sum.inl = 0 := by
      funext b
      exact hvi _ (sumEq7_symm_lt b)
    rw [Matrix.fromBlocks_mulVec]
    simp [hw, hvi _ (sumEq7_symm_lt a)]
  · rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inr, Matrix.zero_mulVec, zero_add, Matrix.one_mulVec, Function.comp_apply]

theorem blk_inH0 (h : Matrix.SpecialLinearGroup (Fin 3) K) :
    InH0 (blk ((h : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  refine ⟨blk_commutes_Dg _, fun v hv => ?_⟩
  apply blk_mulVec_of_ker
  intro i hi
  have := congrFun hv i
  rw [Dg_eq, Matrix.mulVec_diagonal, Pi.zero_apply] at this
  simpa [hi] using this

@[expose] def blkSL (h : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix.SpecialLinearGroup (Fin 7) K :=
  ⟨blk (h : Matrix (Fin 3) (Fin 3) K), by rw [det_blk]; exact h.2⟩

@[expose] def tlOf (g : Matrix (Fin 7) (Fin 7) K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => g (sumEq7.symm (Sum.inl i)) (sumEq7.symm (Sum.inl j))

theorem InH0_eq_blk {g : Matrix (Fin 7) (Fin 7) K} (hg : InH0 g) : g = blk (tlOf g) := by
  ext a b
  rw [blk_apply]
  obtain ⟨x, rfl⟩ : ∃ x, a = sumEq7.symm x := ⟨sumEq7 a, by simp⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = sumEq7.symm y := ⟨sumEq7 b, by simp⟩
  simp only [Equiv.apply_symm_apply]
  rcases x with i | i <;> rcases y with j | j
  · rw [Matrix.fromBlocks_apply₁₁]
    rfl
  · rw [Matrix.fromBlocks_apply₁₂]
    apply InH0_offblock hg
    intro h
    have h1 := sumEq7_symm_lt i
    have h2 := sumEq7_symm_ge j
    rw [eq_iff_iff] at h
    have h3 : ¬ (((sumEq7.symm (Sum.inr j)) : Fin 7) : ℕ) < 3 := by omega
    exact h3 (h.mp h1)
  · rw [Matrix.fromBlocks_apply₂₁]
    apply InH0_offblock hg
    intro h
    have h1 := sumEq7_symm_ge i
    have h2 := sumEq7_symm_lt j
    rw [eq_iff_iff] at h
    have h3 : ¬ (((sumEq7.symm (Sum.inr i)) : Fin 7) : ℕ) < 3 := by omega
    exact h3 (h.mpr h2)
  · rw [Matrix.fromBlocks_apply₂₂, InH0_bottom hg _ _ (sumEq7_symm_ge i) (sumEq7_symm_ge j)]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : sumEq7.symm (Sum.inr i) ≠ sumEq7.symm (Sum.inr j) := fun h =>
        hij (Sum.inr_injective (sumEq7.symm.injective h))
      rw [if_neg hne, Matrix.one_apply_ne hij]

theorem blkSL_mul (a b : Matrix.SpecialLinearGroup (Fin 3) K) :
    blkSL (a * b) = blkSL a * blkSL b := by
  apply Subtype.ext
  show blk (((a * b : Matrix.SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
    blk (a : Matrix (Fin 3) (Fin 3) K) * blk (b : Matrix (Fin 3) (Fin 3) K)
  rw [Matrix.SpecialLinearGroup.coe_mul, blk_mul]

theorem blkSL_one : blkSL (1 : Matrix.SpecialLinearGroup (Fin 3) K) = 1 := by
  apply Subtype.ext
  show blk ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
  rw [Matrix.SpecialLinearGroup.coe_one, blk_one]

@[expose] noncomputable def blkHom : Matrix.SpecialLinearGroup (Fin 3) K →* (H0 (K := K)) where
  toFun h := ⟨blkSL h, blk_inH0 h⟩
  map_one' := Subtype.ext blkSL_one
  map_mul' a b := Subtype.ext (blkSL_mul a b)

theorem blkHom_injective : Function.Injective (blkHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have hh' : blkSL h = 1 := by
    have := congrArg Subtype.val hh
    exact this
  have hb : blk (h : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 7) K =>
      (x : Matrix (Fin 7) (Fin 7) K)) hh'
    exact this
  apply Subtype.ext
  ext i j
  have hij := congrFun (congrFun hb (sumEq7.symm (Sum.inl i))) (sumEq7.symm (Sum.inl j))
  rw [blk_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.fromBlocks_apply₁₁] at hij
  rw [Matrix.SpecialLinearGroup.coe_one, hij, Matrix.one_apply, Matrix.one_apply]
  by_cases hij2 : i = j
  · subst hij2
    simp
  · have hne : sumEq7.symm (Sum.inl i) ≠ sumEq7.symm (Sum.inl j) := fun h =>
      hij2 (Sum.inl_injective (sumEq7.symm.injective h))
    rw [if_neg hne, if_neg hij2]

theorem blkHom_surjective : Function.Surjective (blkHom (K := K)) := by
  rintro ⟨x, hx⟩
  have hx' : InH0 (x : Matrix (Fin 7) (Fin 7) K) := hx
  have hG : (x : Matrix (Fin 7) (Fin 7) K) = blk (tlOf (x : Matrix (Fin 7) (Fin 7) K)) :=
    InH0_eq_blk hx'
  have hdet : (tlOf (x : Matrix (Fin 7) (Fin 7) K)).det = 1 := by
    have h1 : ((x : Matrix.SpecialLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K).det = 1 :=
      x.2
    rw [← det_blk, ← hG]
    exact h1
  refine ⟨⟨tlOf (x : Matrix (Fin 7) (Fin 7) K), hdet⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hG.symm

@[expose] noncomputable def blkEquiv : Matrix.SpecialLinearGroup (Fin 3) K ≃* (H0 (K := K)) :=
  MulEquiv.ofBijective (blkHom (K := K)) ⟨blkHom_injective, blkHom_surjective⟩

theorem isQuasisimple_SL3 : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) K) := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by omega) (Or.inl le_rfl)
  exact ⟨Group.isPerfect_def.mp hperf, hsimple⟩

def cyc (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem cyc_pow_three : cyc K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  simp [cyc, pow_succ, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem cyc_not_central : cyc K ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  intro hmem
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  have h10 := congrFun (congrFun hr 1) 0
  simp [cyc, Matrix.scalar_apply] at h10

theorem three_dvd_quot_of_noncentral {G : Type} [Group G] (g : G) (hg3 : g ^ 3 = 1)
    (hg : g ∉ Subgroup.center G) : 3 ∣ Nat.card (G ⧸ Subgroup.center G) := by
  have h1 : orderOf (QuotientGroup.mk g : G ⧸ Subgroup.center G) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hg3, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk g : G ⧸ Subgroup.center G) ≠ 1 := by
    intro h
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
    exact hg h
  have h3 : orderOf (QuotientGroup.mk g : G ⧸ Subgroup.center G) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd h h2
    · exact h
  rw [← h3]
  exact orderOf_dvd_natCard _

theorem three_dvd_quot_SL3 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) :=
  three_dvd_quot_of_noncentral (cyc K) (cyc_pow_three) cyc_not_central

theorem Dg_mul_Dg : Dg K * Dg K = Dg K := by
  rw [Dg_eq, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < 3 <;> simp [hi]

theorem InH0_conj {g c c' : Matrix (Fin 7) (Fin 7) K} (hg : InH0 g) (hcc' : c * c' = 1)
    (hc'c : c' * c = 1) (hcD : c * Dg K = Dg K * c) : InH0 (c * g * c') := by
  have hc'D : c' * Dg K = Dg K * c' := by
    calc c' * Dg K = c' * Dg K * (c * c') := by rw [hcc', Matrix.mul_one]
      _ = c' * (Dg K * c) * c' := by simp only [Matrix.mul_assoc]
      _ = c' * (c * Dg K) * c' := by rw [← hcD]
      _ = Dg K * c' := by simp only [← Matrix.mul_assoc, hc'c, Matrix.one_mul]
  refine ⟨?_, fun v hv => ?_⟩
  · calc c * g * c' * Dg K = c * g * (c' * Dg K) := by simp only [Matrix.mul_assoc]
      _ = c * g * (Dg K * c') := by rw [hc'D]
      _ = c * (g * Dg K) * c' := by simp only [Matrix.mul_assoc]
      _ = c * (Dg K * g) * c' := by rw [hg.1]
      _ = (c * Dg K) * g * c' := by simp only [Matrix.mul_assoc]
      _ = (Dg K * c) * g * c' := by rw [hcD]
      _ = Dg K * (c * g * c') := by simp only [Matrix.mul_assoc]
  · have hc'v : (Dg K) *ᵥ (c' *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, ← hc'D, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    have hg' : g *ᵥ (c' *ᵥ v) = c' *ᵥ v := hg.2 _ hc'v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg', Matrix.mulVec_mulVec, hcc',
      Matrix.one_mulVec]

theorem H0_conj_mem (c : Matrix.SpecialLinearGroup (Fin 7) K)
    (hc : (c : Matrix (Fin 7) (Fin 7) K) * Dg K = Dg K * (c : Matrix (Fin 7) (Fin 7) K))
    (g : Matrix.SpecialLinearGroup (Fin 7) K) (hg : g ∈ (H0 (K := K))) :
    c * g * c⁻¹ ∈ (H0 (K := K)) := by
  have hg' : InH0 (g : Matrix (Fin 7) (Fin 7) K) := hg
  have hcc : (c : Matrix (Fin 7) (Fin 7) K) * ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hcc2 : ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      (c : Matrix (Fin 7) (Fin 7) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  show InH0 _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact InH0_conj hg' hcc hcc2 hc

theorem InH0_comm {g f : Matrix (Fin 7) (Fin 7) K} (hg : InH0 g) (hf1 : f * Dg K = Dg K)
    (hf2 : Dg K * f = Dg K) : g * f = f * g := by
  have hfD : ∀ x, f *ᵥ (Dg K *ᵥ x) = Dg K *ᵥ x := fun x => by
    rw [Matrix.mulVec_mulVec, hf1]
  have hDf : ∀ x, Dg K *ᵥ (f *ᵥ x) = Dg K *ᵥ x := fun x => by
    rw [Matrix.mulVec_mulVec, hf2]
  have hgD : ∀ x, g *ᵥ (Dg K *ᵥ x) = Dg K *ᵥ (g *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg.1]
  have hDD : ∀ x, Dg K *ᵥ (Dg K *ᵥ x) = Dg K *ᵥ x := fun x => by
    rw [Matrix.mulVec_mulVec, Dg_mul_Dg]
  have hkerw : ∀ x, Dg K *ᵥ (x - Dg K *ᵥ x) = 0 := fun x => by
    rw [Matrix.mulVec_sub, hDD, sub_self]
  have hvec : ∀ v, g *ᵥ (f *ᵥ v) = f *ᵥ (g *ᵥ v) := by
    intro v
    have hgw : g *ᵥ (v - Dg K *ᵥ v) = v - Dg K *ᵥ v := hg.2 _ (hkerw v)
    have hfw : g *ᵥ (f *ᵥ (v - Dg K *ᵥ v)) = f *ᵥ (v - Dg K *ᵥ v) :=
      hg.2 _ (by rw [hDf]; exact hkerw v)
    have hgu : f *ᵥ (g *ᵥ (Dg K *ᵥ v)) = g *ᵥ (Dg K *ᵥ v) := by
      rw [hgD, hfD]
    have hv1 : v = Dg K *ᵥ v + (v - Dg K *ᵥ v) := (add_sub_cancel _ _).symm
    have hfv : f *ᵥ v = Dg K *ᵥ v + f *ᵥ (v - Dg K *ᵥ v) := by
      conv_lhs => rw [hv1]
      rw [Matrix.mulVec_add, hfD]
    have hgv : g *ᵥ v = g *ᵥ (Dg K *ᵥ v) + (v - Dg K *ᵥ v) := by
      conv_lhs => rw [hv1]
      rw [Matrix.mulVec_add, hgw]
    rw [hfv, Matrix.mulVec_add, hfw, hgv, Matrix.mulVec_add, hgu]
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hvec _

theorem H0_isQuasisimple : CFSG.Open.IsQuasisimple (H0 (K := K)) :=
  CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv blkEquiv isQuasisimple_SL3

theorem H0_three_dvd : 3 ∣ Nat.card (↥(H0 (K := K)) ⧸ Subgroup.center ↥(H0 (K := K))) := by
  rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv blkEquiv]
  exact three_dvd_quot_SL3

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

end
