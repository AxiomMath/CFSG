module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Matrix CFSG.Open CFSG.SectionRank.ClassicalEven

theorem threeTwoWitness_statedProj_commuting {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (g x : Matrix.GeneralLinearGroup ι K) (hg : g ∈ H) (hx : x ∈ H) (hgg : g * g = 1)
    (hgns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ g) (hx3 : x ^ 3 = 1)
    (hxns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ x) (hc : Commute g x) :
    ThreeTwoWitness (StatedProj H) := by
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  let a : H := ⟨g, hg⟩
  let c' : H := ⟨x, hx⟩
  have hmem : ∀ y : H, π y = 1 →
      ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u = (y : Matrix.GeneralLinearGroup ι K) :=
    fun y hy => (QuotientGroup.eq_one_iff y).1 hy
  have haa : a * a = 1 := Subtype.ext hgg
  have hc3 : c' ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hx3)
  refine ThreeTwoWitness.of_commuting (g := π a) (x := π c') ?_ ?_ ?_ ?_
  · rw [pow_two, ← map_mul, haa, map_one]
  · intro h
    obtain ⟨u, hu⟩ := hmem a h
    exact hgns u hu
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hc3, map_one]
    · intro h
      obtain ⟨u, hu⟩ := hmem c' h
      exact hxns u hu
  · exact Commute.map (show Commute a c' from Subtype.ext hc) π

variable {K : Type} [Field K] {n : ℕ}

@[expose] def sgnVec (k : Fin n) : Fin n ⊕ Fin n → K :=
  fun a => if a = Sum.inl k ∨ a = Sum.inr k then -1 else 1

theorem sgnVec_mul_self (k : Fin n) (a : Fin n ⊕ Fin n) :
    sgnVec (K := K) k a * sgnVec k a = 1 := by
  unfold sgnVec
  split_ifs <;> simp

theorem sgn_symplectic (k : Fin n) :
    (diagonal (sgnVec (K := K) k))ᵀ * fromBlocks 0 1 (-1) 0 * diagonal (sgnVec k) =
      fromBlocks 0 1 (-1) 0 := by
  rw [diagonal_transpose]
  ext (a | a) (b | b) <;> simp only [mul_diagonal, diagonal_mul]
  · simp [fromBlocks]
  · by_cases h : a = b
    · subst h
      simp [fromBlocks, sgnVec]
      split_ifs <;> simp
    · simp [fromBlocks, sgnVec, h]
  · by_cases h : a = b
    · subst h
      simp [fromBlocks, sgnVec]
      split_ifs <;> simp
    · simp [fromBlocks, sgnVec, h]
  · simp [fromBlocks]

@[expose] def glSgn (k : Fin n) : GL (Fin n ⊕ Fin n) K :=
  ⟨diagonal (sgnVec k), diagonal (sgnVec k), by
    rw [diagonal_mul_diagonal]
    convert (diagonal_one : (diagonal fun _ => (1 : K) : Matrix (Fin n ⊕ Fin n) _ K) = 1) using 2
    ext a
    exact sgnVec_mul_self k a, by
    rw [diagonal_mul_diagonal]
    convert (diagonal_one : (diagonal fun _ => (1 : K) : Matrix (Fin n ⊕ Fin n) _ K) = 1) using 2
    ext a
    exact sgnVec_mul_self k a⟩

theorem sgn_rot_commute {k0 k1 : Fin n} (h : k0 ≠ k1) :
    Commute (diagonal (sgnVec (K := K) k1)) (rotMatrix (Sum.inl k0) (Sum.inr k0)) := by
  have h1 : sgnVec (K := K) k1 (Sum.inl k0) = 1 := by simp [sgnVec, h]
  have h2 : sgnVec (K := K) k1 (Sum.inr k0) = 1 := by simp [sgnVec, h]
  show _ * _ = _ * _
  ext a b
  simp only [diagonal_mul, mul_diagonal, rotMatrix, of_apply, rotCol]
  by_cases hb1 : b = Sum.inl k0
  · subst hb1
    by_cases ha : a = Sum.inr k0
    · subst ha; simp [h1, h2]
    · simp [Pi.single_apply, ha]
  by_cases hb2 : b = Sum.inr k0
  · subst hb2
    by_cases ha1 : a = Sum.inl k0
    · subst ha1; simp [h1, h2]
    by_cases ha2 : a = Sum.inr k0
    · subst ha2; simp [h1, h2]
    · simp [Pi.single_apply, ha1, ha2]
  · by_cases hab : a = b
    · subst hab; simp [hb1, hb2, Pi.single_apply]
    · simp [hb1, hb2, Pi.single_apply, hab]

@[expose] def tvMat (k : Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  1 + Matrix.single (Sum.inl k) (Sum.inr k) 1

theorem tvMat_symplectic (k : Fin n) :
    (tvMat (K := K) k)ᵀ * fromBlocks 0 1 (-1) 0 * tvMat k = fromBlocks 0 1 (-1) 0 := by
  simp only [tvMat, transpose_add, transpose_one, transpose_single, add_mul, mul_add, one_mul,
    mul_one]
  ext (a | a) (b | b) <;>
  simp [Matrix.mul_apply, Matrix.single_apply, fromBlocks, Fintype.sum_sum_type,
    Matrix.one_apply] <;>
  by_cases ha : k = a <;> by_cases hb : k = b <;>
    simp [ha, hb, eq_comm, ite_and, Finset.sum_ite_eq] <;> split_ifs <;> simp

theorem tvMat_mul_self (h2 : (1 : K) + 1 = 0) (k : Fin n) : tvMat (K := K) k * tvMat k = 1 := by
  ext (a | a) (b | b) <;>
  simp [tvMat, mul_add, Matrix.mul_apply, Matrix.single_apply, Fintype.sum_sum_type,
    Matrix.one_apply] <;>
  by_cases ha : k = a <;> by_cases hb : k = b <;>
    simp [ha, hb, eq_comm, ite_and, Finset.sum_ite_eq] <;> split_ifs <;> simp [h2]

theorem rotMatrix_apply_of_ne_left {ι : Type} [DecidableEq ι] {i j x : ι} (b : ι) (hxi : x ≠ i)
    (hxj : x ≠ j) : rotMatrix (K := K) i j x b = if x = b then 1 else 0 := by
  simp only [rotMatrix, of_apply, rotCol]
  by_cases hb1 : b = i
  · subst hb1; simp [hxi, hxj]
  by_cases hb2 : b = j
  · subst hb2; simp [hb1, hxi, hxj, Pi.single_apply]
  · simp [hb1, hb2, Pi.single_apply]

theorem rotMatrix_apply_of_ne_right {ι : Type} [DecidableEq ι] {i j y : ι} (a : ι) (hyi : y ≠ i)
    (hyj : y ≠ j) : rotMatrix (K := K) i j a y = if a = y then 1 else 0 := by
  simp only [rotMatrix, of_apply, rotCol]
  simp [hyi, hyj, Pi.single_apply]

theorem tv_rot_commute {k0 k1 : Fin n} (h : k0 ≠ k1) :
    Commute (tvMat (K := K) k1) (rotMatrix (Sum.inl k0) (Sum.inr k0)) := by
  refine Commute.add_left (Commute.one_left _) ?_
  have h1 : (Sum.inr k1 : Fin n ⊕ Fin n) ≠ Sum.inl k0 := Sum.inr_ne_inl
  have h2 : (Sum.inr k1 : Fin n ⊕ Fin n) ≠ Sum.inr k0 := fun e => h (Sum.inr_injective e).symm
  have h3 : (Sum.inl k1 : Fin n ⊕ Fin n) ≠ Sum.inl k0 := fun e => h (Sum.inl_injective e).symm
  have h4 : (Sum.inl k1 : Fin n ⊕ Fin n) ≠ Sum.inr k0 := Sum.inl_ne_inr
  show _ * _ = _ * _
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply]
  simp [ite_and, rotMatrix_apply_of_ne_left b h1 h2, rotMatrix_apply_of_ne_right a h3 h4]
  by_cases ha : a = Sum.inl k1
  · subst ha
    by_cases hb : Sum.inr k1 = b <;> simp [hb]
  · have ha' : ¬ Sum.inl k1 = a := fun e => ha e.symm
    simp [ha, ha']

@[expose] def glTv (h2 : (1 : K) + 1 = 0) (k : Fin n) : GL (Fin n ⊕ Fin n) K :=
  ⟨tvMat k, tvMat k, tvMat_mul_self h2 k, tvMat_mul_self h2 k⟩

theorem glSgn_mem (k : Fin n) : glSgn (K := K) k ∈ StatedSp n K :=
  Subgroup.subset_closure (sgn_symplectic k)

theorem glTv_mem (h2 : (1 : K) + 1 = 0) (k : Fin n) : glTv h2 k ∈ StatedSp n K :=
  Subgroup.subset_closure (tvMat_symplectic k)

theorem rotGL_mem_sp (k : Fin n) :
    rotGL (K := K) (Sum.inl k) (Sum.inr k) ∈ StatedSp n K :=
  Subgroup.subset_closure (rotMatrix_inl_inr_symplectic k)

theorem threeTwoWitness_psp [Finite K] (hn : 2 ≤ n) :
    ThreeTwoWitness (StatedProj (StatedSp n K)) := by
  let k0 : Fin n := ⟨0, by omega⟩
  let k1 : Fin n := ⟨1, by omega⟩
  have hk : k0 ≠ k1 := by simp [k0, k1, Fin.ext_iff]
  have hxns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) u ≠
      rotGL (K := K) (Sum.inl k0) (Sum.inr k0) := fun u hu =>
    mul_scalar_ne (g := 1) (c := Matrix.GeneralLinearGroup.scalar _ u)
      (h := rotGL (K := K) (Sum.inl k0) (Sum.inr k0))
      (a := (Sum.inl k0 : Fin n ⊕ Fin n)) (b := Sum.inr k0) Sum.inl_ne_inr
      (by simp only [Units.val_one, one_mulVec]) (rotMatrix_mulVec_left _ _) ⟨u, rfl⟩
      (by rw [one_mul]; exact hu)
  by_cases h2 : (1 : K) + 1 = 0
  · refine threeTwoWitness_statedProj_commuting (glTv h2 k1) (rotGL (Sum.inl k0) (Sum.inr k0))
      (glTv_mem h2 k1) (rotGL_mem_sp k0) (Units.ext (tvMat_mul_self h2 k1)) ?_
      (rotGL_pow_three _ _) hxns ?_
    · intro u hu
      have e := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl k1) (Sum.inr k1)) hu
      simp [glTv, tvMat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply] at e
    · exact Commute.units_val_iff.1 (tv_rot_commute hk)
  · refine threeTwoWitness_statedProj_commuting (glSgn k1) (rotGL (Sum.inl k0) (Sum.inr k0))
      (glSgn_mem k1) (rotGL_mem_sp k0) (Units.ext ?_) ?_ (rotGL_pow_three _ _) hxns ?_
    · show diagonal (sgnVec (K := K) k1) * diagonal (sgnVec k1) = 1
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      ext a
      exact sgnVec_mul_self k1 a
    · intro u hu
      have e1 := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl k1) (Sum.inl k1)) hu
      have e0 := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl k0) (Sum.inl k0)) hu
      simp [glSgn, sgnVec, hk, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply] at e1 e0
      have := congrArg Units.val (e1.symm.trans e0)
      rw [Units.val_neg, Units.val_one] at this
      exact h2 (by linear_combination -this)
    · exact Commute.units_val_iff.1 (sgn_rot_commute hk)

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
