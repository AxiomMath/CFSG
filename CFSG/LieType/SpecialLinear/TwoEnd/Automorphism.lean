module

public import CFSG.LieType.SpecialLinear.TwoEnd.Fix
public import CFSG.LieType.SpecialLinear.Block222.Borel.BlockEmbedProof

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.ComponentClassification

noncomputable section

variable {F : Type} [Field F]

section Mid

variable (m : ℕ) (F : Type) [Field F]

theorem midGL_mul_inv_block {A : GL (Fin (m+3)) F} (hA : IsUpperGL A) :
    (Matrix.of (fun (i j : Fin (m+1)) =>
        (A : Matrix (Fin (m+3)) (Fin (m+3)) F) i.castSucc.succ j.castSucc.succ) *
      Matrix.of (fun (i j : Fin (m+1)) =>
        ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F)
          i.castSucc.succ j.castSucc.succ)) =
      (1 : Matrix (Fin (m+1)) (Fin (m+1)) F) := by
  ext i j
  have hMN : (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
      ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hsum := congrFun (congrFun hMN (Fin.succ (Fin.castSucc i)))
    (Fin.succ (Fin.castSucc j))
  rw [Matrix.mul_apply, Matrix.one_apply] at hsum
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ] at hsum
  simp only [Fin.castSucc_zero] at hsum
  have h0 : (0 : Fin (m+3)) < Fin.succ (Fin.castSucc i) := by simp
  have hlast : Fin.succ (Fin.castSucc j) < (Fin.last (m+2) : Fin (m+3)) := by
    rw [Fin.lt_def]
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    omega
  rw [hA _ _ h0, zero_mul, isUpperGL_inv (F := F) (n := m+3) (A := A) hA _ _ hlast,
    mul_zero, add_zero] at hsum
  simp only [Matrix.mul_apply, Matrix.one_apply]
  simpa using hsum

@[expose] noncomputable def midGL (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    GL (Fin (m+1)) F :=
  let M : Matrix (Fin (m+3)) (Fin (m+3)) F := (A : Matrix (Fin (m+3)) (Fin (m+3)) F)
  let N : Matrix (Fin (m+3)) (Fin (m+3)) F :=
    ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F)
  let B : Matrix (Fin (m+1)) (Fin (m+1)) F :=
    fun i j => M i.castSucc.succ j.castSucc.succ
  let B' : Matrix (Fin (m+1)) (Fin (m+1)) F :=
    fun i j => N i.castSucc.succ j.castSucc.succ
  Units.mkOfMulEqOne B B' (midGL_mul_inv_block (m := m) (F := F) hA)

@[simp] theorem coe_midGL (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    ((midGL m F A hA : GL (Fin (m+1)) F) : Matrix (Fin (m+1)) (Fin (m+1)) F) =
      fun i j => (A : Matrix (Fin (m+3)) (Fin (m+3)) F) i.castSucc.succ j.castSucc.succ :=
  rfl

@[simp] theorem coe_midGL_inv (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    (((midGL m F A hA)⁻¹ : GL (Fin (m+1)) F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F) =
      fun i j => ((A⁻¹ : GL (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) i.castSucc.succ j.castSucc.succ :=
  rfl

theorem isUpperGL_midGL {A : GL (Fin (m+3)) F} (hA : IsUpperGL A) :
    IsUpperGL (midGL m F A hA) := by
  intro i j hji
  rw [coe_midGL]
  refine hA _ _ ?_
  rw [Fin.lt_def] at hji ⊢
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

@[expose] def e131 : Fin 1 ⊕ (Fin (m+1) ⊕ Fin 1) ≃ Fin (m+3) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv (m := m+1) (n := 1))).trans
    ((finSumFinEquiv (m := 1) (n := (m+1)+1)).trans (finCongr (by omega)))

theorem e131_inl (a : Fin 1) : e131 m (Sum.inl a) = (0 : Fin (m+3)) := by
  apply Fin.ext
  simp [e131]

theorem e131_inr_inl (i : Fin (m+1)) :
    e131 m (Sum.inr (Sum.inl i)) = i.castSucc.succ := by
  apply Fin.ext
  simp [e131]

theorem e131_inr_inr (k : Fin 1) :
    e131 m (Sum.inr (Sum.inr k)) = (Fin.last (m+2) : Fin (m+3)) := by
  apply Fin.ext
  simp [e131, Fin.val_last]

@[expose] def rev131 {m : ℕ} (x : Fin 1 ⊕ (Fin (m+1) ⊕ Fin 1)) :
    Fin 1 ⊕ (Fin (m+1) ⊕ Fin 1) :=
  match x with
  | Sum.inl a => Sum.inr (Sum.inr (Fin.rev a))
  | Sum.inr (Sum.inl s) => Sum.inr (Sum.inl (Fin.rev s))
  | Sum.inr (Sum.inr k) => Sum.inl (Fin.rev k)

theorem e131_rev {m : ℕ} (x : Fin 1 ⊕ (Fin (m+1) ⊕ Fin 1)) :
    Fin.rev (e131 m x) = e131 m (rev131 x) := by
  rcases x with a | (s | k)
  · rw [rev131, e131_inl, e131_inr_inr]
    apply Fin.ext
    simp [Fin.val_last]
  · rw [rev131, e131_inr_inl, e131_inr_inl]
    apply Fin.ext
    simp [Fin.val_rev]
    omega
  · rw [rev131, e131_inr_inr, e131_inl]
    apply Fin.ext
    simp

theorem reindex131_apply (M : Matrix (Fin (m+3)) (Fin (m+3)) F)
    (x y : Fin 1 ⊕ (Fin (m+1) ⊕ Fin 1)) :
    (Matrix.reindexAlgEquiv F F (e131 m).symm) M x y = M (e131 m x) (e131 m y) := by
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]

@[expose] def b131_11 {m : ℕ} {F : Type} [Field F] (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    Matrix (Fin 1) (Fin 1) F :=
  fun i j => A (e131 m (Sum.inl i)) (e131 m (Sum.inl j))

@[expose] def b131_12 {m : ℕ} {F : Type} [Field F] (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    Matrix (Fin 1) ((Fin (m+1)) ⊕ Fin 1) F :=
  fun i j => A (e131 m (Sum.inl i)) (e131 m (Sum.inr j))

@[expose] def b131_21 {m : ℕ} {F : Type} [Field F] (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    Matrix ((Fin (m+1)) ⊕ Fin 1) (Fin 1) F :=
  fun i j => A (e131 m (Sum.inr i)) (e131 m (Sum.inl j))

@[expose] def b131_22a {m : ℕ} {F : Type} [Field F] (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    Matrix (Fin (m+1)) (Fin (m+1)) F :=
  fun i j => A (e131 m (Sum.inr (Sum.inl i))) (e131 m (Sum.inr (Sum.inl j)))

@[expose] def b131_22b {m : ℕ} {F : Type} [Field F] (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    Matrix (Fin (m+1)) (Fin 1) F :=
  fun i j => A (e131 m (Sum.inr (Sum.inl i))) (e131 m (Sum.inr (Sum.inr j)))

@[expose] def b131_22c {m : ℕ} {F : Type} [Field F] (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    Matrix (Fin 1) (Fin (m+1)) F :=
  fun i j => A (e131 m (Sum.inr (Sum.inr i))) (e131 m (Sum.inr (Sum.inl j)))

@[expose] def b131_22d {m : ℕ} {F : Type} [Field F] (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    Matrix (Fin 1) (Fin 1) F :=
  fun i j => A (e131 m (Sum.inr (Sum.inr i))) (e131 m (Sum.inr (Sum.inr j)))

theorem reindex131_eq_fromBlocks (A : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    (Matrix.reindexAlgEquiv F F (e131 m).symm) A =
      Matrix.fromBlocks (b131_11 A) (b131_12 A) (b131_21 A)
        (Matrix.fromBlocks (b131_22a A) (b131_22b A) (b131_22c A) (b131_22d A)) := by
  ext x y
  rw [reindex131_apply]
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, b131_11, b131_12, b131_21, b131_22a, b131_22b, b131_22c,
      b131_22d]

theorem b131_21_eq_zero (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    b131_21 (A : Matrix (Fin (m+3)) (Fin (m+3)) F) = 0 := by
  ext x j
  rcases x with s | k
  · rw [b131_21, Matrix.zero_apply]
    refine hA _ _ ?_
    rw [e131_inl, e131_inr_inl, Fin.lt_def]
    simp
  · rw [b131_21, Matrix.zero_apply]
    refine hA _ _ ?_
    rw [e131_inl, e131_inr_inr, Fin.lt_def]
    simp

theorem b131_22c_eq_zero (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    b131_22c (A : Matrix (Fin (m+3)) (Fin (m+3)) F) = 0 := by
  ext k j
  rw [b131_22c, Matrix.zero_apply]
  refine hA _ _ ?_
  rw [e131_inr_inl, e131_inr_inr, Fin.lt_def]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  omega

theorem reindex131_eq_fromBlocks' (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    (Matrix.reindexAlgEquiv F F (e131 m).symm)
        (A : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      Matrix.fromBlocks (b131_11 (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
        (b131_12 (A : Matrix (Fin (m+3)) (Fin (m+3)) F)) 0
        (Matrix.fromBlocks (b131_22a (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
          (b131_22b (A : Matrix (Fin (m+3)) (Fin (m+3)) F)) 0
          (b131_22d (A : Matrix (Fin (m+3)) (Fin (m+3)) F))) := by
  rw [reindex131_eq_fromBlocks, b131_21_eq_zero m F A hA, b131_22c_eq_zero m F A hA]

theorem b131_11_eq (A : Matrix (Fin (m+3)) (Fin (m+3)) F) (i j : Fin 1) :
    b131_11 A i j = A 0 0 := by
  simp [b131_11, e131_inl]

theorem b131_22d_eq (A : Matrix (Fin (m+3)) (Fin (m+3)) F) (i j : Fin 1) :
    b131_22d A i j = A (Fin.last (m+2)) (Fin.last (m+2)) := by
  simp [b131_22d, e131_inr_inr]

theorem b131_22a_eq_midGL (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    b131_22a (A : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      ((midGL m F A hA : GL (Fin (m+1)) F) : Matrix (Fin (m+1)) (Fin (m+1)) F) := by
  ext i j
  simp [b131_22a, coe_midGL, e131_inr_inl]

theorem b131_22a_inv_eq_midGL_inv (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    b131_22a ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      (((midGL m F A hA)⁻¹ : GL (Fin (m+1)) F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F) := by
  rw [b131_22a_eq_midGL (m := m) (F := F) (A := A⁻¹) (isUpperGL_inv (F := F) (A := A) hA)]
  ext i j
  rw [coe_midGL, coe_midGL_inv]

theorem b131_11_mul_inv (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    b131_11 (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
      b131_11 ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) = 1 := by
  have hMN : (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
      ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hsum := congrFun (congrFun hMN 0) 0
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hsum
  rw [Finset.sum_eq_single 0] at hsum
  · ext i j
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi
    subst hj
    simpa [b131_11_eq, Matrix.mul_apply] using hsum
  · intro k _ hk
    rw [isUpperGL_inv (F := F) (n := m+3) (A := A) hA k 0 (Fin.pos_iff_ne_zero.mpr hk), mul_zero]
  · intro h0
    simp at h0

theorem b131_22d_mul_inv (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    b131_22d (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
      b131_22d ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) = 1 := by
  have hMN : (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
      ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hsum := congrFun (congrFun hMN (Fin.last (m+2))) (Fin.last (m+2))
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hsum
  rw [Finset.sum_eq_single (Fin.last (m+2))] at hsum
  · ext i j
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi
    subst hj
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simpa [b131_22d_eq] using hsum
  · intro k _ hk
    rw [hA _ _ (Fin.lt_last_iff_ne_last.mpr hk), zero_mul]
  · intro hlast
    simp at hlast

@[simp] theorem one_fin_one_apply (i j : Fin 1) :
    (1 : Matrix (Fin 1) (Fin 1) F) i j = 1 := by
  rw [Matrix.one_apply, if_pos (Subsingleton.elim i j)]

theorem reindex_embedMid (g : SpecialLinearGroup (Fin (m+1)) F) :
    (Matrix.reindexAlgEquiv F F (e131 m).symm)
        ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
          Matrix (Fin (m+3)) (Fin (m+3)) F) =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
        (Matrix.fromBlocks (g : Matrix (Fin (m+1)) (Fin (m+1)) F) 0 0
          (1 : Matrix (Fin 1) (Fin 1) F)) := by
  ext x y
  rw [reindex131_apply]
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, e131_inl, e131_inr_inl, e131_inr_inr,
      embedMid_zero_apply, embedMid_last_apply, embedMid_apply_zero, embedMid_apply_last,
      coe_embedMid_succ_succ]

theorem reindex_embedMid_apply {m : ℕ} {F : Type} [Field F] (g : SpecialLinearGroup (Fin (m+1)) F)
    (x y : Fin 1 ⊕ (Fin (m+1) ⊕ Fin 1)) :
    ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) (e131 m x) (e131 m y) =
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
        (Matrix.fromBlocks (g : Matrix (Fin (m+1)) (Fin (m+1)) F) 0 0
          (1 : Matrix (Fin 1) (Fin 1) F))) x y := by
  have h := congrFun (congrFun (reindex_embedMid m F g) x) y
  rw [reindex131_apply] at h
  exact h

theorem reindex_borelGraph_embedMid (g : SpecialLinearGroup (Fin (m+1)) F) :
    (Matrix.reindexAlgEquiv F F (e131 m).symm)
        ((borelGraph (m+3) F (embedMid m F g) : SpecialLinearGroup (Fin (m+3)) F) :
          Matrix (Fin (m+3)) (Fin (m+3)) F) =
      (Matrix.reindexAlgEquiv F F (e131 m).symm)
        ((embedMid m F (borelGraph (m+1) F g) : SpecialLinearGroup (Fin (m+3)) F) :
          Matrix (Fin (m+3)) (Fin (m+3)) F) := by
  ext x y
  rw [reindex131_apply, reindex131_apply]
  rw [coe_borelGraph_apply]
  have hinv : (embedMid m F g)⁻¹ = embedMid m F g⁻¹ :=
    (map_inv (embedMid m F) g).symm
  rw [hinv]
  rw [e131_rev y, e131_rev x]
  rw [reindex_embedMid_apply (g⁻¹) (rev131 y) (rev131 x)]
  rw [reindex_embedMid_apply (borelGraph (m+1) F g) x y]
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp [rev131, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, coe_borelGraph_apply]

theorem borelGraph_embedMid (g : SpecialLinearGroup (Fin (m+1)) F) :
    borelGraph (m+3) F (embedMid m F g) =
      embedMid m F (borelGraph (m+1) F g) := by
  apply Subtype.ext
  apply (Matrix.reindexAlgEquiv F F (e131 m).symm).injective
  exact reindex_borelGraph_embedMid m F g

theorem reindex131_map {m : ℕ} {F : Type} [Field F] (σ : F ≃+* F)
    (M : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    (Matrix.reindexAlgEquiv F F (e131 m).symm) (M.map σ) =
      ((Matrix.reindexAlgEquiv F F (e131 m).symm) M).map σ := by
  ext x y
  rw [reindex131_apply, Matrix.map_apply, Matrix.map_apply, reindex131_apply]

section UpperMul

variable {m : ℕ} {F : Type} [Field F]

theorem fin_pos_castSucc_succ {m : ℕ} (i : Fin (m+1)) :
    (0 : Fin (m+3)) < i.castSucc.succ := by simp

theorem fin_castSucc_succ_lt_last {m : ℕ} (i : Fin (m+1)) :
    (i.castSucc.succ : Fin (m+3)) < Fin.last (m+2) := by
  rw [Fin.lt_def]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  have := i.isLt
  omega

theorem fin_pos_last {m : ℕ} : (0 : Fin (m+3)) < Fin.last (m+2) := by
  rw [Fin.lt_def]
  simp [Fin.val_last]

theorem IsTwoEndZero.mul_left_of_isUpperTriangular
    {N : Matrix (Fin (m+3)) (Fin (m+3)) F} (hN : IsTwoEndZero N)
    {A : Matrix (Fin (m+3)) (Fin (m+3)) F} (hA : A.IsUpperTriangular) :
    IsTwoEndZero (A * N) := by
  refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
  · rw [Matrix.mul_apply]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · refine Finset.sum_eq_zero fun k _ => ?_
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
      · rw [hN.1, mul_zero]
      · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
        · rw [hN.2 _ _ (by simp) (by simp), mul_zero]
        · rw [hN.2 _ _ (by simp) (by simp), mul_zero]
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · refine Finset.sum_eq_zero fun k _ => ?_
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
        · have hzero : A i.castSucc.succ 0 = 0 := hA (fin_pos_castSucc_succ i)
          rw [hzero, zero_mul]
        · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
          · rw [hN.2 _ _ (by simp) (by simp), mul_zero]
          · rw [hN.2 _ _ (by simp) (by simp), mul_zero]
      · refine Finset.sum_eq_zero fun k _ => ?_
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
        · have hzero : A (Fin.last (m+2)) 0 = 0 := hA (fin_pos_last)
          rw [Fin.succ_last, hzero, zero_mul]
        · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
          · have hzero : A (Fin.last (m+2)) k.castSucc.succ = 0 :=
              hA (fin_castSucc_succ_lt_last k)
            rw [Fin.succ_last, hzero, zero_mul]
          · rw [Fin.succ_last, hN.1, mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · have hzero : A i 0 = 0 := hA (Fin.pos_iff_ne_zero.mpr hi)
      rw [hzero, zero_mul]
    · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
      · rw [hN.2 _ _ (by simp) hj, mul_zero]
      · rw [hN.2 _ _ (by simp) hj, mul_zero]

theorem IsTwoEndZero.mul_right_of_isUpperTriangular
    {N : Matrix (Fin (m+3)) (Fin (m+3)) F} (hN : IsTwoEndZero N)
    {A : Matrix (Fin (m+3)) (Fin (m+3)) F} (hA : A.IsUpperTriangular) :
    IsTwoEndZero (N * A) := by
  refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
  · rw [Matrix.mul_apply]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · refine Finset.sum_eq_zero fun k _ => ?_
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
      · rw [hN.1, zero_mul]
      · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
        · have hzero : A k.castSucc.succ 0 = 0 := hA (fin_pos_castSucc_succ k)
          rw [hzero, mul_zero]
        · have hzero : A (Fin.last (m+2)) 0 = 0 := hA (fin_pos_last)
          rw [Fin.succ_last, hzero, mul_zero]
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · refine Finset.sum_eq_zero fun k _ => ?_
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
        · rw [hN.2 _ _ (by simp) (by simp), zero_mul]
        · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
          · rw [hN.2 _ _ (by simp) (by simp), zero_mul]
          · have hzero : A (Fin.last (m+2)) i.castSucc.succ = 0 :=
              hA (fin_castSucc_succ_lt_last i)
            rw [Fin.succ_last, hzero, mul_zero]
      · refine Finset.sum_eq_zero fun k _ => ?_
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
        · rw [hN.2 _ _ (by simp) (by simp), zero_mul]
        · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
          · rw [hN.2 _ _ (by simp) (by simp), zero_mul]
          · rw [Fin.succ_last, hN.1, zero_mul]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · rw [hN.2 _ _ hi (by simp), zero_mul]
    · rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
      · rw [hN.2 _ _ hi (by simp), zero_mul]
      · have hzero : A (Fin.last (m+2)) j = 0 := hA (Fin.lt_last_iff_ne_last.mpr hj)
        rw [Fin.succ_last, hzero, mul_zero]

end UpperMul

theorem blockUpper131_sub_one {m : ℕ} {F : Type} [Field F]
    (B : Matrix (Fin 1) ((Fin (m+1)) ⊕ Fin 1) F) (E : Matrix (Fin (m+1)) (Fin 1) F) :
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) B 0
      (Matrix.fromBlocks (1 : Matrix (Fin (m+1)) (Fin (m+1)) F) E 0
        (1 : Matrix (Fin 1) (Fin 1) F)) - 1 =
    Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) F) B 0
      (Matrix.fromBlocks (0 : Matrix (Fin (m+1)) (Fin (m+1)) F) E 0
        (0 : Matrix (Fin 1) (Fin 1) F)) := by
  ext x y
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.sub_apply]

theorem isTwoEndZero_of_reindex_blockStrictUpper {m : ℕ} {F : Type} [Field F]
    {M : Matrix (Fin (m+3)) (Fin (m+3)) F}
    {B : Matrix (Fin 1) ((Fin (m+1)) ⊕ Fin 1) F} {E : Matrix (Fin (m+1)) (Fin 1) F}
    (h : (Matrix.reindexAlgEquiv F F (e131 m).symm) M =
      Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) F) B 0
        (Matrix.fromBlocks (0 : Matrix (Fin (m+1)) (Fin (m+1)) F) E 0
          (0 : Matrix (Fin 1) (Fin 1) F))) :
    IsTwoEndZero M := by
  refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
  · have hx : (Matrix.reindexAlgEquiv F F (e131 m).symm) M
        ((e131 m).symm i) ((e131 m).symm i) = M i i := by
      rw [reindex131_apply]
      simp
    rw [← hx, h]
    rcases (e131 m).symm i with a | (s | k) <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  · have hx : (Matrix.reindexAlgEquiv F F (e131 m).symm) M
        ((e131 m).symm i) ((e131 m).symm j) = M i j := by
      rw [reindex131_apply]
      simp
    rw [← hx, h]
    rcases hx' : (e131 m).symm i with a | (s | k)
    · exfalso
      apply hi
      rw [← (e131 m).apply_symm_apply i, hx', e131_inl]
    · rcases hy' : (e131 m).symm j with b | (t | l)
      · simp [Matrix.fromBlocks_apply₂₁]
      · simp [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁]
      · exfalso
        apply hj
        rw [← (e131 m).apply_symm_apply j, hy', e131_inr_inr]
    · rcases hy' : (e131 m).symm j with b | (t | l)
      · simp [Matrix.fromBlocks_apply₂₁]
      · simp [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁]
      · exfalso
        apply hj
        rw [← (e131 m).apply_symm_apply j, hy', e131_inr_inr]

end Mid

section Preservation

variable (m : ℕ) (F : Type) [Field F]

theorem isUpperTriangular_of_isUpperGL {A : GL (Fin (m+3)) F} (hA : IsUpperGL A) :
    (A : Matrix (Fin (m+3)) (Fin (m+3)) F).IsUpperTriangular := by
  intro i j hji
  exact hA i j hji

theorem isTwoEndZero_slFieldAut (σ : F ≃+* F)
    {q : SpecialLinearGroup (Fin (m+3)) F}
    (hq : IsTwoEndZero ((q : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1)) :
    IsTwoEndZero
      (((CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ q :
        SpecialLinearGroup (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by
  have hcoe : ((CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ q :
      SpecialLinearGroup (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      (q : Matrix (Fin (m+3)) (Fin (m+3)) F).map σ.toRingHom := by
    ext i j
    exact CatalogueBHigherLinearField.slFieldEquiv_entry (Fin (m+3)) σ q i j
  rw [hcoe]
  have hsub : ((q : Matrix (Fin (m+3)) (Fin (m+3)) F).map σ.toRingHom) - 1 =
      ((q : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1).map σ.toRingHom := by
    rw [Matrix.map_sub _ (map_sub σ.toRingHom),
      Matrix.map_one _ (map_zero σ.toRingHom) (map_one σ.toRingHom)]
  rw [hsub]
  exact hq.map σ.toRingHom

theorem isTwoEndZero_borelGraph {q : SpecialLinearGroup (Fin (m+3)) F}
    (hq : q ∈ twoEndRadical m F) :
    IsTwoEndZero
      (((borelGraph (m+3) F q : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by
  have hqinv : q⁻¹ ∈ twoEndRadical m F := (twoEndRadical m F).inv_mem hq
  have hq' := (mem_twoEndRadical (m := m) (F := F)).mp hqinv
  refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
  · rw [Matrix.sub_apply, coe_borelGraph_apply, hq'.1, Matrix.one_apply_eq, sub_self]
  · rw [Matrix.sub_apply, coe_borelGraph_apply]
    have hrevj : Fin.rev j ≠ 0 := by
      intro h
      apply hj
      have h' : Fin.rev j = Fin.rev (Fin.last (m+2)) := by rw [h, Fin.rev_last]
      exact Fin.rev_injective h'
    have hrevi : Fin.rev i ≠ Fin.last (m+2) := by
      intro h
      apply hi
      have h' : Fin.rev i = Fin.rev (0 : Fin (m+3)) := by rw [h, Fin.rev_zero]
      exact Fin.rev_injective h'
    rw [hq'.2 (Fin.rev j) (Fin.rev i) hrevj hrevi]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hrevne : Fin.rev j ≠ Fin.rev i := fun h => hij (Fin.rev_injective h).symm
      simp [hij, hrevne]

theorem isTwoEndZero_slConjugation (A : GL (Fin (m+3)) F) (hA : IsUpperGL A)
    {q : SpecialLinearGroup (Fin (m+3)) F} (hq : q ∈ twoEndRadical m F) :
    IsTwoEndZero
      (((CatalogueBHigherLinearAction.slConjugation (m+3) F A q :
        SpecialLinearGroup (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by
  have hqN : IsTwoEndZero ((q : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := hq
  have hAmat : (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
      ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hcoe : ((CatalogueBHigherLinearAction.slConjugation (m+3) F A q :
      SpecialLinearGroup (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
        (q : Matrix (Fin (m+3)) (Fin (m+3)) F) *
        ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation
      (n := m+3) (K := F) A q
  rw [hcoe]
  have hsub : (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
        (q : Matrix (Fin (m+3)) (Fin (m+3)) F) *
        ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1 =
      (A : Matrix (Fin (m+3)) (Fin (m+3)) F) *
        ((q : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
        ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAmat]
  rw [hsub]
  exact (hqN.mul_left_of_isUpperTriangular
    (isUpperTriangular_of_isUpperGL m F hA)).mul_right_of_isUpperTriangular
      (isUpperTriangular_of_isUpperGL m F (isUpperGL_inv (F := F) (A := A) hA))

theorem mem_slFieldAut_twoEndRadical (σ : F ≃+* F)
    {q : SpecialLinearGroup (Fin (m+3)) F} (hq : q ∈ twoEndRadical m F) :
    CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ q ∈ twoEndRadical m F :=
  isTwoEndZero_slFieldAut m F σ hq

theorem mem_borelGraph_twoEndRadical {q : SpecialLinearGroup (Fin (m+3)) F}
    (hq : q ∈ twoEndRadical m F) :
    borelGraph (m+3) F q ∈ twoEndRadical m F :=
  isTwoEndZero_borelGraph m F hq

theorem mem_slConjugation_twoEndRadical (A : GL (Fin (m+3)) F) (hA : IsUpperGL A)
    {q : SpecialLinearGroup (Fin (m+3)) F} (hq : q ∈ twoEndRadical m F) :
    CatalogueBHigherLinearAction.slConjugation (m+3) F A q ∈ twoEndRadical m F :=
  isTwoEndZero_slConjugation m F A hA hq

theorem map_slFieldAut_twoEndRadical (σ : F ≃+* F) :
    (twoEndRadical m F).map
        (CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ).toMonoidHom =
      twoEndRadical m F := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro q hq
    exact mem_slFieldAut_twoEndRadical m F σ hq
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨
      CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ⁻¹ q, ?_, ?_⟩
    · exact mem_slFieldAut_twoEndRadical m F σ⁻¹ hq
    · have hcomp : CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ *
          CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      change (CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ *
          CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ⁻¹) q = q
      rw [hcomp]
      rfl

theorem map_slConjugation_twoEndRadical (A : GL (Fin (m+3)) F) (hA : IsUpperGL A) :
    (twoEndRadical m F).map
        (CatalogueBHigherLinearAction.slConjugation (m+3) F A).toMonoidHom =
      twoEndRadical m F := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro q hq
    exact mem_slConjugation_twoEndRadical m F A hA hq
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨
      CatalogueBHigherLinearAction.slConjugation (m+3) F A⁻¹ q, ?_, ?_⟩
    · exact mem_slConjugation_twoEndRadical m F A⁻¹
        (isUpperGL_inv (F := F) (A := A) hA) hq
    · have hcomp : CatalogueBHigherLinearAction.slConjugation (m+3) F A *
          CatalogueBHigherLinearAction.slConjugation (m+3) F A⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      change (CatalogueBHigherLinearAction.slConjugation (m+3) F A *
          CatalogueBHigherLinearAction.slConjugation (m+3) F A⁻¹) q = q
      rw [hcomp]
      rfl

theorem map_borelGraph_twoEndRadical :
    (twoEndRadical m F).map (borelGraph (m+3) F).toMonoidHom =
      twoEndRadical m F := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro q hq
    exact mem_borelGraph_twoEndRadical m F hq
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨borelGraph (m+3) F q, ?_, ?_⟩
    · exact mem_borelGraph_twoEndRadical m F hq
    · simpa [MulAut.mul_apply] using
        congrArg (fun f : MulAut (SpecialLinearGroup (Fin (m+3)) F) => f q)
          (borelGraph_mul_self (m+3) (F := F))

theorem map_borelGraph_pow_twoEndRadical (ε : ℕ) :
    (twoEndRadical m F).map (((borelGraph (m+3) F) ^ ε).toMonoidHom) =
      twoEndRadical m F := by
  induction ε with
  | zero =>
      rw [pow_zero]
      rw [show MulEquiv.toMonoidHom (1 : MulAut (SpecialLinearGroup (Fin (m+3)) F)) =
          MonoidHom.id _ from MonoidHom.ext fun x => MulAut.one_apply _ x]
      rw [Subgroup.map_id]
  | succ n ih =>
      rw [pow_succ]
      rw [show (((borelGraph (m+3) F) ^ n * borelGraph (m+3) F)).toMonoidHom =
          ((borelGraph (m+3) F) ^ n).toMonoidHom.comp
            (borelGraph (m+3) F).toMonoidHom from rfl]
      rw [← Subgroup.map_map, map_borelGraph_twoEndRadical m F, ih]

theorem map_stdAut_zero_twoEndRadical (A : GL (Fin (m+3)) F) (hA : IsUpperGL A)
    (σ : F ≃+* F) :
    (twoEndRadical m F).map
        (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom =
      twoEndRadical m F := by
  rw [show (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom =
      (CatalogueBHigherLinearAction.slConjugation (m+3) F A).toMonoidHom.comp
        (CatalogueBHigherLinearField.slFieldAut (Fin (m+3)) F σ).toMonoidHom from by
    rw [CFSG.QuasithinUnique.K1.stdAut, pow_zero, mul_one]
    rfl,
    ← Subgroup.map_map, map_slFieldAut_twoEndRadical m F σ,
    map_slConjugation_twoEndRadical m F A hA]

theorem twoEndRadical_map_borelStd (A : GL (Fin (m+3)) F) (hA : IsUpperGL A)
    (σ : F ≃+* F) (ε : ℕ) :
    (twoEndRadical m F).map (borelStd (m+3) F A σ ε).toMonoidHom =
      twoEndRadical m F := by
  rw [borelStd]
  rw [show ((CFSG.QuasithinUnique.K1.stdAut A σ 0 * borelGraph (m+3) F ^ ε)).toMonoidHom =
      (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom.comp
        ((borelGraph (m+3) F ^ ε)).toMonoidHom from rfl]
  rw [← Subgroup.map_map, map_borelGraph_pow_twoEndRadical m F ε,
    map_stdAut_zero_twoEndRadical m F A hA σ]

theorem stdAut_zero_embedMid {A : GL (Fin (m+3)) F} (hA : IsUpperGL A)
    (σ : F ≃+* F) (g : SpecialLinearGroup (Fin (m+1)) F) :
    (embedMid m F (CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g))⁻¹ *
      CFSG.QuasithinUnique.K1.stdAut A σ 0 (embedMid m F g) ∈ twoEndRadical m F := by
  let R := Matrix.reindexAlgEquiv F F (e131 m).symm
  let s : Matrix (Fin (m+1)) (Fin (m+1)) F :=
    (g : Matrix (Fin (m+1)) (Fin (m+1)) F).map σ
  let β : Matrix (Fin (m+1)) (Fin (m+1)) F :=
    ((CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g :
      SpecialLinearGroup (Fin (m+1)) F) : Matrix (Fin (m+1)) (Fin (m+1)) F)
  let β' : Matrix (Fin (m+1)) (Fin (m+1)) F :=
    (((CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g)⁻¹ :
      SpecialLinearGroup (Fin (m+1)) F) : Matrix (Fin (m+1)) (Fin (m+1)) F)
  have hβeq : β =
      b131_22a (A : Matrix (Fin (m+3)) (Fin (m+3)) F) * s *
        b131_22a ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) := by
    simp only [β, s, CFSG.QuasithinUnique.K1.coe_stdAut_zero,
      b131_22a_eq_midGL (m := m) (F := F) A hA,
      b131_22a_inv_eq_midGL_inv (m := m) (F := F) A hA]
  have hβ1 : (1 : Matrix (Fin 1) (Fin 1) F) =
      b131_11 (A : Matrix (Fin (m+3)) (Fin (m+3)) F) * 1 *
        b131_11 ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) := by
    simpa using (b131_11_mul_inv (m := m) (F := F) A hA).symm
  have hβ3 : (1 : Matrix (Fin 1) (Fin 1) F) =
      b131_22d (A : Matrix (Fin (m+3)) (Fin (m+3)) F) * 1 *
        b131_22d ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) := by
    simpa using (b131_22d_mul_inv (m := m) (F := F) A hA).symm
  have hβ2' : β' * β = 1 := by
    change ((((CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g)⁻¹ *
      CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g :
      SpecialLinearGroup (Fin (m+1)) F)) : Matrix (Fin (m+1)) (Fin (m+1)) F) = 1
    rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hβ2'' : β * β' = 1 := by
    change (((CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g *
      (CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g)⁻¹ :
      SpecialLinearGroup (Fin (m+1)) F)) : Matrix (Fin (m+1)) (Fin (m+1)) F) = 1
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hβ1' : (1 : Matrix (Fin 1) (Fin 1) F) * 1 = 1 := by simp
  have hβ3' : (1 : Matrix (Fin 1) (Fin 1) F) * 1 = 1 := by simp
  have hβ1'' : (1 : Matrix (Fin 1) (Fin 1) F) * 1 = 1 := by simp
  have hβ3'' : (1 : Matrix (Fin 1) (Fin 1) F) * 1 = 1 := by simp
  obtain ⟨B, E, hBE⟩ := exists_fromBlocks_quotient (F := F)
    (A₁ := b131_11 (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₁₂ := b131_12 (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₂ := b131_22a (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₂₃ := b131_22b (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₃ := b131_22d (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₁' := b131_11 ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₁₂' := b131_12 ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₂' := b131_22a ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₂₃' := b131_22b ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (A₃' := b131_22d ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))
    (S₁ := (1 : Matrix (Fin 1) (Fin 1) F)) (S₂ := s)
    (S₃ := (1 : Matrix (Fin 1) (Fin 1) F))
    (β₁ := (1 : Matrix (Fin 1) (Fin 1) F)) (β₁' := (1 : Matrix (Fin 1) (Fin 1) F))
    (β₂ := β) (β₂' := β') (β₃ := (1 : Matrix (Fin 1) (Fin 1) F))
    (β₃' := (1 : Matrix (Fin 1) (Fin 1) F))
    hβ1 hβeq hβ3 hβ1' hβ2' hβ3' hβ1'' hβ2'' hβ3''
  have hRX : R ((CFSG.QuasithinUnique.K1.stdAut A σ 0 (embedMid m F g) :
      SpecialLinearGroup (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      Matrix.fromBlocks (b131_11 (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
        (b131_12 (A : Matrix (Fin (m+3)) (Fin (m+3)) F)) 0
        (Matrix.fromBlocks (b131_22a (A : Matrix (Fin (m+3)) (Fin (m+3)) F))
          (b131_22b (A : Matrix (Fin (m+3)) (Fin (m+3)) F)) 0
          (b131_22d (A : Matrix (Fin (m+3)) (Fin (m+3)) F))) *
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
        (Matrix.fromBlocks s 0 0 (1 : Matrix (Fin 1) (Fin 1) F)) *
      Matrix.fromBlocks (b131_11 ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))
        (b131_12 ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F)) 0
        (Matrix.fromBlocks (b131_22a ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))
          (b131_22b ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F)) 0
          (b131_22d ((A⁻¹ : GL (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F))) := by
    rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    rw [map_mul, map_mul]
    rw [reindex131_eq_fromBlocks' (m := m) (F := F) A hA]
    rw [reindex131_map]
    rw [reindex_embedMid]
    have hSmap : ((Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
        (Matrix.fromBlocks (g : Matrix (Fin (m+1)) (Fin (m+1)) F) 0 0
          (1 : Matrix (Fin 1) (Fin 1) F))).map σ) =
        Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
          (Matrix.fromBlocks s 0 0 (1 : Matrix (Fin 1) (Fin 1) F)) := by
      ext x y
      rcases x with a | (u | k) <;> rcases y with b | (v | l) <;>
        simp [s, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    rw [hSmap]
    rw [reindex131_eq_fromBlocks' (m := m) (F := F) A⁻¹
      (isUpperGL_inv (F := F) (A := A) hA)]
  have hRY : R ((embedMid m F (CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g) :
      SpecialLinearGroup (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
        (Matrix.fromBlocks β 0 0 (1 : Matrix (Fin 1) (Fin 1) F)) :=
    reindex_embedMid (m := m) (F := F)
      (CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g)
  have hRprod : R ((((embedMid m F
        (CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g))⁻¹ *
      CFSG.QuasithinUnique.K1.stdAut A σ 0 (embedMid m F g) :
        SpecialLinearGroup (Fin (m+3)) F)) : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) B 0
        (Matrix.fromBlocks (1 : Matrix (Fin (m+1)) (Fin (m+1)) F) E 0
          (1 : Matrix (Fin 1) (Fin 1) F)) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul]
    have hinv : (embedMid m F
        (CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g))⁻¹ =
        embedMid m F
          ((CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g)⁻¹) :=
      (map_inv (embedMid m F) _).symm
    rw [hinv, reindex_embedMid (m := m) (F := F)
      ((CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g)⁻¹), hRX]
    have hinvblock :
        (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
          (Matrix.fromBlocks β 0 0 (1 : Matrix (Fin 1) (Fin 1) F)))⁻¹ =
        Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0
          (Matrix.fromBlocks β' 0 0 (1 : Matrix (Fin 1) (Fin 1) F)) := by
      apply inv_fromBlocks_diag
      · simp
      · rw [Matrix.fromBlocks_multiply, hβ2'']
        simp [Matrix.fromBlocks_one]
    rw [← hinvblock]
    exact hBE
  have hN : R ((((embedMid m F
        (CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 g))⁻¹ *
      CFSG.QuasithinUnique.K1.stdAut A σ 0 (embedMid m F g) :
        SpecialLinearGroup (Fin (m+3)) F) : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) =
      Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) F) B 0
        (Matrix.fromBlocks (0 : Matrix (Fin (m+1)) (Fin (m+1)) F) E 0
          (0 : Matrix (Fin 1) (Fin 1) F)) := by
    rw [map_sub, hRprod, map_one, blockUpper131_sub_one]
  exact isTwoEndZero_of_reindex_blockStrictUpper (m := m) (F := F) hN

theorem borelStd_embedMid {A : GL (Fin (m+3)) F} (hA : IsUpperGL A)
    (σ : F ≃+* F) (ε : ℕ) (g : SpecialLinearGroup (Fin (m+1)) F) :
    (embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g))⁻¹ *
      borelStd (m+3) F A σ ε (embedMid m F g) ∈ twoEndRadical m F := by
  rcases Nat.mod_two_eq_zero_or_one ε with hε | hε
  · have hγ : (borelGraph (m+3) F) ^ ε = 1 :=
      borelGraph_pow_eq_one_of_even (n := m+3) (F := F) (ε := ε) hε
    have hγ' : (borelGraph (m+1) F) ^ ε = 1 :=
      borelGraph_pow_eq_one_of_even (n := m+1) (F := F) (ε := ε) hε
    have hstd : borelStd (m+3) F A σ ε = CFSG.QuasithinUnique.K1.stdAut A σ 0 := by
      rw [borelStd, hγ, mul_one]
    have hbs : borelStd (m+1) F (midGL m F A hA) σ ε =
        CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0 := by
      rw [borelStd, hγ', mul_one]
    rw [hstd, hbs]
    exact stdAut_zero_embedMid m F hA σ g
  · have hε1 : ε % 2 = 1 := by omega
    have hγ : (borelGraph (m+3) F) ^ ε = borelGraph (m+3) F :=
      borelGraph_pow_eq_self_of_odd (n := m+3) (F := F) (ε := ε) hε1
    have hγ' : (borelGraph (m+1) F) ^ ε = borelGraph (m+1) F :=
      borelGraph_pow_eq_self_of_odd (n := m+1) (F := F) (ε := ε) hε1
    have hstd : borelStd (m+3) F A σ ε (embedMid m F g) =
        CFSG.QuasithinUnique.K1.stdAut A σ 0
          (borelGraph (m+3) F (embedMid m F g)) := by
      rw [borelStd_apply, hγ]
    have hbs : borelStd (m+1) F (midGL m F A hA) σ ε g =
        CFSG.QuasithinUnique.K1.stdAut (midGL m F A hA) σ 0
          (borelGraph (m+1) F g) := by
      rw [borelStd_apply, hγ']
    rw [hstd, hbs, borelGraph_embedMid]
    exact stdAut_zero_embedMid m F hA σ (borelGraph (m+1) F g)

theorem twoEnd_intertwine_apply {A : GL (Fin (m+3)) F} (hA : IsUpperGL A)
    (σ : F ≃+* F) (ε : ℕ) {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) (T : V →ₗ[k] V)
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m+3) F A σ ε g) (T v)) :
    (∀ x ∈ twoEndFix m F ρ, T x ∈ twoEndFix m F ρ) ∧
      ∀ g, ∀ x ∈ twoEndFix m F ρ,
        T (ρ (embedMid m F g) x) =
          ρ (embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g)) (T x) := by
  have hN : (twoEndRadical m F).map (borelStd (m+3) F A σ ε).toMonoidHom =
      twoEndRadical m F := twoEndRadical_map_borelStd m F A hA σ ε
  have hfix : ∀ x ∈ twoEndFix m F ρ, T x ∈ twoEndFix m F ρ :=
    fixSub_mapsTo_of_intertwine hN hT
  refine ⟨hfix, ?_⟩
  intro g x hx
  have hTx : T x ∈ twoEndFix m F ρ := hfix x hx
  let q : SpecialLinearGroup (Fin (m+3)) F :=
    (embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g))⁻¹ *
      borelStd (m+3) F A σ ε (embedMid m F g)
  have hq : q ∈ twoEndRadical m F := borelStd_embedMid m F hA σ ε g
  have hdecomp : borelStd (m+3) F A σ ε (embedMid m F g) =
      embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g) * q := by
    rw [show q = (embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g))⁻¹ *
        borelStd (m+3) F A σ ε (embedMid m F g) from rfl]
    group
  calc T (ρ (embedMid m F g) x)
      = ρ (borelStd (m+3) F A σ ε (embedMid m F g)) (T x) := hT _ _
    _ = ρ (embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g) * q) (T x) := by
        rw [hdecomp]
    _ = ρ (embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g)) (ρ q (T x)) := by
        rw [map_mul]
        rfl
    _ = ρ (embedMid m F (borelStd (m+1) F (midGL m F A hA) σ ε g)) (T x) := by
        congr 1
        exact (mem_fixSub (ρ := ρ) (S := twoEndRadical m F)).mp hTx q hq

end Preservation

end

end CFSG.LieType.SpecialLinear
