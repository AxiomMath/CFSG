module

public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.Phan

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Entries

variable {F : Type*} [Field F] {m k l i j : ℕ}

@[expose] def blockIdx (i : ℕ) (h : i + k ≤ m) (x : Fin k) : Fin m :=
  ⟨i + x.val, by have := x.isLt; omega⟩

@[simp] theorem blockIdx_val (h : i + k ≤ m) (x : Fin k) : (blockIdx i h x).val = i + x.val :=
  rfl

theorem blockIdx_injective (h : i + k ≤ m) : Function.Injective (blockIdx i h) := by
  intro x y hxy
  exact Fin.ext (by simpa [Fin.ext_iff] using hxy)

theorem blockSel_mul_apply {n : ℕ} (M : Matrix (Fin k) (Fin n) F) (a : Fin m) (c : Fin n) :
    (blockSel F m k i * M) a c =
      if h : i ≤ a.val ∧ a.val < i + k then M ⟨a.val - i, by omega⟩ c else 0 := by
  rw [mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨a.val - i, by omega⟩ : Fin k)]
    · rw [blockSel_apply, ite_eq_left (by dsimp only; omega), one_mul]
    · intro x _ hx
      have : ¬ a.val = i + x.val := fun h' => hx (Fin.ext (by dsimp only; omega))
      rw [blockSel_apply, ite_eq_right this, zero_mul]
    · simp
  · refine Finset.sum_eq_zero fun x _ => ?_
    have : ¬ a.val = i + x.val := by have := x.isLt; omega
    rw [blockSel_apply, ite_eq_right this, zero_mul]

theorem mul_blockSel_transpose_apply {n : ℕ} (M : Matrix (Fin n) (Fin k) F) (c : Fin n)
    (b : Fin m) :
    (M * (blockSel F m k i)ᵀ) c b =
      if h : i ≤ b.val ∧ b.val < i + k then M c ⟨b.val - i, by omega⟩ else 0 := by
  rw [mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨b.val - i, by omega⟩ : Fin k)]
    · rw [transpose_apply, blockSel_apply, ite_eq_left (by dsimp only; omega), mul_one]
    · intro x _ hx
      have : ¬ b.val = i + x.val := fun h' => hx (Fin.ext (by dsimp only; omega))
      rw [transpose_apply, blockSel_apply, ite_eq_right this, mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun x _ => ?_
    have : ¬ b.val = i + x.val := by have := x.isLt; omega
    rw [transpose_apply, blockSel_apply, ite_eq_right this, mul_zero]

theorem blockMat_apply (A : Matrix (Fin k) (Fin k) F) (a b : Fin m) :
    blockMat m i A a b =
      if h : (i ≤ a.val ∧ a.val < i + k) ∧ (i ≤ b.val ∧ b.val < i + k) then
        A ⟨a.val - i, by omega⟩ ⟨b.val - i, by omega⟩
      else (1 : Matrix (Fin m) (Fin m) F) a b := by
  unfold blockMat
  rw [Matrix.add_apply, mul_blockSel_transpose_apply]
  by_cases hb : i ≤ b.val ∧ b.val < i + k
  · rw [dite_eq_left hb, blockSel_mul_apply]
    by_cases ha : i ≤ a.val ∧ a.val < i + k
    · rw [dite_eq_left ha, dite_eq_left ⟨ha, hb⟩, Matrix.sub_apply]
      have : ((1 : Matrix (Fin m) (Fin m) F) a b) =
          (1 : Matrix (Fin k) (Fin k) F) ⟨a.val - i, by omega⟩ ⟨b.val - i, by omega⟩ := by
        simp only [one_apply, Fin.ext_iff]
        congr 1
        exact propext ⟨fun h' => by omega, fun h' => by omega⟩
      rw [this]
      ring
    · rw [dite_eq_right ha, dite_eq_right (fun h' => ha h'.1), add_zero]
  · rw [dite_eq_right hb, dite_eq_right (fun h' => hb h'.2), add_zero]

theorem blockMat_apply_blockIdx (h : i + k ≤ m) (A : Matrix (Fin k) (Fin k) F) (x y : Fin k) :
    blockMat m i A (blockIdx i h x) (blockIdx i h y) = A x y := by
  rw [blockMat_apply, dite_eq_left (by
    simp only [blockIdx_val]; have := x.isLt; have := y.isLt; omega)]
  simp

theorem blockMat_apply_of_not_mem_left (A : Matrix (Fin k) (Fin k) F) {a : Fin m}
    (ha : ¬ (i ≤ a.val ∧ a.val < i + k)) (b : Fin m) :
    blockMat m i A a b = (1 : Matrix (Fin m) (Fin m) F) a b := by
  rw [blockMat_apply, dite_eq_right (fun h' => ha h'.1)]

theorem blockMat_apply_of_not_mem_right (A : Matrix (Fin k) (Fin k) F) (a : Fin m) {b : Fin m}
    (hb : ¬ (i ≤ b.val ∧ b.val < i + k)) :
    blockMat m i A a b = (1 : Matrix (Fin m) (Fin m) F) a b := by
  rw [blockMat_apply, dite_eq_right (fun h' => hb h'.2)]

theorem blockMat_injective (h : i + k ≤ m) :
    Function.Injective (blockMat (F := F) (k := k) m i) := by
  intro A B hAB
  ext x y
  have := congrFun (congrFun hAB (blockIdx i h x)) (blockIdx i h y)
  rwa [blockMat_apply_blockIdx, blockMat_apply_blockIdx] at this

theorem blockSel_transpose_mul_blockSel_of_disjoint (hij : i + k ≤ j ∨ j + l ≤ i) :
    (blockSel F m k i)ᵀ * blockSel F m l j = 0 := by
  ext x y
  rw [mul_apply]
  refine (Finset.sum_eq_zero fun a _ => ?_).trans (by simp)
  rw [transpose_apply, blockSel_apply, blockSel_apply]
  by_cases h : a.val = i + x.val
  · have : ¬ a.val = j + y.val := by have := x.isLt; have := y.isLt; omega
    rw [ite_eq_right this, mul_zero]
  · rw [ite_eq_right h, zero_mul]

theorem blockMat_comm (hij : i + k ≤ j ∨ j + l ≤ i) (A : Matrix (Fin k) (Fin k) F)
    (B : Matrix (Fin l) (Fin l) F) :
    blockMat m i A * blockMat m j B = blockMat m j B * blockMat m i A := by
  have h1 := blockSel_transpose_mul_blockSel_of_disjoint (F := F) (m := m) hij
  have h2 : (blockSel F m l j)ᵀ * blockSel F m k i = 0 := by
    have := congrArg Matrix.transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_zero] at this
  have e1 : blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ *
      (blockSel F m l j * (B - 1) * (blockSel F m l j)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (blockSel F m k i)ᵀ (blockSel F m l j), h1, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.mul_zero]
  have e2 : blockSel F m l j * (B - 1) * (blockSel F m l j)ᵀ *
      (blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (blockSel F m l j)ᵀ (blockSel F m k i), h2, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.mul_zero]
  unfold blockMat
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  rw [e1, e2]
  abel

theorem blockSel_mul_blockSel (hj : j + l ≤ k) :
    blockSel F m k i * blockSel F k l j = blockSel F m l (i + j) := by
  ext a y
  rw [blockSel_mul_apply]
  have hy := y.isLt
  by_cases h : i ≤ a.val ∧ a.val < i + k
  · rw [dite_eq_left h, blockSel_apply, blockSel_apply]
    by_cases h' : a.val = i + j + y.val
    · rw [ite_eq_left h', ite_eq_left (by dsimp only; omega)]
    · rw [ite_eq_right h', ite_eq_right (by dsimp only; omega)]
  · rw [dite_eq_right h, blockSel_apply, ite_eq_right (by omega)]

theorem blockMat_blockMat (hj : j + l ≤ k) (A : Matrix (Fin l) (Fin l) F) :
    blockMat m i (blockMat k j A) = blockMat m (i + j) A := by
  have h1 : blockMat k j A - 1 = blockSel F k l j * (A - 1) * (blockSel F k l j)ᵀ := by
    unfold blockMat
    rw [add_sub_cancel_left]
  have h2 : (blockSel F m k i * blockSel F k l j)ᵀ = (blockSel F k l j)ᵀ * (blockSel F m k i)ᵀ :=
    transpose_mul _ _
  have h3 := blockSel_mul_blockSel (F := F) (m := m) (i := i) hj
  unfold blockMat
  rw [add_sub_cancel_left, ← h3, h2]
  simp only [Matrix.mul_assoc]

theorem conj_blockMat_of_intertwine {i' : ℕ} {W W' : Matrix (Fin m) (Fin m) F}
    {D D' : Matrix (Fin k) (Fin k) F} (hWW' : W * W' = 1) (hDD' : D * D' = 1)
    (h1 : W * blockSel F m k i = blockSel F m k i' * D)
    (h2 : (blockSel F m k i')ᵀ * W = D * (blockSel F m k i)ᵀ) (A : Matrix (Fin k) (Fin k) F) :
    W * blockMat m i A * W' = blockMat m i' (D * A * D') := by
  have hD'D : D' * D = 1 := mul_eq_one_comm.mp hDD'
  have h3 : (blockSel F m k i)ᵀ * W' = D' * (blockSel F m k i')ᵀ := by
    calc (blockSel F m k i)ᵀ * W'
        = (D' * D) * (blockSel F m k i)ᵀ * W' := by rw [hD'D, Matrix.one_mul]
      _ = D' * ((D * (blockSel F m k i)ᵀ) * W') := by simp only [Matrix.mul_assoc]
      _ = D' * (((blockSel F m k i')ᵀ * W) * W') := by rw [h2]
      _ = D' * (blockSel F m k i')ᵀ := by rw [Matrix.mul_assoc, hWW', Matrix.mul_one]
  have h4 : D * (A - 1) * D' = D * A * D' - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD']
  unfold blockMat
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hWW', ← h4]
  have : W * (blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ) * W' =
      blockSel F m k i' * (D * (A - 1) * D') * (blockSel F m k i')ᵀ := by
    calc W * (blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ) * W'
        = (W * blockSel F m k i) * (A - 1) * ((blockSel F m k i)ᵀ * W') := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h3]; simp only [Matrix.mul_assoc]
  rw [this]

theorem blockSel_transpose_mulVec (h : i + k ≤ m) (v : Fin m → F) (y : Fin k) :
    ((blockSel F m k i)ᵀ *ᵥ v) y = v (blockIdx i h y) := by
  rw [mulVec, dotProduct]
  rw [Finset.sum_eq_single (blockIdx i h y)]
  · rw [transpose_apply, blockSel_apply, ite_eq_left (by simp), one_mul]
  · intro a _ ha
    have : ¬ a.val = i + y.val := fun h' => ha (Fin.ext (by simpa using h'))
    rw [transpose_apply, blockSel_apply, ite_eq_right this, zero_mul]
  · simp

theorem blockSel_mulVec (w : Fin k → F) (a : Fin m) :
    (blockSel F m k i *ᵥ w) a =
      if h : i ≤ a.val ∧ a.val < i + k then w ⟨a.val - i, by omega⟩ else 0 := by
  have := blockSel_mul_apply (F := F) (m := m) (k := k) (i := i)
    (Matrix.of fun (x : Fin k) (_ : Fin 1) => w x) a 0
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

theorem blockMat_mulVec_blockIdx (h : i + k ≤ m) (A : Matrix (Fin k) (Fin k) F) (v : Fin m → F)
    (x : Fin k) :
    (blockMat m i A *ᵥ v) (blockIdx i h x) = (A *ᵥ fun y => v (blockIdx i h y)) x := by
  have hv : ((blockSel F m k i)ᵀ *ᵥ v) = fun y => v (blockIdx i h y) :=
    funext (blockSel_transpose_mulVec h v)
  unfold blockMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Pi.add_apply, blockSel_mulVec,
    dite_eq_left (by simp only [blockIdx_val]; have := x.isLt; omega),
    hv, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp [blockIdx]

theorem blockMat_mulVec_of_not_mem (A : Matrix (Fin k) (Fin k) F) (v : Fin m → F) {a : Fin m}
    (ha : ¬ (i ≤ a.val ∧ a.val < i + k)) : (blockMat m i A *ᵥ v) a = v a := by
  unfold blockMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Pi.add_apply, blockSel_mulVec, dite_eq_right ha, add_zero]

theorem embPair_two_eq_blockMat (A : Matrix (Fin 2) (Fin 2) F) :
    embPair 2 A = blockMat 3 0 A := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [embPair, blockMat_apply]

theorem embPair_zero_eq_blockMat (A : Matrix (Fin 2) (Fin 2) F) :
    embPair 0 A = blockMat 3 1 A := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [embPair, blockMat_apply]

end Entries

section Embeddings

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem embSUid_two_eq_blockEmb :
    embSUid (unitaryInvolution K p f) 2 = blockEmb K p f 3 2 0 (by omega) :=
  MonoidHom.ext fun _ => Subtype.ext (Units.ext (embPair_two_eq_blockMat _))

theorem embSUid_zero_eq_blockEmb :
    embSUid (unitaryInvolution K p f) 0 = blockEmb K p f 3 2 1 (by omega) :=
  MonoidHom.ext fun _ => Subtype.ext (Units.ext (embPair_zero_eq_blockMat _))

theorem blockEmb_injective {m k i : ℕ} (h : i + k ≤ m) :
    Function.Injective (blockEmb K p f m k i h) := by
  intro A B hAB
  have := congrArg (fun g : Su K p f m => (((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))) hAB
  exact Subtype.ext (Units.ext (blockMat_injective h this))

theorem blockEmb_comm {m k l i j : ℕ} (h₁ : i + k ≤ m) (h₂ : j + l ≤ m)
    (hij : i + k ≤ j ∨ j + l ≤ i) (A : Su K p f k) (B : Su K p f l) :
    blockEmb K p f m k i h₁ A * blockEmb K p f m l j h₂ B =
      blockEmb K p f m l j h₂ B * blockEmb K p f m k i h₁ A :=
  Subtype.ext (Units.ext (blockMat_comm hij _ _))

theorem blockEmb_comp {m k l i j : ℕ} (h₁ : i + k ≤ m) (h₂ : j + l ≤ k) :
    (blockEmb K p f m k i h₁).comp (blockEmb K p f k l j h₂) =
      blockEmb K p f m l (i + j) (by omega) :=
  MonoidHom.ext fun _ => Subtype.ext (Units.ext (blockMat_blockMat h₂ _))

theorem blockEmb_comp_apply {m k l i j : ℕ} (h₁ : i + k ≤ m) (h₂ : j + l ≤ k) (A : Su K p f l) :
    blockEmb K p f m k i h₁ (blockEmb K p f k l j h₂ A) =
      blockEmb K p f m l (i + j) (by omega) A :=
  DFunLike.congr_fun (blockEmb_comp h₁ h₂) A

theorem blockEmb2_comm (n : ℕ) (i j : Fin n) (hij : (i : ℕ) + 1 < j) (A B : Su K p f 2) :
    blockEmb2 K p f n i A * blockEmb2 K p f n j B = blockEmb2 K p f n j B * blockEmb2 K p f n i A :=
  blockEmb_comm _ _ (Or.inl (by omega)) A B

theorem blockEmb3_comp_embSUid_two (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (blockEmb3 K p f n i h).comp (embSUid (unitaryInvolution K p f) 2) =
      blockEmb2 K p f n i := by
  rw [embSUid_two_eq_blockEmb]
  exact blockEmb_comp _ _

theorem blockEmb3_comp_embSUid_zero (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (blockEmb3 K p f n i h).comp (embSUid (unitaryInvolution K p f) 0) =
      blockEmb2 K p f n ⟨i + 1, h⟩ := by
  rw [embSUid_zero_eq_blockEmb]
  exact blockEmb_comp _ _

theorem coe_coe_blockEmb2 (n : ℕ) (i : Fin n) (A : Su K p f 2) :
    (((blockEmb2 K p f n i A : Su K p f (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      blockMat (n + 1) i.val (((A : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem coe_coe_blockEmb3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) (A : Su K p f 3) :
    (((blockEmb3 K p f n i h A : Su K p f (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      blockMat (n + 1) i.val (((A : Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem blockEmb2_injective (n : ℕ) (i : Fin n) : Function.Injective (blockEmb2 K p f n i) :=
  blockEmb_injective _

theorem blockEmb3_injective (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    Function.Injective (blockEmb3 K p f n i h) :=
  blockEmb_injective _

theorem range_blockEmb2_le_range_blockEmb3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (blockEmb2 K p f n i).range ≤ (blockEmb3 K p f n i h).range := by
  rw [← blockEmb3_comp_embSUid_two n i h, MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

theorem range_blockEmb2_succ_le_range_blockEmb3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (blockEmb2 K p f n ⟨i + 1, h⟩).range ≤ (blockEmb3 K p f n i h).range := by
  rw [← blockEmb3_comp_embSUid_zero n i h, MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

end Embeddings

section Swap

variable {F : Type*} [Field F]

@[expose] def swapMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

@[expose] def rotMat : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]

@[expose] def rotMatInv : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

theorem swapMat_mul_self : swapMat * swapMat = (1 : Matrix (Fin 3) (Fin 3) F) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_swapMat : (swapMat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [swapMat, Matrix.det_fin_three]

theorem conjTr_swapMat (σ : F ≃+* F) : conjTr σ (swapMat : Matrix (Fin 3) (Fin 3) F) = swapMat := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [conjTr, swapMat]

theorem rotMat_mul_rotMatInv : rotMat * rotMatInv = (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [rotMat, rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotMatInv_mul_rotMat : rotMatInv * rotMat = (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [rotMat, rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_rotMat : (rotMat : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [rotMat, Matrix.det_fin_two]

theorem conjTr_rotMat (σ : F ≃+* F) :
    conjTr σ (rotMat : Matrix (Fin 2) (Fin 2) F) = rotMatInv := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [conjTr, rotMat, rotMatInv]

theorem swapMat_mul_embPair_two (A : Matrix (Fin 2) (Fin 2) F) :
    swapMat * embPair 2 A * swapMat = embPair 0 (rotMat * A * rotMatInv) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [embPair, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] <;>
    simp [swapMat, rotMat, rotMatInv]

theorem swapMat_mul_embPair_zero (A : Matrix (Fin 2) (Fin 2) F) :
    swapMat * embPair 0 A * swapMat = embPair 2 (rotMat * A * rotMatInv) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [embPair, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] <;>
    simp [swapMat, rotMat, rotMatInv]

variable (σ : F ≃+* F)

@[expose] def swapSU : SUid σ 3 :=
  ⟨⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩, by
    rw [Units.val_mk, det_swapMat], by
    rw [Units.val_mk, conjTr_swapMat, swapMat_mul_self]⟩

@[expose] def rotSU : SUid σ 2 :=
  ⟨⟨rotMat, rotMatInv, rotMat_mul_rotMatInv, rotMatInv_mul_rotMat⟩, by
    rw [Units.val_mk, det_rotMat], by
    rw [Units.val_mk, conjTr_rotMat, rotMatInv_mul_rotMat]⟩

theorem swapSU_inv : (swapSU σ)⁻¹ = swapSU σ :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (Units.ext swapMat_mul_self))

theorem swapSU_mul_embSUid_two_mul_inv (A : SUid σ 2) :
    swapSU σ * embSUid σ 2 A * (swapSU σ)⁻¹ = embSUid σ 0 (rotSU σ * A * (rotSU σ)⁻¹) := by
  rw [swapSU_inv]
  exact Subtype.ext (Units.ext (swapMat_mul_embPair_two _))

theorem swapSU_mul_embSUid_zero_mul_inv (A : SUid σ 2) :
    swapSU σ * embSUid σ 0 A * (swapSU σ)⁻¹ = embSUid σ 2 (rotSU σ * A * (rotSU σ)⁻¹) := by
  rw [swapSU_inv]
  exact Subtype.ext (Units.ext (swapMat_mul_embPair_zero _))

end Swap

section SwapPhan

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def swapElt : Su K p f 3 := swapSU (unitaryInvolution K p f)

theorem map_conj_swapElt_B12 :
    (B12 K p f).map (MulAut.conj (swapElt K p f)).toMonoidHom = B23 K p f := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, (swapSU_mul_embSUid_two_mul_inv _ A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨embSUid (unitaryInvolution K p f) 2 ((rotSU _)⁻¹ * A * rotSU _), ⟨_, rfl⟩, ?_⟩
    change swapSU _ * _ * (swapSU _)⁻¹ = _
    rw [swapSU_mul_embSUid_two_mul_inv]
    congr 1
    group

theorem map_conj_swapElt_B23 :
    (B23 K p f).map (MulAut.conj (swapElt K p f)).toMonoidHom = B12 K p f := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, (swapSU_mul_embSUid_zero_mul_inv _ A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨embSUid (unitaryInvolution K p f) 0 ((rotSU _)⁻¹ * A * rotSU _), ⟨_, rfl⟩, ?_⟩
    change swapSU _ * _ * (swapSU _)⁻¹ = _
    rw [swapSU_mul_embSUid_zero_mul_inv]
    congr 1
    group

theorem swapElt_inv : (swapElt K p f)⁻¹ = swapElt K p f := swapSU_inv _

end SwapPhan

end CFSG.ClassicalInvolution.Phan
