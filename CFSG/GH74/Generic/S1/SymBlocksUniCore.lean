module

public import CFSG.GH74.Generic.S1.FrameDefs

public section

namespace CFSG.GH74.Generic.S1.SymBlocksUni

open Matrix CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable (F : Type) [Field F]

@[expose] def selL {k m : ℕ} (ι : Fin k → Fin m) : Matrix (Fin m) (Fin k) F :=
  Matrix.of fun x j => if x = ι j then 1 else 0

variable {F}

section Sel

variable {k m n : ℕ} {ι : Fin k → Fin m}

theorem selL_apply (ι : Fin k → Fin m) (x : Fin m) (j : Fin k) :
    selL F ι x j = if x = ι j then 1 else 0 := rfl

theorem selL_transpose_mul_self (hι : Function.Injective ι) : (selL F ι)ᵀ * selL F ι = 1 := by
  ext j j'
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (ι j)]
  · simp only [Matrix.transpose_apply, selL_apply, ite_true, one_mul]
    by_cases h : j = j'
    · subst h; simp
    · have : ι j ≠ ι j' := fun e => h (hι e)
      simp [h, this]
  · intro x _ hx
    simp [selL_apply, hx]
  · simp

theorem selL_mul_apply (hι : Function.Injective ι) (X : Matrix (Fin k) (Fin n) F) (x : Fin k)
    (y : Fin n) : (selL F ι * X) (ι x) y = X x y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · simp [selL_apply]
  · intro x' _ hx'
    have : ι x ≠ ι x' := fun e => hx' (hι e).symm
    simp [selL_apply, this]
  · simp

theorem selL_mul_apply_of_not_mem (X : Matrix (Fin k) (Fin n) F) {i : Fin m} (hi : ∀ x, i ≠ ι x)
    (y : Fin n) : (selL F ι * X) i y = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [selL_apply, hi x]

theorem mul_selL_transpose_apply (hι : Function.Injective ι) (X : Matrix (Fin n) (Fin k) F)
    (x : Fin n) (y : Fin k) : (X * (selL F ι)ᵀ) x (ι y) = X x y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single y]
  · simp [selL_apply]
  · intro y' _ hy'
    have : ι y ≠ ι y' := fun e => hy' (hι e).symm
    simp [selL_apply, this]
  · simp

theorem mul_selL_transpose_apply_of_not_mem (X : Matrix (Fin n) (Fin k) F) (x : Fin n) {j : Fin m}
    (hj : ∀ y, j ≠ ι y) : (X * (selL F ι)ᵀ) x j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  simp [selL_apply, hj y]

theorem selL_comp {l : ℕ} (ι' : Fin m → Fin l) : selL F (ι' ∘ ι) = selL F ι' * selL F ι := by
  ext x j
  rw [Matrix.mul_apply, Finset.sum_eq_single (ι j)]
  · simp [selL_apply]
  · intro y _ hy
    have : ¬ (y = ι j) := hy
    simp [selL_apply, this]
  · simp

end Sel

section BlkMat

variable {k m l : ℕ} {ι : Fin k → Fin m}

@[expose] def blkMat (ι : Fin k → Fin m) (A : Matrix (Fin k) (Fin k) F) : Matrix (Fin m) (Fin m) F :=
  1 + selL F ι * (A - 1) * (selL F ι)ᵀ

theorem blkMat_mul (hι : Function.Injective ι) (A B : Matrix (Fin k) (Fin k) F) :
    blkMat ι (A * B) = blkMat ι A * blkMat ι B := by
  have hL := selL_transpose_mul_self (F := F) hι
  unfold blkMat
  set L : Matrix (Fin m) (Fin k) F := selL F ι
  have e1 : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have e2 : (L * (A - 1) * Lᵀ) * (L * (B - 1) * Lᵀ) = L * ((A - 1) * (B - 1)) * Lᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Lᵀ L (((B - 1) * Lᵀ)), hL, Matrix.one_mul]
  have hG : L * (A * B - 1) * Lᵀ =
      L * (A - 1) * Lᵀ + L * (B - 1) * Lᵀ + L * ((A - 1) * (B - 1)) * Lᵀ := by
    rw [e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  have key : ∀ E E' G : Matrix (Fin m) (Fin m) F, G = E + E' + E * E' →
      1 + G = (1 + E) * (1 + E') := by
    intro E E' G hG
    rw [hG]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    abel
  exact key _ _ _ (by rw [hG, e2])

theorem blkMat_one : blkMat ι (1 : Matrix (Fin k) (Fin k) F) = 1 := by
  simp [blkMat]

theorem det_blkMat (hι : Function.Injective ι) (A : Matrix (Fin k) (Fin k) F) :
    (blkMat ι A).det = A.det := by
  have hL := selL_transpose_mul_self (F := F) hι
  unfold blkMat
  set L : Matrix (Fin m) (Fin k) F := selL F ι
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc (A - 1) Lᵀ L, hL,
    Matrix.mul_one]
  simp

theorem conjTr_blkMat (σ : F ≃+* F) (A : Matrix (Fin k) (Fin k) F) :
    conjTr σ (blkMat ι A) = blkMat ι (conjTr σ A) := by
  have hL : (selL F ι).map σ = selL F ι := by
    ext a j
    simp only [Matrix.map_apply, selL_apply]
    split_ifs <;> simp
  have hLt : ((selL F ι)ᵀ).map σ = (selL F ι)ᵀ := by
    rw [Matrix.transpose_map, hL]
  have hN : (A - 1).map σ = A.map σ - 1 := by
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  unfold blkMat conjTr
  rw [Matrix.map_add _ (map_add σ), Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.map_mul,
    Matrix.map_mul,
    hL, hLt, hN, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.mul_assoc]

theorem blkMat_apply_ι (hι : Function.Injective ι) (A : Matrix (Fin k) (Fin k) F) (x y : Fin k) :
    blkMat ι A (ι x) (ι y) = A x y := by
  unfold blkMat
  rw [Matrix.add_apply, mul_selL_transpose_apply hι, selL_mul_apply hι, Matrix.sub_apply]
  have : (1 : Matrix (Fin m) (Fin m) F) (ι x) (ι y) = (1 : Matrix (Fin k) (Fin k) F) x y := by
    simp only [Matrix.one_apply, hι.eq_iff]
  rw [this]
  ring

theorem blkMat_apply_of_not_mem_left (A : Matrix (Fin k) (Fin k) F) {i : Fin m}
    (hi : ∀ x, i ≠ ι x) (j : Fin m) : blkMat ι A i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
  unfold blkMat
  rw [Matrix.add_apply, Matrix.mul_apply]
  have h0 : ∀ y, (selL F ι * (A - 1) : Matrix (Fin m) (Fin k) F) i y = 0 :=
    fun y => selL_mul_apply_of_not_mem _ hi y
  simp [h0]

theorem blkMat_apply_of_not_mem_right (A : Matrix (Fin k) (Fin k) F) (i : Fin m) {j : Fin m}
    (hj : ∀ y, j ≠ ι y) : blkMat ι A i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
  unfold blkMat
  rw [Matrix.add_apply, mul_selL_transpose_apply_of_not_mem _ _ hj, add_zero]

theorem blkMat_injective (hι : Function.Injective ι) :
    Function.Injective (blkMat (F := F) ι : Matrix (Fin k) (Fin k) F → _) := by
  intro A B hAB
  ext x y
  have := congrFun (congrFun hAB (ι x)) (ι y)
  rwa [blkMat_apply_ι hι, blkMat_apply_ι hι] at this

theorem blkMat_blkMat (ι' : Fin m → Fin l) (A : Matrix (Fin k) (Fin k) F) :
    blkMat ι' (blkMat ι A) = blkMat (ι' ∘ ι) A := by
  have h1 : blkMat ι A - 1 = selL F ι * (A - 1) * (selL F ι)ᵀ := by
    unfold blkMat
    rw [add_sub_cancel_left]
  have h2 : (selL F ι' * selL F ι)ᵀ = (selL F ι)ᵀ * (selL F ι')ᵀ := transpose_mul _ _
  unfold blkMat
  rw [add_sub_cancel_left, selL_comp, h2]
  simp only [Matrix.mul_assoc]

end BlkMat

section Embedding

variable {k m l : ℕ} {ι : Fin k → Fin m}

@[expose] def blkMatHom (hι : Function.Injective ι) :
    Matrix (Fin k) (Fin k) F →* Matrix (Fin m) (Fin m) F where
  toFun := blkMat ι
  map_one' := blkMat_one
  map_mul' := blkMat_mul hι

@[expose] def blkGL (hι : Function.Injective ι) : GL (Fin k) F →* GL (Fin m) F :=
  Units.map (blkMatHom hι)

theorem coe_blkGL (hι : Function.Injective ι) (g : GL (Fin k) F) :
    ((blkGL hι g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      blkMat ι (g : Matrix (Fin k) (Fin k) F) :=
  rfl

theorem blkGL_mem_SUid (σ : F ≃+* F) (hι : Function.Injective ι) {g : GL (Fin k) F}
    (hg : g ∈ SUid σ k) : blkGL hι g ∈ SUid σ m := by
  obtain ⟨hdet, hiso⟩ := hg
  refine ⟨by rw [coe_blkGL, det_blkMat hι, hdet], ?_⟩
  rw [coe_blkGL, conjTr_blkMat, ← blkMat_mul hι, hiso, blkMat_one]

@[expose] def blkEmb (σ : F ≃+* F) (hι : Function.Injective ι) : SUid σ k →* SUid σ m :=
  ((blkGL hι).comp (SUid σ k).subtype).codRestrict _ fun g => blkGL_mem_SUid σ hι g.2

theorem coe_coe_blkEmb (σ : F ≃+* F) (hι : Function.Injective ι) (g : SUid σ k) :
    (((blkEmb σ hι g : SUid σ m) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      blkMat ι (((g : SUid σ k) : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) :=
  rfl

theorem blkEmb_injective (σ : F ≃+* F) (hι : Function.Injective ι) :
    Function.Injective (blkEmb σ hι) := by
  intro A B hAB
  have := congrArg (fun g : SUid σ m => (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))) hAB
  exact Subtype.ext (Units.ext (blkMat_injective hι this))

theorem blkEmb_comp (σ : F ≃+* F) (hι : Function.Injective ι) {ι' : Fin m → Fin l}
    (hι' : Function.Injective ι') :
    (blkEmb σ hι').comp (blkEmb σ hι) = blkEmb σ (hι'.comp hι) :=
  MonoidHom.ext fun _ => Subtype.ext (Units.ext (blkMat_blkMat ι' _))

end Embedding

section IdOut

@[expose] def pairIdx (a b : Fin 4) : Fin 2 → Fin 4 := ![a, b]

theorem pairIdx_zero (a b : Fin 4) : pairIdx a b 0 = a := rfl

theorem pairIdx_one (a b : Fin 4) : pairIdx a b 1 = b := rfl

theorem pairIdx_injective {a b : Fin 4} (h : a ≠ b) : Function.Injective (pairIdx a b) := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · rfl
  · exact absurd hxy h
  · exact absurd hxy.symm h
  · rfl

theorem exists_pairIdx_iff {a b i : Fin 4} : (∃ x, i = pairIdx a b x) ↔ (i = a ∨ i = b) := by
  simp [pairIdx, Fin.exists_fin_two]

@[expose] def IdOut (a b : Fin 4) (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ i j, ¬ ((i = a ∨ i = b) ∧ (j = a ∨ j = b)) → M i j = (1 : Matrix (Fin 4) (Fin 4) F) i j

theorem IdOut.one (a b : Fin 4) : IdOut a b (1 : Matrix (Fin 4) (Fin 4) F) := fun _ _ _ => rfl

theorem IdOut.mul {a b : Fin 4} {M N : Matrix (Fin 4) (Fin 4) F} (hM : IdOut a b M)
    (hN : IdOut a b N) : IdOut a b (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  by_cases hi : (i = a ∨ i = b)
  · have hj : ¬ (j = a ∨ j = b) := fun hj => hij ⟨hi, hj⟩
    rw [Finset.sum_eq_single j]
    · rw [hN j j (fun h => hj h.2), hM i j hij]
      simp
    · intro k _ hk
      rw [hN k j (fun h => hj h.2)]
      simp [hk]
    · simp
  · rw [Finset.sum_eq_single i]
    · rw [hM i i (fun h => hi h.1), hN i j hij]
      simp
    · intro k _ hk
      rw [hM i k (fun h => hi h.1)]
      simp [Ne.symm hk]
    · simp

theorem IdOut.conjTr {a b : Fin 4} {σ : F ≃+* F} {M : Matrix (Fin 4) (Fin 4) F} (hM : IdOut a b M) :
    IdOut a b (CFSG.LieType.Universal.Unitary.conjTr σ M) := by
  intro i j hij
  have h1 := hM j i (fun h => hij ⟨h.2, h.1⟩)
  simp only [CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply, h1]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem idOut_blkMat {a b : Fin 4} (A : Matrix (Fin 2) (Fin 2) F) :
    IdOut a b (blkMat (pairIdx a b) A) := by
  intro i j hij
  by_cases hi : (i = a ∨ i = b)
  · have hj : ¬ (j = a ∨ j = b) := fun hj => hij ⟨hi, hj⟩
    exact blkMat_apply_of_not_mem_right A i (fun y h => hj (exists_pairIdx_iff.1 ⟨y, h⟩))
  · exact blkMat_apply_of_not_mem_left A (fun x h => hi (exists_pairIdx_iff.1 ⟨x, h⟩)) j

theorem eq_blkMat_of_idOut {a b : Fin 4} (hab : a ≠ b) {M : Matrix (Fin 4) (Fin 4) F}
    (hM : IdOut a b M) :
    M = blkMat (pairIdx a b) (Matrix.of fun x y => M (pairIdx a b x) (pairIdx a b y)) := by
  have hι := pairIdx_injective hab
  ext i j
  by_cases hi : ∃ x, i = pairIdx a b x
  · by_cases hj : ∃ y, j = pairIdx a b y
    · obtain ⟨x, rfl⟩ := hi
      obtain ⟨y, rfl⟩ := hj
      rw [blkMat_apply_ι hι]
      rfl
    · rw [blkMat_apply_of_not_mem_right _ _ (fun y h => hj ⟨y, h⟩),
        hM i j (fun h => hj (exists_pairIdx_iff.2 h.2))]
  · rw [blkMat_apply_of_not_mem_left _ (fun x h => hi ⟨x, h⟩),
      hM i j (fun h => hi (exists_pairIdx_iff.2 h.1))]

end IdOut

section Blk

variable (F)

@[expose] def uniBlk (q : ℕ) (a b : Fin 4) : Subgroup ↥(StatedSU 4 q F) where
  carrier := {g : ↥(StatedSU 4 q F) |
    IdOut a b ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ∧
      IdOut a b (((g : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_mul, Units.val_mul]
      exact hg1.mul hh1
    · rw [Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul]
      exact hh2.mul hg2
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using IdOut.one _ _
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_inv]
      exact hg2
    · rw [Subgroup.coe_inv, inv_inv]
      exact hg1

end Blk

section Ops

variable (F)

theorem IdOut.symm {a b : Fin 4} {M : Matrix (Fin 4) (Fin 4) F} (h : IdOut a b M) : IdOut b a M :=
  fun i j hij => h i j fun ⟨hi, hj⟩ => hij ⟨hi.symm, hj.symm⟩

theorem uniBlk_symm (q : ℕ) (a b : Fin 4) : uniBlk F q a b = uniBlk F q b a :=
  Subgroup.ext fun _ => ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

variable {F}

theorem uniBlk_commute {q : ℕ} {a b c d : Fin 4} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) {g h : ↥(StatedSU 4 q F)} (hg : g ∈ uniBlk F q a b) (hh : h ∈ uniBlk F q c d) :
    g * h = h * g := by
  apply Subtype.ext
  apply Units.ext
  change ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((h : GL (Fin 4) F) : Matrix _ _ F) =
    ((h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((g : GL (Fin 4) F) : Matrix _ _ F)
  set G : Matrix (Fin 4) (Fin 4) F := ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hG
  set H : Matrix (Fin 4) (Fin 4) F := ((h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hH
  have hg1 : IdOut a b G := hg.1
  have hh1 : IdOut c d H := hh.1
  have key : G * H - H * G = (G - 1) * (H - 1) - (H - 1) * (G - 1) := by noncomm_ring
  have hX : ∀ i j, ¬ ((i = a ∨ i = b) ∧ (j = a ∨ j = b)) → (G - 1) i j = 0 := fun i j hij => by
    rw [Matrix.sub_apply, hg1 i j hij, sub_self]
  have hY : ∀ i j, ¬ ((i = c ∨ i = d) ∧ (j = c ∨ j = d)) → (H - 1) i j = 0 := fun i j hij => by
    rw [Matrix.sub_apply, hh1 i j hij, sub_self]
  have h1 : (G - 1) * (H - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).trans (Matrix.zero_apply i j).symm
    by_cases hk : (k = a ∨ k = b)
    · have : ¬ (k = c ∨ k = d) := by
        rintro (h | h) <;> rcases hk with hk | hk <;> subst h <;> simp_all
      rw [hY k j (fun h' => this h'.1), mul_zero]
    · rw [hX i k (fun h' => hk h'.2), zero_mul]
  have h2 : (H - 1) * (G - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).trans (Matrix.zero_apply i j).symm
    by_cases hk : (k = c ∨ k = d)
    · have : ¬ (k = a ∨ k = b) := by
        rintro (h | h) <;> rcases hk with hk | hk <;> subst h <;> simp_all
      rw [hX k j (fun h' => this h'.1), mul_zero]
    · rw [hY i k (fun h' => hk h'.2), zero_mul]
  rw [← sub_eq_zero, key, h1, h2, sub_zero]

theorem uniBlk_comm_refl {q : ℕ} {a b c : Fin 4} (hca : c ≠ a) (hcb : c ≠ b)
    {g : ↥(StatedSU 4 q F)} (hg : g ∈ uniBlk F q a b) :
    (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * reflDiagMat F c =
    reflDiagMat F c * ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  unfold reflDiagMat
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : ((i = a ∨ i = b) ∧ (j = a ∨ j = b))
  · have hi : i ≠ c := by
      rintro rfl
      rcases hij.1 with h | h <;> simp_all
    have hj : j ≠ c := by
      rintro rfl
      rcases hij.2 with h | h <;> simp_all
    simp [hi, hj]
  · rw [hg.1 i j hij]
    by_cases h : i = j
    · subst h; simp [mul_comm]
    · simp [h]

end Ops

end CFSG.GH74.Generic.S1.SymBlocksUni
