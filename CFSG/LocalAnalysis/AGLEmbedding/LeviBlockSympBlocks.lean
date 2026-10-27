module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open SymplecticHigher (flagStabilizer mem_flagStabilizer)

variable {r : ℕ} {K : Type} [Field K]

theorem spFlag_mulVec_single_mem {d : ℕ} {g : StatedSp r K}
    (hg : g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K d)) {l : Fin r}
    (hl : (l : ℕ) < d) :
    mat r K g *ᵥ Pi.single (Sum.inl l) 1 ∈ SymplecticFlag.isoFlag r K d := by
  rw [SymplecticFlag.mem_stabilizer] at hg
  rw [← hg]
  exact ⟨_, Submodule.subset_span ⟨l, hl, rfl⟩, rfl⟩

theorem spFlag_inr_inl_eq_zero {d : ℕ} {g : StatedSp r K}
    (hg : g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K d)) {l : Fin r}
    (hl : (l : ℕ) < d) (k : Fin r) : mat r K g (Sum.inr k) (Sum.inl l) = 0 := by
  have h := (SymplecticFlag.mem_isoFlag.mp (spFlag_mulVec_single_mem hg hl)).1 k
  rwa [mulVec_single_one, col_apply] at h

theorem spFlag_inl_inl_eq_zero {d : ℕ} {g : StatedSp r K}
    (hg : g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K d)) {l : Fin r}
    (hl : (l : ℕ) < d) {k : Fin r} (hk : d ≤ (k : ℕ)) :
    mat r K g (Sum.inl k) (Sum.inl l) = 0 := by
  have h := (SymplecticFlag.mem_isoFlag.mp (spFlag_mulVec_single_mem hg hl)).2 k hk
  rwa [mulVec_single_one, col_apply] at h

theorem spFlag_inr_eq_zero {d : ℕ} {g : StatedSp r K}
    (hg : g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K d)) {m : Fin r}
    (hm : (m : ℕ) < d) {β : Fin r ⊕ Fin r} (hβ : ∀ j : Fin r, β = Sum.inr j → d ≤ (j : ℕ)) :
    mat r K g (Sum.inr m) β = 0 := by
  have hβo : (Pi.single β (1 : K) : Fin r ⊕ Fin r → K) ∈
      (pairedSympForm K r).orthogonal (SymplecticFlag.isoFlag r K d) := by
    rw [SymplecticFlag.mem_orthogonal_isoFlag]
    intro j hj
    exact Pi.single_eq_of_ne (fun h => absurd (hβ j h.symm) (not_le.mpr hj)) _
  have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hβo) _
    (spFlag_mulVec_single_mem (inv_mem hg) hm)
  have hinv : mat r K g *ᵥ (mat r K g⁻¹ *ᵥ Pi.single (Sum.inl m) 1) =
      Pi.single (Sum.inl m) 1 := by
    rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]
  have key := SymplecticHigher.pairedSympForm_mulVec g (mat r K g⁻¹ *ᵥ Pi.single (Sum.inl m) 1)
    (Pi.single β 1)
  rw [← mat_apply, hinv, SymplecticFlag.pairedSympForm_single_inl, mulVec_single_one,
    col_apply] at key
  rw [key]
  exact h0

theorem spFlag_mem_stabilizer {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {g : StatedSp r K}
    (hg : g ∈ flagStabilizer r K I) {i : ℕ} (hi : i ∈ I) :
    g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K i) := by
  have h := mem_flagStabilizer.mp hg i hi
  rwa [SymplecticFlag.flag, ite_eq_left (hI i hi)] at h

theorem spFlag_submatrix_mul {ι ι' : Type*} [Fintype ι] [Fintype ι'] {e : ι' → ι}
    (he : Function.Injective e) (x y : Matrix ι ι K)
    (h : ∀ i j k, k ∉ Set.range e → x (e i) k * y k (e j) = 0) :
    (x * y).submatrix e e = x.submatrix e e * y.submatrix e e := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  exact (Fintype.sum_of_injective e he _ _ (fun k hk => h i j k hk) fun _ => rfl).symm

@[expose] def spFlagShift (a b : ℕ) (hb : b ≤ r) : Fin (b - a) → Fin r :=
  fun i => ⟨a + i, by have := i.isLt; omega⟩

theorem spFlagShift_injective (a b : ℕ) (hb : b ≤ r) : Function.Injective (spFlagShift a b hb) :=
  fun i j hij => Fin.ext (by simpa [spFlagShift] using congrArg Fin.val hij)

theorem coe_spFlagShift (a b : ℕ) (hb : b ≤ r) (i : Fin (b - a)) :
    (spFlagShift a b hb i : ℕ) = a + i :=
  rfl

theorem mem_range_spFlagShift {a b : ℕ} (hb : b ≤ r) {j : Fin r} :
    j ∈ Set.range (spFlagShift a b hb) ↔ a ≤ (j : ℕ) ∧ (j : ℕ) < b := by
  constructor
  · rintro ⟨i, rfl⟩
    have := i.isLt
    simp only [coe_spFlagShift]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(j : ℕ) - a, by omega⟩, Fin.ext (by simp [coe_spFlagShift]; omega)⟩

@[expose] def spFlagCutMat (a b : ℕ) (hb : b ≤ r) (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    Matrix (Fin (b - a)) (Fin (b - a)) K :=
  g.submatrix (Sum.inl ∘ spFlagShift a b hb) (Sum.inl ∘ spFlagShift a b hb)

omit [Field K] in
theorem spFlagCutMat_apply (a b : ℕ) (hb : b ≤ r) (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (i j : Fin (b - a)) :
    spFlagCutMat a b hb g i j =
      g (Sum.inl (spFlagShift a b hb i)) (Sum.inl (spFlagShift a b hb j)) :=
  rfl

theorem spFlagCutMat_one (a b : ℕ) (hb : b ≤ r) :
    spFlagCutMat a b hb (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 :=
  submatrix_one _ (Sum.inl_injective.comp (spFlagShift_injective a b hb))

theorem spFlagCutMat_mul {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {a b : ℕ} (ha : a = 0 ∨ a ∈ I)
    (hbI : b ∈ I) {x y : StatedSp r K} (hx : x ∈ flagStabilizer r K I)
    (hy : y ∈ flagStabilizer r K I) :
    spFlagCutMat a b (hI b hbI) (mat r K (x * y)) =
      spFlagCutMat a b (hI b hbI) (mat r K x) * spFlagCutMat a b (hI b hbI) (mat r K y) := by
  have hyb := spFlag_mem_stabilizer hI hy hbI
  rw [map_mul]
  refine spFlag_submatrix_mul (Sum.inl_injective.comp (spFlagShift_injective a b _)) _ _
    fun i j k hk => ?_
  have hi := i.isLt
  have hj := j.isLt
  rcases k with m | m
  · by_cases hma : (m : ℕ) < a
    · rcases ha with rfl | ha
      · omega
      have := spFlag_inl_inl_eq_zero (spFlag_mem_stabilizer hI hx ha) hma
        (k := spFlagShift a b (hI b hbI) i) (by simp [coe_spFlagShift])
      simp only [Function.comp_apply, this, zero_mul]
    · have hmb : b ≤ (m : ℕ) := by
        by_contra hmb
        exact hk ⟨⟨(m : ℕ) - a, by omega⟩, by
          simp only [Function.comp_apply, Sum.inl.injEq]
          exact Fin.ext (by simp [coe_spFlagShift]; omega)⟩
      have := spFlag_inl_inl_eq_zero hyb (l := spFlagShift a b (hI b hbI) j)
        (by simp [coe_spFlagShift]; omega) hmb
      simp only [Function.comp_apply, this, mul_zero]
  · have := spFlag_inr_inl_eq_zero hyb (l := spFlagShift a b (hI b hbI) j)
      (by simp [coe_spFlagShift]; omega) m
    simp only [Function.comp_apply, this, mul_zero]

@[expose] noncomputable def spFlagCutHom {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {a b : ℕ}
    (ha : a = 0 ∨ a ∈ I) (hbI : b ∈ I) : flagStabilizer r K I →* GL (Fin (b - a)) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => spFlagCutMat a b (hI b hbI) (mat r K g)
      map_one' := by rw [Subgroup.coe_one, map_one, spFlagCutMat_one]
      map_mul' := fun x y => spFlagCutMat_mul hI ha hbI x.2 y.2 }

theorem coe_spFlagCutHom {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {a b : ℕ} (ha : a = 0 ∨ a ∈ I)
    (hbI : b ∈ I) (g : flagStabilizer r K I) :
    ((spFlagCutHom hI ha hbI g : GL (Fin (b - a)) K) : Matrix (Fin (b - a)) (Fin (b - a)) K) =
      spFlagCutMat a b (hI b hbI) (mat r K g) :=
  rfl

@[expose] def spFlagResIdx (t : ℕ) : Fin (r - t) ⊕ Fin (r - t) → Fin r ⊕ Fin r :=
  Sum.map (spFlagShift t r le_rfl) (spFlagShift t r le_rfl)

theorem spFlagResIdx_injective (t : ℕ) : Function.Injective (spFlagResIdx (r := r) t) :=
  Sum.map_injective.mpr ⟨spFlagShift_injective _ _ _, spFlagShift_injective _ _ _⟩

@[expose] def spFlagResMat (t : ℕ) (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    Matrix (Fin (r - t) ⊕ Fin (r - t)) (Fin (r - t) ⊕ Fin (r - t)) K :=
  g.submatrix (spFlagResIdx t) (spFlagResIdx t)

theorem spFlagResMat_one (t : ℕ) :
    spFlagResMat t (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 :=
  submatrix_one _ (spFlagResIdx_injective t)

theorem lt_of_not_mem_range_spFlagResIdx {t : ℕ} {k : Fin r ⊕ Fin r}
    (hk : k ∉ Set.range (spFlagResIdx (r := r) t)) :
    ∃ m : Fin r, (m : ℕ) < t ∧ (k = Sum.inl m ∨ k = Sum.inr m) := by
  have hmem : ∀ m : Fin r, t ≤ (m : ℕ) → m ∈ Set.range (spFlagShift t r le_rfl) := fun m hm =>
    (mem_range_spFlagShift le_rfl).mpr ⟨hm, m.isLt⟩
  rcases k with m | m
  · refine ⟨m, ?_, Or.inl rfl⟩
    by_contra hmt
    obtain ⟨i, hi⟩ := hmem m (not_lt.mp hmt)
    exact hk ⟨Sum.inl i, by simp [spFlagResIdx, hi]⟩
  · refine ⟨m, ?_, Or.inr rfl⟩
    by_contra hmt
    obtain ⟨i, hi⟩ := hmem m (not_lt.mp hmt)
    exact hk ⟨Sum.inr i, by simp [spFlagResIdx, hi]⟩

theorem spFlagResIdx_cases (t : ℕ) (α : Fin (r - t) ⊕ Fin (r - t)) :
    (∃ i : Fin (r - t), spFlagResIdx t α = Sum.inl (spFlagShift t r le_rfl i)) ∨
      ∃ i : Fin (r - t), spFlagResIdx t α = Sum.inr (spFlagShift t r le_rfl i) := by
  rcases α with i | i
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

theorem spFlag_res_inl_eq_zero {t : ℕ} {x : StatedSp r K}
    (hx : x ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K t)) {m : Fin r}
    (hm : (m : ℕ) < t) (α : Fin (r - t) ⊕ Fin (r - t)) :
    mat r K x (spFlagResIdx t α) (Sum.inl m) = 0 := by
  rcases spFlagResIdx_cases t α with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi]
  · exact spFlag_inl_inl_eq_zero hx hm (by simp [coe_spFlagShift])
  · exact spFlag_inr_inl_eq_zero hx hm _

theorem spFlag_inr_res_eq_zero {t : ℕ} {y : StatedSp r K}
    (hy : y ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K t)) {m : Fin r}
    (hm : (m : ℕ) < t) (β : Fin (r - t) ⊕ Fin (r - t)) :
    mat r K y (Sum.inr m) (spFlagResIdx t β) = 0 := by
  refine spFlag_inr_eq_zero hy hm fun j hj => ?_
  rcases spFlagResIdx_cases t β with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [hi] at hj
    exact absurd hj Sum.inl_ne_inr
  · rw [hi, Sum.inr.injEq] at hj
    rw [← hj, coe_spFlagShift]
    omega

theorem spFlagResMat_mul {t : ℕ} {x y : StatedSp r K}
    (hx : x ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K t))
    (hy : y ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K t)) :
    spFlagResMat t (mat r K (x * y)) = spFlagResMat t (mat r K x) * spFlagResMat t (mat r K y) := by
  rw [map_mul]
  refine spFlag_submatrix_mul (spFlagResIdx_injective t) _ _ fun α β k hk => ?_
  obtain ⟨m, hm, rfl | rfl⟩ := lt_of_not_mem_range_spFlagResIdx hk
  · rw [spFlag_res_inl_eq_zero hx hm, zero_mul]
  · rw [spFlag_inr_res_eq_zero hy hm, mul_zero]

theorem spFlagResMat_gram (t : ℕ) :
    spFlagResMat t (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks 0 1 (-1) 0 := by
  have hinj := spFlagShift_injective (r := r) t r le_rfl
  ext (i | i) (j | j) <;> simp [spFlagResMat, spFlagResIdx, one_apply, hinj.eq_iff]

theorem gram_mul_apply_inl (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (m : Fin r)
    (c : Fin r ⊕ Fin r) :
    ((fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * g) (Sum.inl m) c =
      g (Sum.inr m) c := by
  simp [mul_apply, Fintype.sum_sum_type, one_apply]

theorem gram_res_apply_eq_zero (t : ℕ) (α : Fin (r - t) ⊕ Fin (r - t)) {k : Fin r ⊕ Fin r}
    (hk : k ∉ Set.range (spFlagResIdx (r := r) t)) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (spFlagResIdx t α) k =
      0 := by
  obtain ⟨m, hm, rfl | rfl⟩ := lt_of_not_mem_range_spFlagResIdx hk <;>
    rcases α with i | i <;>
    simp only [spFlagResIdx, Sum.map_inl, Sum.map_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply,
      Matrix.one_apply] <;>
    · split_ifs with h
      · rw [← h, coe_spFlagShift] at hm
        omega
      · simp

theorem spFlagResMat_symplectic {t : ℕ} {g : StatedSp r K}
    (hg : g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K t)) :
    (spFlagResMat t (mat r K g))ᵀ * fromBlocks 0 1 (-1) 0 * spFlagResMat t (mat r K g) =
      fromBlocks 0 1 (-1) 0 := by
  have hsp := SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  rw [← mat_apply] at hsp
  have h1 : spFlagResMat t ((fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      mat r K g) = spFlagResMat t (fromBlocks 0 1 (-1) 0) * spFlagResMat t (mat r K g) :=
    spFlag_submatrix_mul (spFlagResIdx_injective t) _ _ fun α β k hk => by
      rw [gram_res_apply_eq_zero t α hk, zero_mul]
  have h2 : spFlagResMat t ((mat r K g)ᵀ *
      ((fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * mat r K g)) =
      spFlagResMat t (mat r K g)ᵀ *
        spFlagResMat t (fromBlocks 0 1 (-1) 0 * mat r K g) :=
    spFlag_submatrix_mul (spFlagResIdx_injective t) _ _ fun α β k hk => by
      obtain ⟨m, hm, rfl | rfl⟩ := lt_of_not_mem_range_spFlagResIdx hk
      · rw [gram_mul_apply_inl, spFlag_inr_res_eq_zero hg hm, mul_zero]
      · rw [transpose_apply, spFlag_inr_res_eq_zero hg hm, zero_mul]
  have h3 := congrArg (spFlagResMat t) hsp
  rw [Matrix.mul_assoc, h2, h1, spFlagResMat_gram] at h3
  rw [Matrix.mul_assoc]
  exact h3

@[expose] noncomputable def spFlagResMon {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) :
    flagStabilizer r K I →* Matrix (Fin (r - t) ⊕ Fin (r - t)) (Fin (r - t) ⊕ Fin (r - t)) K where
  toFun g := spFlagResMat t (mat r K g)
  map_one' := by rw [Subgroup.coe_one, map_one, spFlagResMat_one]
  map_mul' x y := spFlagResMat_mul (spFlag_mem_stabilizer hI x.2 htI)
    (spFlag_mem_stabilizer hI y.2 htI)

@[expose] noncomputable def spFlagResHom {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) :
    flagStabilizer r K I →* StatedSp (r - t) K :=
  (spFlagResMon hI htI).toHomUnits.codRestrict (StatedSp (r - t) K) fun g => by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, MonoidHom.coe_toHomUnits]
    exact spFlagResMat_symplectic (spFlag_mem_stabilizer hI g.2 htI)

theorem mat_spFlagResHom {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)
    (g : flagStabilizer r K I) :
    mat (r - t) K (spFlagResHom hI htI g) = spFlagResMat t (mat r K g) :=
  rfl

end CFSG.AGLEmbedding.LeviBlock
