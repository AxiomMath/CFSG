module

public import CFSG.LieType.SpecialLinear.Block222.Radicals

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

private def blk11 (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    Matrix (Fin 2) (Fin 2) F :=
  fun i j => M (Sum.inl i) (Sum.inl j)

private def blk12 (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    Matrix (Fin 2) (Fin c ⊕ Fin 2) F :=
  fun i k => M (Sum.inl i) (Sum.inr k)

private def blk21 (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    Matrix (Fin c ⊕ Fin 2) (Fin 2) F :=
  fun k a => M (Sum.inr k) (Sum.inl a)

private def blk22 (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    Matrix (Fin c) (Fin c) F :=
  fun s t => M (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inl t))

private def blk23 (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    Matrix (Fin c) (Fin 2) F :=
  fun s l => M (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inr l))

private def blk32 (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    Matrix (Fin 2) (Fin c) F :=
  fun l s => M (Sum.inr (Sum.inr l)) (Sum.inr (Sum.inl s))

private def blk33 (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    Matrix (Fin 2) (Fin 2) F :=
  fun l m => M (Sum.inr (Sum.inr l)) (Sum.inr (Sum.inr m))

private theorem eq_fromBlocks_upper
    (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F)
    (h21 : ∀ (k : Fin c ⊕ Fin 2) (a : Fin 2), M (Sum.inr k) (Sum.inl a) = 0)
    (h32 : ∀ (l : Fin 2) (s : Fin c), M (Sum.inr (Sum.inr l)) (Sum.inr (Sum.inl s)) = 0) :
    M = Matrix.fromBlocks (blk11 c F M) (blk12 c F M) 0
      (Matrix.fromBlocks (blk22 c F M) (blk23 c F M) 0 (blk33 c F M)) := by
  ext i j
  rcases i with a | (s | l) <;> rcases j with b | (t | m)
  · simp [blk11]
  · simp [blk12]
  · simp [blk12]
  · exact h21 (Sum.inl s) b
  · simp [blk22]
  · simp [blk23]
  · exact h21 (Sum.inr l) b
  · exact h32 l t
  · simp [blk33]

private theorem eq_fromBlocks_lower
    (M : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F)
    (h12 : ∀ (a : Fin 2) (k : Fin c ⊕ Fin 2), M (Sum.inl a) (Sum.inr k) = 0)
    (h23 : ∀ (s : Fin c) (m : Fin 2), M (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inr m)) = 0) :
    M = Matrix.fromBlocks (blk11 c F M) 0 (blk21 c F M)
      (Matrix.fromBlocks (blk22 c F M) 0 (blk32 c F M) (blk33 c F M)) := by
  ext i j
  rcases i with a | (s | l) <;> rcases j with b | (t | m)
  · simp [blk11]
  · exact h12 a (Sum.inl t)
  · exact h12 a (Sum.inr m)
  · simp [blk21]
  · simp [blk22]
  · exact h23 s m
  · simp [blk21]
  · simp [blk32]
  · simp [blk33]

private theorem det_eq_one_of_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (hup : A.IsUpperTriangular) (hd : ∀ i, A i i = 1) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular hup]
  simp [hd]

private theorem det_eq_one_of_lower {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (hlo : A.IsLowerTriangular) (hd : ∀ i, A i i = 1) : A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular A hlo]
  simp [hd]

private theorem inv_triDiagMat (A : Matrix (Fin 2) (Fin 2) F) (D : Matrix (Fin c) (Fin c) F)
    (G : Matrix (Fin 2) (Fin 2) F) (hA : A.det = 1) (hD : D.det = 1) (hG : G.det = 1) :
    (triDiagMat c F A D G)⁻¹ = triDiagMat c F A⁻¹ D⁻¹ G⁻¹ := by
  have hA' : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hA]; exact isUnit_one)
  have hD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D (by rw [hD]; exact isUnit_one)
  have hG' : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (by rw [hG]; exact isUnit_one)
  exact Matrix.inv_eq_right_inv (by rw [triDiagMat_mul, hA', hD', hG', triDiagMat_one])

theorem blockEmbed222_mem_U_of_entries [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
      SpecialLinearGroup (Fin 2) F}
    (h1d : ∀ i, (g.1 : Matrix (Fin 2) (Fin 2) F) i i = 1)
    (h1u : ∀ i j, j < i → (g.1 : Matrix (Fin 2) (Fin 2) F) i j = 0)
    (h2d : ∀ i, (g.2.1 : Matrix (Fin c) (Fin c) F) i i = 1)
    (h2u : ∀ i j, j < i → (g.2.1 : Matrix (Fin c) (Fin c) F) i j = 0)
    (h3d : ∀ i, (g.2.2 : Matrix (Fin 2) (Fin 2) F) i i = 1)
    (h3u : ∀ i j, j < i → (g.2.2 : Matrix (Fin 2) (Fin 2) F) i j = 0) :
    blockEmbed222 c F g ∈ (curtisDatum (c + 3) F p).U := by
  rw [mem_curtisDatum_U_iff]
  constructor
  · intro i
    obtain ⟨a, rfl⟩ := (e222 c).surjective i
    rcases a with a | (s | l)
    · rw [coe_blockEmbed222_apply_inl_inl]
      exact h1d a
    · rw [coe_blockEmbed222_apply_inr_inl_inl]
      exact h2d s
    · rw [coe_blockEmbed222_apply_inr_inr_inr]
      exact h3d l
  · intro i j hji
    exact blockEmbed222_mem_upper c F h1u h2u h3u i j hji

theorem blockEmbed222_mem_H_of_entries [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
      SpecialLinearGroup (Fin 2) F}
    (h1 : ∀ i j, i ≠ j → (g.1 : Matrix (Fin 2) (Fin 2) F) i j = 0)
    (h2 : ∀ i j, i ≠ j → (g.2.1 : Matrix (Fin c) (Fin c) F) i j = 0)
    (h3 : ∀ i j, i ≠ j → (g.2.2 : Matrix (Fin 2) (Fin 2) F) i j = 0) :
    blockEmbed222 c F g ∈ (curtisDatum (c + 3) F p).H := by
  rw [mem_curtisDatum_H_iff]
  exact blockEmbed222_mem_diagonal c F h1 h2 h3

theorem reindexSL_symm_apply (u : SpecialLinearGroup (Fin (c + 4)) F)
    (a b : Fin 2 ⊕ (Fin c ⊕ Fin 2)) :
    (((reindexSL c F).symm u : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
        Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) a b =
      (u : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c a) (e222 c b) := by
  have h := reindexSL_apply c F ((reindexSL c F).symm u) (e222 c a) (e222 c b)
  rw [MulEquiv.apply_symm_apply] at h
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  exact h.symm

theorem curtisDatum_U_le_block222_sup [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    (curtisDatum (c + 3) F p).U ≤ blockRadical222 c F ⊔
      ((curtisDatum (c + 3) F p).U ⊓ (blockEmbed222 c F).range) := by
  intro u hu
  let x : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F := (reindexSL c F).symm u
  have hxmat : ∀ a b, (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) a b =
      (u : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c a) (e222 c b) :=
    fun a b => reindexSL_symm_apply c F u a b
  have hu' := (mem_curtisDatum_U_iff (m := c + 3) (F := F) (p := p)).mp hu
  have hA_upper : (blk11 c F x).IsUpperTriangular := by
    intro i j hji
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inl i) (Sum.inl j) = 0 by
      rw [hxmat]
      exact hu'.2 _ _ ((e222_inl_lt_inl_iff c).mpr hji))
  have hA_diag : ∀ i, blk11 c F x i i = 1 := by
    intro i
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inl i) (Sum.inl i) = 1 by
      rw [hxmat]
      exact hu'.1 _)
  have hD_upper : (blk22 c F x).IsUpperTriangular := by
    intro i j hji
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) = 0 by
      rw [hxmat]
      exact hu'.2 _ _ ((e222_inr_inl_lt_iff c).mpr hji))
  have hD_diag : ∀ i, blk22 c F x i i = 1 := by
    intro i
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)) = 1 by
      rw [hxmat]
      exact hu'.1 _)
  have hG_upper : (blk33 c F x).IsUpperTriangular := by
    intro i j hji
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = 0 by
      rw [hxmat]
      exact hu'.2 _ _ ((e222_inr_inr_lt_iff c).mpr hji))
  have hG_diag : ∀ i, blk33 c F x i i = 1 := by
    intro i
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) = 1 by
      rw [hxmat]
      exact hu'.1 _)
  have hA_det : (blk11 c F x).det = 1 := det_eq_one_of_upper F _ hA_upper hA_diag
  have hD_det : (blk22 c F x).det = 1 := det_eq_one_of_upper F _ hD_upper hD_diag
  have hG_det : (blk33 c F x).det = 1 := det_eq_one_of_upper F _ hG_upper hG_diag
  have hxblocks : (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      Matrix.fromBlocks (blk11 c F x) (blk12 c F x) 0
        (Matrix.fromBlocks (blk22 c F x) (blk23 c F x) 0 (blk33 c F x)) := by
    refine eq_fromBlocks_upper c F _ ?_ ?_
    · intro k a
      rw [hxmat]
      rcases k with s | l
      · exact hu'.2 _ _ (e222_inl_lt_inr_inl c a s)
      · exact hu'.2 _ _ (e222_inl_lt_inr_inr c a l)
    · intro l s
      rw [hxmat]
      exact hu'.2 _ _ (e222_inr_inl_lt_inr_inr c s l)
  let g1 : SpecialLinearGroup (Fin 2) F := ⟨blk11 c F x, hA_det⟩
  let g2 : SpecialLinearGroup (Fin c) F := ⟨blk22 c F x, hD_det⟩
  let g3 : SpecialLinearGroup (Fin 2) F := ⟨blk33 c F x, hG_det⟩
  let d : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F := triDiagHom c F (g1, g2, g3)
  have hdmat : (d : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x) := rfl
  have hdet : (triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x)).det = 1 := by
    rw [det_triDiagMat, hA_det, hD_det, hG_det, mul_one, mul_one]
  have hadj : (triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x)).adjugate =
      (triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x))⁻¹ := by
    rw [← Matrix.inv_eq_right_inv (A := triDiagMat c F (blk11 c F x) (blk22 c F x)
      (blk33 c F x)) (B := (triDiagMat c F (blk11 c F x) (blk22 c F x)
        (blk33 c F x)).adjugate) (by rw [Matrix.mul_adjugate, hdet, one_smul])]
  have hdinv : ((d⁻¹ : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      triDiagMat c F (blk11 c F x)⁻¹ (blk22 c F x)⁻¹ (blk33 c F x)⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hdmat, hadj]
    exact inv_triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x) hA_det hD_det hG_det
  let q : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F := x * d⁻¹
  have hA' : blk11 c F x * (blk11 c F x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hA_det]; exact isUnit_one)
  have hD' : blk22 c F x * (blk22 c F x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hD_det]; exact isUnit_one)
  have hG' : blk33 c F x * (blk33 c F x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hG_det]; exact isUnit_one)
  have hqmat : (q : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      upFormMat c F (blk12 c F x * Matrix.fromBlocks (blk22 c F x)⁻¹ 0 0
        (blk33 c F x)⁻¹) (blk23 c F x * (blk33 c F x)⁻¹) := by
    show ((q : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, hxblocks, hdinv,
      show triDiagMat c F (blk11 c F x)⁻¹ (blk22 c F x)⁻¹ (blk33 c F x)⁻¹ =
        Matrix.fromBlocks (blk11 c F x)⁻¹ 0 0
          (Matrix.fromBlocks (blk22 c F x)⁻¹ 0 0 (blk33 c F x)⁻¹) from rfl,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hA', hD', hG']
    rfl
  have hq_eq : q = upFormSL c F _ _ := Subtype.ext hqmat
  have hq_mem : reindexSL c F q ∈ blockRadical222 c F := by
    rw [hq_eq]
    exact reindexSL_upFormSL_mem c F _ _
  have hd_U : blockEmbed222 c F (g1, g2, g3) ∈ (curtisDatum (c + 3) F p).U := by
    exact blockEmbed222_mem_U_of_entries c F p hA_diag hA_upper hD_diag hD_upper hG_diag hG_upper
  have hd_range : blockEmbed222 c F (g1, g2, g3) ∈ (blockEmbed222 c F).range :=
    ⟨(g1, g2, g3), rfl⟩
  have hu_eq : u = reindexSL c F q * blockEmbed222 c F (g1, g2, g3) := by
    calc u = reindexSL c F x := (MulEquiv.apply_symm_apply (reindexSL c F) u).symm
      _ = reindexSL c F (q * d) := by
            congr 1
            show x = (x * d⁻¹) * d
            group
      _ = reindexSL c F q * reindexSL c F d := map_mul _ _ _
      _ = reindexSL c F q * blockEmbed222 c F (g1, g2, g3) := rfl
  have hmul : reindexSL c F q * blockEmbed222 c F (g1, g2, g3) ∈
      blockRadical222 c F ⊔ ((curtisDatum (c + 3) F p).U ⊓ (blockEmbed222 c F).range) :=
    Subgroup.mul_mem_sup hq_mem ⟨hd_U, hd_range⟩
  rwa [← hu_eq] at hmul

theorem curtisDatum_L_le_block222_sup [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    (curtisDatum (c + 3) F p).L ≤ blockRadicalLower222 c F ⊔
      (blockEmbed222 c F).range := by
  intro u hu
  let x : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F := (reindexSL c F).symm u
  have hxmat : ∀ a b, (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) a b =
      (u : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c a) (e222 c b) :=
    fun a b => reindexSL_symm_apply c F u a b
  have hu' := (mem_curtisDatum_L_iff (m := c + 3) (F := F) (p := p)).mp hu
  have hA_lower : (blk11 c F x).IsLowerTriangular := by
    intro i j hij
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inl i) (Sum.inl j) = 0 by
      rw [hxmat]
      exact hu'.2 _ _ ((e222_inl_lt_inl_iff c).mpr hij))
  have hA_diag : ∀ i, blk11 c F x i i = 1 := by
    intro i
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inl i) (Sum.inl i) = 1 by
      rw [hxmat]
      exact hu'.1 _)
  have hD_lower : (blk22 c F x).IsLowerTriangular := by
    intro i j hij
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) = 0 by
      rw [hxmat]
      exact hu'.2 _ _ ((e222_inr_inl_lt_iff c).mpr hij))
  have hD_diag : ∀ i, blk22 c F x i i = 1 := by
    intro i
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)) = 1 by
      rw [hxmat]
      exact hu'.1 _)
  have hG_lower : (blk33 c F x).IsLowerTriangular := by
    intro i j hij
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = 0 by
      rw [hxmat]
      exact hu'.2 _ _ ((e222_inr_inr_lt_iff c).mpr hij))
  have hG_diag : ∀ i, blk33 c F x i i = 1 := by
    intro i
    exact (show (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) = 1 by
      rw [hxmat]
      exact hu'.1 _)
  have hA_det : (blk11 c F x).det = 1 := det_eq_one_of_lower F _ hA_lower hA_diag
  have hD_det : (blk22 c F x).det = 1 := det_eq_one_of_lower F _ hD_lower hD_diag
  have hG_det : (blk33 c F x).det = 1 := det_eq_one_of_lower F _ hG_lower hG_diag
  have hxblocks : (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      Matrix.fromBlocks (blk11 c F x) 0 (blk21 c F x)
        (Matrix.fromBlocks (blk22 c F x) 0 (blk32 c F x) (blk33 c F x)) := by
    refine eq_fromBlocks_lower c F _ ?_ ?_
    · intro a k
      rw [hxmat]
      rcases k with s | l
      · exact hu'.2 _ _ (e222_inl_lt_inr_inl c a s)
      · exact hu'.2 _ _ (e222_inl_lt_inr_inr c a l)
    · intro s l
      rw [hxmat]
      exact hu'.2 _ _ (e222_inr_inl_lt_inr_inr c s l)
  let g1 : SpecialLinearGroup (Fin 2) F := ⟨blk11 c F x, hA_det⟩
  let g2 : SpecialLinearGroup (Fin c) F := ⟨blk22 c F x, hD_det⟩
  let g3 : SpecialLinearGroup (Fin 2) F := ⟨blk33 c F x, hG_det⟩
  let d : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F := triDiagHom c F (g1, g2, g3)
  have hdmat : (d : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x) := rfl
  have hdet : (triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x)).det = 1 := by
    rw [det_triDiagMat, hA_det, hD_det, hG_det, mul_one, mul_one]
  have hadj : (triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x)).adjugate =
      (triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x))⁻¹ := by
    rw [← Matrix.inv_eq_right_inv (A := triDiagMat c F (blk11 c F x) (blk22 c F x)
      (blk33 c F x)) (B := (triDiagMat c F (blk11 c F x) (blk22 c F x)
        (blk33 c F x)).adjugate) (by rw [Matrix.mul_adjugate, hdet, one_smul])]
  have hdinv : ((d⁻¹ : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      triDiagMat c F (blk11 c F x)⁻¹ (blk22 c F x)⁻¹ (blk33 c F x)⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hdmat, hadj]
    exact inv_triDiagMat c F (blk11 c F x) (blk22 c F x) (blk33 c F x) hA_det hD_det hG_det
  let q : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F := x * d⁻¹
  have hA' : blk11 c F x * (blk11 c F x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hA_det]; exact isUnit_one)
  have hD' : blk22 c F x * (blk22 c F x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hD_det]; exact isUnit_one)
  have hG' : blk33 c F x * (blk33 c F x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hG_det]; exact isUnit_one)
  have hqmat : (q : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      lowFormMat c F (blk21 c F x * (blk11 c F x)⁻¹)
        (blk32 c F x * (blk22 c F x)⁻¹) := by
    show ((q : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, hxblocks, hdinv,
      show triDiagMat c F (blk11 c F x)⁻¹ (blk22 c F x)⁻¹ (blk33 c F x)⁻¹ =
        Matrix.fromBlocks (blk11 c F x)⁻¹ 0 0
          (Matrix.fromBlocks (blk22 c F x)⁻¹ 0 0 (blk33 c F x)⁻¹) from rfl,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hA', hD', hG']
    rfl
  have hq_eq : q = lowFormSL c F _ _ := Subtype.ext hqmat
  have hq_mem : reindexSL c F q ∈ blockRadicalLower222 c F := by
    rw [hq_eq]
    exact reindexSL_lowFormSL_mem c F _ _
  have hd_range : blockEmbed222 c F (g1, g2, g3) ∈ (blockEmbed222 c F).range :=
    ⟨(g1, g2, g3), rfl⟩
  have hu_eq : u = reindexSL c F q * blockEmbed222 c F (g1, g2, g3) := by
    calc u = reindexSL c F x := (MulEquiv.apply_symm_apply (reindexSL c F) u).symm
      _ = reindexSL c F (q * d) := by
            congr 1
            show x = (x * d⁻¹) * d
            group
      _ = reindexSL c F q * reindexSL c F d := map_mul _ _ _
      _ = reindexSL c F q * blockEmbed222 c F (g1, g2, g3) := rfl
  have hmul : reindexSL c F q * blockEmbed222 c F (g1, g2, g3) ∈
      blockRadicalLower222 c F ⊔ (blockEmbed222 c F).range :=
    Subgroup.mul_mem_sup hq_mem hd_range
  rwa [← hu_eq] at hmul

end

end CFSG.LieType.SpecialLinear
