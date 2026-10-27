module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SpecialLinear.CurtisDatum.RankOne
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

theorem fixSub_mapsTo_of_intertwine {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] {ρ : Representation k G V} {α : MulAut G} {N : Subgroup G}
    (hN : N.map (α : G →* G) = N) {T : V →ₗ[k] V}
    (hT : ∀ (g : G) (v : V), T (ρ g v) = ρ (α g) (T v)) :
    ∀ x ∈ fixSub ρ N, T x ∈ fixSub ρ N := by
  intro x hx
  rw [mem_fixSub] at hx ⊢
  intro n hn
  have hpre : (α.symm) n ∈ N := by
    have hn' : n ∈ N.map (α : G →* G) := by rw [hN]; exact hn
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hn'
    have e1 : α.symm n = m := by
      rw [← hmn]
      exact MulEquiv.symm_apply_apply α m
    rw [e1]; exact hm
  calc ρ n (T x) = ρ (α (α.symm n)) (T x) := by rw [MulEquiv.apply_symm_apply]
    _ = T (ρ (α.symm n) x) := (hT (α.symm n) x).symm
    _ = T x := by rw [hx _ hpre]

@[expose] def e222 : Fin 2 ⊕ (Fin c ⊕ Fin 2) ≃ Fin (c + 4) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) (finSumFinEquiv (m := c) (n := 2))).trans
    ((finSumFinEquiv (m := 2) (n := c + 2)).trans (finCongr (by omega)))

theorem e222_inl (a : Fin 2) : e222 c (Sum.inl a) = ⟨a, by omega⟩ := by
  ext
  simp [e222]

theorem e222_inr_inl (s : Fin c) : e222 c (Sum.inr (Sum.inl s)) = ⟨s + 2, by omega⟩ := by
  ext
  simp [e222]

theorem e222_inr_inr (k : Fin 2) : e222 c (Sum.inr (Sum.inr k)) = ⟨c + 2 + k, by omega⟩ := by
  ext
  simp [e222]
  omega

theorem e222_inl_zero : e222 c (Sum.inl (0 : Fin 2)) = (0 : Fin (c + 4)) := by
  rw [e222_inl]
  exact Fin.ext rfl

theorem e222_inl_one : e222 c (Sum.inl (1 : Fin 2)) = (1 : Fin (c + 4)) := by
  rw [e222_inl]
  exact Fin.ext rfl

theorem e222_inr_inr_zero :
    e222 c (Sum.inr (Sum.inr (0 : Fin 2))) = (⟨c + 2, by omega⟩ : Fin (c + 4)) := by
  rw [e222_inr_inr]
  exact Fin.ext rfl

theorem e222_inr_inr_one :
    e222 c (Sum.inr (Sum.inr (1 : Fin 2))) = (⟨c + 3, by omega⟩ : Fin (c + 4)) := by
  rw [e222_inr_inr]
  exact Fin.ext (by simp)

theorem e222_inl_lt_inr_inr (a : Fin 2) (l : Fin 2) :
    e222 c (Sum.inl a) < e222 c (Sum.inr (Sum.inr l)) := by
  rw [e222_inl, e222_inr_inr, Fin.lt_def]
  simp
  omega

theorem e222_inl_lt_inr_inl (a : Fin 2) (s : Fin c) :
    e222 c (Sum.inl a) < e222 c (Sum.inr (Sum.inl s)) := by
  rw [e222_inl, e222_inr_inl, Fin.lt_def]
  simp
  omega

theorem e222_inr_inl_lt_inr_inr (s : Fin c) (k : Fin 2) :
    e222 c (Sum.inr (Sum.inl s)) < e222 c (Sum.inr (Sum.inr k)) := by
  rw [e222_inr_inl, e222_inr_inr, Fin.lt_def]
  simp
  omega

@[expose] def blk222 (i : Fin (c + 4)) : Fin 3 :=
  if (i : ℕ) < 2 then 0 else if (i : ℕ) < c + 2 then 1 else 2

@[expose] def blkSum222 : Fin 2 ⊕ (Fin c ⊕ Fin 2) → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

theorem blk222_e222 (x : Fin 2 ⊕ (Fin c ⊕ Fin 2)) : blk222 c (e222 c x) = blkSum222 c x := by
  rcases x with a | (s | k)
  · rw [e222_inl, blkSum222]
    show (if ((a : ℕ)) < 2 then (0 : Fin 3) else if ((a : ℕ)) < c + 2 then 1 else 2) = 0
    rw [if_pos a.isLt]
  · rw [e222_inr_inl, blkSum222]
    show (if ((s : ℕ) + 2) < 2 then (0 : Fin 3) else if ((s : ℕ) + 2) < c + 2 then 1 else 2) = 1
    rw [if_neg (by omega), if_pos (by omega)]
  · rw [e222_inr_inr, blkSum222]
    show (if ((c : ℕ) + 2 + (k : ℕ)) < 2 then (0 : Fin 3)
      else if ((c : ℕ) + 2 + (k : ℕ)) < c + 2 then 1 else 2) = 2
    rw [if_neg (by omega), if_neg (by omega)]

theorem blk222_le_of_le {i j : Fin (c + 4)} (h : i ≤ j) : blk222 c i ≤ blk222 c j := by
  simp only [blk222]
  split_ifs <;> omega

@[expose] def triDiagMat (A : Matrix (Fin 2) (Fin 2) F) (D : Matrix (Fin c) (Fin c) F)
    (G : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
  Matrix.fromBlocks A 0 0 (Matrix.fromBlocks D 0 0 G)

theorem triDiagMat_mul (A : Matrix (Fin 2) (Fin 2) F) (D : Matrix (Fin c) (Fin c) F)
    (G : Matrix (Fin 2) (Fin 2) F) (A' : Matrix (Fin 2) (Fin 2) F)
    (D' : Matrix (Fin c) (Fin c) F) (G' : Matrix (Fin 2) (Fin 2) F) :
    triDiagMat c F A D G * triDiagMat c F A' D' G' =
      triDiagMat c F (A * A') (D * D') (G * G') := by
  rw [triDiagMat, triDiagMat, triDiagMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem triDiagMat_one :
    triDiagMat c F (1 : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  rw [triDiagMat, show Matrix.fromBlocks (1 : Matrix (Fin c) (Fin c) F) 0 0 1 = 1 from
    Matrix.fromBlocks_one, Matrix.fromBlocks_one]

theorem det_triDiagMat (A : Matrix (Fin 2) (Fin 2) F) (D : Matrix (Fin c) (Fin c) F)
    (G : Matrix (Fin 2) (Fin 2) F) :
    (triDiagMat c F A D G).det = A.det * D.det * G.det := by
  rw [triDiagMat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  ring

theorem triDiagMat_transvection_left {i j : Fin 2} (x : F) :
    triDiagMat c F (1 + Matrix.single i j x) 1 1 =
      (1 : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) +
        Matrix.single (Sum.inl (β := Fin c ⊕ Fin 2) i) (Sum.inl (β := Fin c ⊕ Fin 2) j) x := by
  ext a b
  rcases a with a | (s | k) <;> rcases b with b' | (t | l) <;>
    simp [triDiagMat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem triDiagMat_transvection_right {i j : Fin 2} (x : F) :
    triDiagMat c F 1 1 (1 + Matrix.single i j x) =
      (1 : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) +
        Matrix.single (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) x := by
  ext a b
  rcases a with a | (s | k) <;> rcases b with b' | (t | l) <;>
    simp [triDiagMat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem triDiagMat_diagonal (f : Fin 2 → F) (g : Fin c → F) (h : Fin 2 → F) :
    triDiagMat c F (Matrix.diagonal f) (Matrix.diagonal g) (Matrix.diagonal h) =
      Matrix.diagonal (Sum.elim f (Sum.elim g h)) := by
  rw [triDiagMat, Matrix.fromBlocks_diagonal, Matrix.fromBlocks_diagonal]

@[expose] noncomputable def triDiagHom :
    SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
        SpecialLinearGroup (Fin 2) F →*
      SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F where
  toFun g := ⟨triDiagMat c F (g.1 : Matrix (Fin 2) (Fin 2) F)
      (g.2.1 : Matrix (Fin c) (Fin c) F) (g.2.2 : Matrix (Fin 2) (Fin 2) F), by
    rw [det_triDiagMat, g.1.2, g.2.1.2, g.2.2.2, mul_one, mul_one]⟩
  map_one' := by
    apply Subtype.ext
    exact triDiagMat_one c F
  map_mul' g h := by
    apply Subtype.ext
    show triDiagMat c F ((g.1 * h.1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        ((g.2.1 * h.2.1 : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F)
        ((g.2.2 * h.2.2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      triDiagMat c F (g.1 : Matrix (Fin 2) (Fin 2) F) (g.2.1 : Matrix (Fin c) (Fin c) F)
          (g.2.2 : Matrix (Fin 2) (Fin 2) F) *
        triDiagMat c F (h.1 : Matrix (Fin 2) (Fin 2) F) (h.2.1 : Matrix (Fin c) (Fin c) F)
          (h.2.2 : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, triDiagMat_mul]

@[expose] noncomputable def reindexSL :
    SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F ≃* SpecialLinearGroup (Fin (c + 4)) F where
  toFun g := ⟨(Matrix.reindexAlgEquiv F F (e222 c)) (g : Matrix _ _ F), by
    rw [Matrix.det_reindexAlgEquiv]; exact g.2⟩
  invFun g := ⟨(Matrix.reindexAlgEquiv F F (e222 c).symm) (g : Matrix _ _ F), by
    rw [Matrix.det_reindexAlgEquiv]; exact g.2⟩
  left_inv g := by
    apply Subtype.ext
    show (Matrix.reindexAlgEquiv F F (e222 c).symm)
      ((Matrix.reindexAlgEquiv F F (e222 c)) (g : Matrix _ _ F)) = (g : Matrix _ _ F)
    exact AlgEquiv.symm_apply_apply (Matrix.reindexAlgEquiv F F (e222 c)) (g : Matrix _ _ F)
  right_inv g := by
    apply Subtype.ext
    show (Matrix.reindexAlgEquiv F F (e222 c))
      ((Matrix.reindexAlgEquiv F F (e222 c).symm) (g : Matrix _ _ F)) = (g : Matrix _ _ F)
    exact AlgEquiv.apply_symm_apply (Matrix.reindexAlgEquiv F F (e222 c)) (g : Matrix _ _ F)
  map_mul' g h := by
    apply Subtype.ext
    show (Matrix.reindexAlgEquiv F F (e222 c))
        ((g : Matrix _ _ F) * (h : Matrix _ _ F)) =
      (Matrix.reindexAlgEquiv F F (e222 c)) (g : Matrix _ _ F) *
        (Matrix.reindexAlgEquiv F F (e222 c)) (h : Matrix _ _ F)
    rw [map_mul]

theorem coe_reindexSL (g : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    ((reindexSL c F g : SpecialLinearGroup (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      (Matrix.reindexAlgEquiv F F (e222 c)) (g : Matrix _ _ F) := rfl

theorem reindexAlgEquiv_single (a b : Fin 2 ⊕ (Fin c ⊕ Fin 2)) (x : F) :
    (Matrix.reindexAlgEquiv F F (e222 c)) (Matrix.single a b x) =
      Matrix.single (e222 c a) (e222 c b) x := by
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv]
  rfl

@[expose] noncomputable def blockEmbed222 :
    SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
        SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin (c + 4)) F :=
  (reindexSL c F).toMonoidHom.comp (triDiagHom c F)

theorem coe_blockEmbed222 (g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
    SpecialLinearGroup (Fin 2) F) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      (Matrix.reindexAlgEquiv F F (e222 c))
        (triDiagMat c F (g.1 : Matrix (Fin 2) (Fin 2) F) (g.2.1 : Matrix (Fin c) (Fin c) F)
          (g.2.2 : Matrix (Fin 2) (Fin 2) F)) := rfl

theorem coe_blockEmbed222_apply_inl_inl (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inl i)) (e222 c (Sum.inl j)) =
      (g.1 : Matrix (Fin 2) (Fin 2) F) i j := by
  rw [coe_blockEmbed222, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  simp [triDiagMat]

theorem coe_blockEmbed222_apply_inl_inr (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) (i : Fin 2)
    (k : Fin c ⊕ Fin 2) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inl i)) (e222 c (Sum.inr k)) = 0 := by
  rw [coe_blockEmbed222, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  simp [triDiagMat]

theorem coe_blockEmbed222_apply_inr_inl (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) (k : Fin c ⊕ Fin 2)
    (i : Fin 2) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr k)) (e222 c (Sum.inl i)) = 0 := by
  rw [coe_blockEmbed222, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  simp [triDiagMat]

theorem coe_blockEmbed222_apply_inr_inl_inl (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) (s t : Fin c) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inl s)))
        (e222 c (Sum.inr (Sum.inl t))) = (g.2.1 : Matrix (Fin c) (Fin c) F) s t := by
  rw [coe_blockEmbed222, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  simp [triDiagMat]

theorem coe_blockEmbed222_apply_inr_inl_inr (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) (s : Fin c) (k : Fin 2) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inl s)))
        (e222 c (Sum.inr (Sum.inr k))) = 0 := by
  rw [coe_blockEmbed222, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  simp [triDiagMat]

theorem coe_blockEmbed222_apply_inr_inr_inl (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) (k : Fin 2) (s : Fin c) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inr k)))
        (e222 c (Sum.inr (Sum.inl s))) = 0 := by
  rw [coe_blockEmbed222, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  simp [triDiagMat]

theorem coe_blockEmbed222_apply_inr_inr_inr (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) (k l : Fin 2) :
    ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inr k)))
        (e222 c (Sum.inr (Sum.inr l))) = (g.2.2 : Matrix (Fin 2) (Fin 2) F) k l := by
  rw [coe_blockEmbed222, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  simp [triDiagMat]

theorem blockEmbed222_injective : Function.Injective (blockEmbed222 c F) := by
  intro g h hgh
  have hm : ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
      Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      ((blockEmbed222 c F h : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) := congrArg Subtype.val hgh
  have h1 : g.1 = h.1 := by
    apply Subtype.ext
    ext i j
    rw [← coe_blockEmbed222_apply_inl_inl c F g i j,
      ← coe_blockEmbed222_apply_inl_inl c F h i j, hm]
  have h2 : g.2.1 = h.2.1 := by
    apply Subtype.ext
    ext i j
    rw [← coe_blockEmbed222_apply_inr_inl_inl c F g i j,
      ← coe_blockEmbed222_apply_inr_inl_inl c F h i j, hm]
  have h3 : g.2.2 = h.2.2 := by
    apply Subtype.ext
    ext i j
    rw [← coe_blockEmbed222_apply_inr_inr_inr c F g i j,
      ← coe_blockEmbed222_apply_inr_inr_inr c F h i j, hm]
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem triDiagHom_transvection_left {i j : Fin 2} (hij : i ≠ j) (x : F) :
    triDiagHom c F (SpecialLinearGroup.transvection hij x, 1, 1) =
      SpecialLinearGroup.transvection (Sum.inl_injective.ne hij) x := by
  apply Subtype.ext
  change triDiagMat c F ((SpecialLinearGroup.transvection hij x : Matrix (Fin 2) (Fin 2) F)) 1 1 =
    (1 + Matrix.single (Sum.inl (β := Fin c ⊕ Fin 2) i)
      (Sum.inl (β := Fin c ⊕ Fin 2) j) x : Matrix _ _ F)
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  exact triDiagMat_transvection_left c F x

theorem triDiagHom_transvection_right {i j : Fin 2} (hij : i ≠ j) (x : F) :
    triDiagHom c F (1, 1, SpecialLinearGroup.transvection hij x) =
      SpecialLinearGroup.transvection (Sum.inr_injective.ne (Sum.inr_injective.ne hij)) x := by
  apply Subtype.ext
  change triDiagMat c F 1 1 ((SpecialLinearGroup.transvection hij x : Matrix (Fin 2) (Fin 2) F)) =
    (1 + Matrix.single (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) x : Matrix _ _ F)
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  exact triDiagMat_transvection_right c F x

theorem reindexSL_transvection {a b : Fin 2 ⊕ (Fin c ⊕ Fin 2)} (hab : a ≠ b) (x : F) :
    reindexSL c F (SpecialLinearGroup.transvection hab x) =
      SpecialLinearGroup.transvection ((e222 c).injective.ne hab) x := by
  apply Subtype.ext
  rw [coe_reindexSL, Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one,
    reindexAlgEquiv_single, Matrix.SpecialLinearGroup.transvection_coe]

theorem blockEmbed222_transvection_left {i j : Fin 2} (hij : i ≠ j) (x : F) :
    blockEmbed222 c F (SpecialLinearGroup.transvection hij x, 1, 1) =
      SpecialLinearGroup.transvection ((e222 c).injective.ne (Sum.inl_injective.ne hij)) x := by
  rw [blockEmbed222, MonoidHom.comp_apply, triDiagHom_transvection_left]
  exact reindexSL_transvection c F _ x

theorem blockEmbed222_transvection_right {i j : Fin 2} (hij : i ≠ j) (x : F) :
    blockEmbed222 c F (1, 1, SpecialLinearGroup.transvection hij x) =
      SpecialLinearGroup.transvection
        ((e222 c).injective.ne (Sum.inr_injective.ne (Sum.inr_injective.ne hij))) x := by
  rw [blockEmbed222, MonoidHom.comp_apply, triDiagHom_transvection_right]
  exact reindexSL_transvection c F _ x

theorem reindexAlgEquiv_diagonal (d : Fin 2 ⊕ (Fin c ⊕ Fin 2) → F) :
    (Matrix.reindexAlgEquiv F F (e222 c)) (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d ((e222 c).symm i)) := by
  ext i j
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h ((e222 c).symm.injective hh))]

theorem fin_castSucc_zero_eq : ((0 : Fin 1).castSucc : Fin 2) = 0 := Fin.ext rfl

theorem fin_succ_zero_eq : ((0 : Fin 1).succ : Fin 2) = 1 := Fin.ext rfl

theorem node222_left_castSucc :
    ((⟨0, by omega⟩ : Fin (c + 3)).castSucc : Fin (c + 4)) =
      e222 c (Sum.inl (0 : Fin 2)) := (e222_inl_zero c).symm

theorem node222_left_succ :
    ((⟨0, by omega⟩ : Fin (c + 3)).succ : Fin (c + 4)) =
      e222 c (Sum.inl (1 : Fin 2)) := (e222_inl_one c).symm

theorem node222_right_castSucc :
    ((⟨c + 2, by omega⟩ : Fin (c + 3)).castSucc : Fin (c + 4)) =
      e222 c (Sum.inr (Sum.inr (0 : Fin 2))) := (e222_inr_inr_zero c).symm

theorem node222_right_succ :
    ((⟨c + 2, by omega⟩ : Fin (c + 3)).succ : Fin (c + 4)) =
      e222 c (Sum.inr (Sum.inr (1 : Fin 2))) := (e222_inr_inr_one c).symm

theorem blockEmbed222_hdiag_left (u : Fˣ) :
    blockEmbed222 c F (hdiag 1 F (0 : Fin 1) u, 1, 1) =
      hdiag (c + 3) F (⟨0, by omega⟩ : Fin (c + 3)) u := by
  apply Subtype.ext
  rw [coe_blockEmbed222, hdiag, hdiag, Matrix.SpecialLinearGroup.diag2nUnit_coe,
    Matrix.SpecialLinearGroup.diag2nUnit_coe,
    show ((1 : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) =
      Matrix.diagonal (fun _ => (1 : F)) from Matrix.diagonal_one.symm,
    show ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal (fun _ => (1 : F)) from Matrix.diagonal_one.symm,
    triDiagMat_diagonal, reindexAlgEquiv_diagonal]
  congr 1
  funext i
  rcases h : (e222 c).symm i with a | (s | k)
  · have hi : i = e222 c (Sum.inl a) := by rw [← h, Equiv.apply_symm_apply]
    rw [hi, node222_left_castSucc, node222_left_succ, fin_castSucc_zero_eq, fin_succ_zero_eq]
    simp only [Sum.elim_inl, (e222 c).injective.eq_iff]
    simp
  · have hi : i = e222 c (Sum.inr (Sum.inl s)) := by rw [← h, Equiv.apply_symm_apply]
    rw [hi, node222_left_castSucc, node222_left_succ]
    simp only [Sum.elim_inr, Sum.elim_inl, (e222 c).injective.eq_iff]
    simp
  · have hi : i = e222 c (Sum.inr (Sum.inr k)) := by rw [← h, Equiv.apply_symm_apply]
    rw [hi, node222_left_castSucc, node222_left_succ]
    simp only [Sum.elim_inr, (e222 c).injective.eq_iff]
    simp

theorem blockEmbed222_hdiag_right (u : Fˣ) :
    blockEmbed222 c F (1, 1, hdiag 1 F (0 : Fin 1) u) =
      hdiag (c + 3) F (⟨c + 2, by omega⟩ : Fin (c + 3)) u := by
  apply Subtype.ext
  rw [coe_blockEmbed222, hdiag, hdiag, Matrix.SpecialLinearGroup.diag2nUnit_coe,
    Matrix.SpecialLinearGroup.diag2nUnit_coe,
    show ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal (fun _ => (1 : F)) from Matrix.diagonal_one.symm,
    show ((1 : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) =
      Matrix.diagonal (fun _ => (1 : F)) from Matrix.diagonal_one.symm,
    triDiagMat_diagonal, reindexAlgEquiv_diagonal]
  congr 1
  funext i
  rcases h : (e222 c).symm i with a | (s | k)
  · have hi : i = e222 c (Sum.inl a) := by rw [← h, Equiv.apply_symm_apply]
    rw [hi, node222_right_castSucc, node222_right_succ]
    simp only [Sum.elim_inl, (e222 c).injective.eq_iff]
    simp
  · have hi : i = e222 c (Sum.inr (Sum.inl s)) := by rw [← h, Equiv.apply_symm_apply]
    rw [hi, node222_right_castSucc, node222_right_succ]
    simp only [Sum.elim_inr, Sum.elim_inl, (e222 c).injective.eq_iff]
    simp
  · have hi : i = e222 c (Sum.inr (Sum.inr k)) := by rw [← h, Equiv.apply_symm_apply]
    rw [hi, node222_right_castSucc, node222_right_succ, fin_castSucc_zero_eq, fin_succ_zero_eq]
    simp only [Sum.elim_inr, (e222 c).injective.eq_iff]
    simp

theorem transvection_congr {n : ℕ} {i j i' j' : Fin n} (hi : i = i') (hj : j = j')
    (hij : i ≠ j) (x : F) :
    SpecialLinearGroup.transvection hij x =
      SpecialLinearGroup.transvection (hi ▸ hj ▸ hij) x := by
  subst hi
  subst hj
  exact Subtype.ext rfl

theorem prod_triple_left (a1 a2 a3 : SpecialLinearGroup (Fin 2) F) :
    (a1 * a2 * a3, (1 : SpecialLinearGroup (Fin c) F), (1 : SpecialLinearGroup (Fin 2) F)) =
      (a1, 1, 1) * (a2, 1, 1) * (a3, 1, 1) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem prod_triple_right (a1 a2 a3 : SpecialLinearGroup (Fin 2) F) :
    ((1 : SpecialLinearGroup (Fin 2) F), (1 : SpecialLinearGroup (Fin c) F), a1 * a2 * a3) =
      (1, 1, a1) * (1, 1, a2) * (1, 1, a3) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem blockEmbed222_weylRep_left :
    blockEmbed222 c F (weylRep 1 F (0 : Fin 1), 1, 1) =
      weylRep (c + 3) F (⟨0, by omega⟩ : Fin (c + 3)) := by
  unfold weylRep
  rw [prod_triple_left, map_mul, map_mul, blockEmbed222_transvection_left,
    blockEmbed222_transvection_left]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  rw [node222_left_castSucc, node222_left_succ, fin_castSucc_zero_eq, fin_succ_zero_eq]

theorem blockEmbed222_weylRep_right :
    blockEmbed222 c F (1, 1, weylRep 1 F (0 : Fin 1)) =
      weylRep (c + 3) F (⟨c + 2, by omega⟩ : Fin (c + 3)) := by
  unfold weylRep
  rw [prod_triple_right, map_mul, map_mul, blockEmbed222_transvection_right,
    blockEmbed222_transvection_right]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  rw [node222_right_castSucc, node222_right_succ, fin_castSucc_zero_eq, fin_succ_zero_eq]

theorem e222_inl_lt_inl_iff {a b : Fin 2} :
    e222 c (Sum.inl b) < e222 c (Sum.inl a) ↔ b < a := by
  rw [e222_inl, e222_inl, Fin.lt_def, Fin.lt_def]

theorem e222_inr_inl_lt_iff {s t : Fin c} :
    e222 c (Sum.inr (Sum.inl t)) < e222 c (Sum.inr (Sum.inl s)) ↔ t < s := by
  rw [e222_inr_inl, e222_inr_inl, Fin.lt_def, Fin.lt_def]
  simp

theorem e222_inr_inr_lt_iff {k l : Fin 2} :
    e222 c (Sum.inr (Sum.inr l)) < e222 c (Sum.inr (Sum.inr k)) ↔ l < k := by
  rw [e222_inr_inr, e222_inr_inr, Fin.lt_def, Fin.lt_def]
  simp

theorem blockEmbed222_mem_upper {g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F}
    (h1 : ∀ i j, j < i → (g.1 : Matrix (Fin 2) (Fin 2) F) i j = 0)
    (h2 : ∀ i j, j < i → (g.2.1 : Matrix (Fin c) (Fin c) F) i j = 0)
    (h3 : ∀ i j, j < i → (g.2.2 : Matrix (Fin 2) (Fin 2) F) i j = 0) :
    ∀ i j, j < i → ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
      Matrix (Fin (c + 4)) (Fin (c + 4)) F) i j = 0 := by
  intro i j hji
  obtain ⟨x, rfl⟩ := (e222 c).surjective i
  obtain ⟨y, rfl⟩ := (e222 c).surjective j
  rcases x with a | (s | k) <;> rcases y with b | (t | l)
  · rw [coe_blockEmbed222_apply_inl_inl]
    exact h1 _ _ ((e222_inl_lt_inl_iff c).mp hji)
  · rw [coe_blockEmbed222_apply_inl_inr]
  · rw [coe_blockEmbed222_apply_inl_inr]
  · rw [coe_blockEmbed222_apply_inr_inl]
  · rw [coe_blockEmbed222_apply_inr_inl_inl]
    exact h2 _ _ ((e222_inr_inl_lt_iff c).mp hji)
  · rw [coe_blockEmbed222_apply_inr_inl_inr]
  · rw [coe_blockEmbed222_apply_inr_inl]
  · rw [coe_blockEmbed222_apply_inr_inr_inl]
  · rw [coe_blockEmbed222_apply_inr_inr_inr]
    exact h3 _ _ ((e222_inr_inr_lt_iff c).mp hji)

theorem blockEmbed222_mem_diagonal {g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F}
    (h1 : ∀ i j, i ≠ j → (g.1 : Matrix (Fin 2) (Fin 2) F) i j = 0)
    (h2 : ∀ i j, i ≠ j → (g.2.1 : Matrix (Fin c) (Fin c) F) i j = 0)
    (h3 : ∀ i j, i ≠ j → (g.2.2 : Matrix (Fin 2) (Fin 2) F) i j = 0) :
    ∀ i j, i ≠ j → ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
      Matrix (Fin (c + 4)) (Fin (c + 4)) F) i j = 0 := by
  intro i j hij
  have hxy : (e222 c).symm i ≠ (e222 c).symm j := fun h => hij ((e222 c).symm.injective h)
  obtain ⟨x, rfl⟩ := (e222 c).surjective i
  obtain ⟨y, rfl⟩ := (e222 c).surjective j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hxy
  rcases x with a | (s | k) <;> rcases y with b | (t | l)
  · rw [coe_blockEmbed222_apply_inl_inl]
    exact h1 _ _ (fun h => hxy (by rw [h]))
  · rw [coe_blockEmbed222_apply_inl_inr]
  · rw [coe_blockEmbed222_apply_inl_inr]
  · rw [coe_blockEmbed222_apply_inr_inl]
  · rw [coe_blockEmbed222_apply_inr_inl_inl]
    exact h2 _ _ (fun h => hxy (by rw [h]))
  · rw [coe_blockEmbed222_apply_inr_inl_inr]
  · rw [coe_blockEmbed222_apply_inr_inl]
  · rw [coe_blockEmbed222_apply_inr_inr_inl]
  · rw [coe_blockEmbed222_apply_inr_inr_inr]
    exact h3 _ _ (fun h => hxy (by rw [h]))

end

end CFSG.LieType.SpecialLinear
