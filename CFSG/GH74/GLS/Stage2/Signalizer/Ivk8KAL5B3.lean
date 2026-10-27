module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL5Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProjFix

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

section Defs

variable (F : Type) [Field F]

abbrev kaL5B3E : Fin 3 ⊕ Fin 2 ≃ Fin 5 := finSumFinEquiv

@[expose] def kaL5B3Mat : Matrix (Fin 5) (Fin 5) F :=
  diagBlock (1 : Matrix (Fin 3) (Fin 3) F) (-1 : Matrix (Fin 2) (Fin 2) F)

theorem kaL5B3Mat_mul_self : kaL5B3Mat F * kaL5B3Mat F = 1 := by
  rw [kaL5B3Mat, diagBlock_mul, mul_one, neg_mul_neg, mul_one, diagBlock_one]

@[expose] def kaL5B3GL : GL (Fin 5) F :=
  ⟨kaL5B3Mat F, kaL5B3Mat F, kaL5B3Mat_mul_self F, kaL5B3Mat_mul_self F⟩

theorem coe_kaL5B3GL : ((kaL5B3GL F : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = kaL5B3Mat F :=
  rfl

theorem kaL5B3GL_mul_self : kaL5B3GL F * kaL5B3GL F = 1 :=
  Units.ext (by rw [Units.val_mul, coe_kaL5B3GL, kaL5B3Mat_mul_self, Units.val_one])

theorem kaL5B3GL_inv : (kaL5B3GL F)⁻¹ = kaL5B3GL F :=
  inv_eq_of_mul_eq_one_right (kaL5B3GL_mul_self F)

theorem kaL5B3E_inl_val (i : Fin 3) : ((kaL5B3E (Sum.inl i) : Fin 5) : ℕ) = i := rfl

theorem kaL5B3E_inr_val (j : Fin 2) : ((kaL5B3E (Sum.inr j) : Fin 5) : ℕ) = 3 + j := rfl

theorem kaL5B3Mat_eq_diagonal :
    kaL5B3Mat F = diagonal fun i : Fin 5 => if (i : ℕ) < 3 then (1 : F) else -1 := by
  ext x y
  obtain ⟨a, rfl⟩ := kaL5B3E.surjective x
  obtain ⟨b, rfl⟩ := kaL5B3E.surjective y
  rw [kaL5B3Mat, diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, diagonal_apply]
  rcases a with i | i <;> rcases b with j | j
  · rw [fromBlocks_apply₁₁]
    by_cases hij : i = j
    · subst hij
      simp [kaL5B3E_inl_val, i.isLt]
    · simp [hij, Matrix.one_apply_ne hij]
  · simp
  · simp
  · rw [fromBlocks_apply₂₂]
    by_cases hij : i = j
    · subst hij
      have : ¬ (3 + (i : ℕ) < 3) := by omega
      simp [kaL5B3E_inr_val, this]
    · simp [hij, Matrix.one_apply_ne hij]

end Defs

section Frame

variable {F : Type} [Field F]

theorem kaL5B3_exists_frame (hK : ringChar F ≠ 2) {B : GL (Fin 5) F} (hB : B * B = 1)
    (h3 : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 3) :
    ∃ P : GL (Fin 5) F, B = P * kaL5B3GL F * P⁻¹ := by
  have hBm : (B : Matrix (Fin 5) (Fin 5) F) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  have hDd : (D : Matrix (Fin 5) (Fin 5) F) = kaL5B3Mat F := by
    rw [hD, kaL5B3Mat_eq_diagonal]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, h3, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  refine ⟨P, ?_⟩
  have hDe : D = kaL5B3GL F := Units.ext hDd
  rw [← hDe, ← hPD]
  group

end Frame

section Diag

variable {F : Type} [Field F]

theorem kaL5B3_det_diagBlock (X : Matrix (Fin 3) (Fin 3) F) (Y : Matrix (Fin 2) (Fin 2) F) :
    (diagBlock X Y : Matrix (Fin 5) (Fin 5) F).det = X.det * Y.det := by
  rw [diagBlock, det_reindex_self, det_fromBlocks_zero₁₂]

theorem kaL5B3_diagBlock_inj {X X' : Matrix (Fin 3) (Fin 3) F} {Y Y' : Matrix (Fin 2) (Fin 2) F}
    (h : (diagBlock X Y : Matrix (Fin 5) (Fin 5) F) = diagBlock X' Y') : X = X' ∧ Y = Y' := by
  have h1 : fromBlocks X 0 0 Y = fromBlocks X' 0 0 Y' := by
    have := congrArg (reindex kaL5B3E.symm kaL5B3E.symm) h
    simpa [diagBlock] using this
  have := fromBlocks_inj.1 h1
  exact ⟨this.1, this.2.2.2⟩

theorem kaL5B3_diagBlock_add (X X' : Matrix (Fin 3) (Fin 3) F) (Y Y' : Matrix (Fin 2) (Fin 2) F) :
    (diagBlock (X + X') (Y + Y') : Matrix (Fin 5) (Fin 5) F) = diagBlock X Y + diagBlock X' Y' := by
  have h : (fromBlocks (X + X') 0 0 (Y + Y') : Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) F) =
      fromBlocks X 0 0 Y + fromBlocks X' 0 0 Y' := by
    rw [fromBlocks_add]
    simp
  rw [diagBlock, diagBlock, diagBlock, h, reindex_apply, reindex_apply, reindex_apply,
    submatrix_add]
  rfl

theorem kaL5B3_single_inl (i j : Fin 3) (c : F) :
    (diagBlock (Matrix.single i j c) (0 : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 5) (Fin 5) F) =
      Matrix.single (kaL5B3E (Sum.inl i)) (kaL5B3E (Sum.inl j)) c := by
  ext x y
  obtain ⟨a, rfl⟩ := kaL5B3E.surjective x
  obtain ⟨b, rfl⟩ := kaL5B3E.surjective y
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with k | k <;> rcases b with l | l
  · rw [fromBlocks_apply₁₁]
    simp [Matrix.single_apply]
  · rw [fromBlocks_apply₁₂]
    simp
  · rw [fromBlocks_apply₂₁]
    simp
  · rw [fromBlocks_apply₂₂]
    simp

theorem kaL5B3_single_inr (i j : Fin 2) (c : F) :
    (diagBlock (0 : Matrix (Fin 3) (Fin 3) F) (Matrix.single i j c) : Matrix (Fin 5) (Fin 5) F) =
      Matrix.single (kaL5B3E (Sum.inr i)) (kaL5B3E (Sum.inr j)) c := by
  ext x y
  obtain ⟨a, rfl⟩ := kaL5B3E.surjective x
  obtain ⟨b, rfl⟩ := kaL5B3E.surjective y
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with k | k <;> rcases b with l | l
  · rw [fromBlocks_apply₁₁]
    simp
  · rw [fromBlocks_apply₁₂]
    simp
  · rw [fromBlocks_apply₂₁]
    simp
  · rw [fromBlocks_apply₂₂]
    simp [Matrix.single_apply]

theorem kaL5B3_blocks (h2 : (2 : F) ≠ 0) {c : Matrix (Fin 5) (Fin 5) F}
    (hc : c * kaL5B3Mat F = kaL5B3Mat F * c) :
    c = diagBlock (Matrix.of fun i j : Fin 3 => c (kaL5B3E (Sum.inl i)) (kaL5B3E (Sum.inl j)))
      (Matrix.of fun i j : Fin 2 => c (kaL5B3E (Sum.inr i)) (kaL5B3E (Sum.inr j))) := by
  rw [kaL5B3Mat_eq_diagonal] at hc
  have key : ∀ x y : Fin 5, (x : ℕ) < 3 → ¬ (y : ℕ) < 3 → c x y = 0 ∧ c y x = 0 := by
    intro x y hx hy
    have h1 := congrFun (congrFun hc x) y
    have h2' := congrFun (congrFun hc y) x
    rw [mul_diagonal, diagonal_mul] at h1 h2'
    simp only [hx, hy, ↓reduceIte] at h1 h2'
    constructor
    · have : (2 : F) * c x y = 0 := by linear_combination -h1
      exact (mul_eq_zero.1 this).resolve_left h2
    · have : (2 : F) * c y x = 0 := by linear_combination h2'
      exact (mul_eq_zero.1 this).resolve_left h2
  ext x y
  obtain ⟨a, rfl⟩ := kaL5B3E.surjective x
  obtain ⟨b, rfl⟩ := kaL5B3E.surjective y
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with i | i <;> rcases b with j | j
  · rw [fromBlocks_apply₁₁]
    rfl
  · rw [fromBlocks_apply₁₂]
    exact (key _ _ (by rw [kaL5B3E_inl_val]; exact i.isLt)
      (by rw [kaL5B3E_inr_val]; omega)).1
  · rw [fromBlocks_apply₂₁]
    exact (key _ _ (by rw [kaL5B3E_inl_val]; exact j.isLt)
      (by rw [kaL5B3E_inr_val]; omega)).2
  · rw [fromBlocks_apply₂₂]
    rfl

end Diag

section Hom

variable {F : Type} [Field F]

@[expose] def kaL5B3Hom1 (F : Type) [Field F] : SL(3, F) →* SL(5, F) where
  toFun X := ⟨diagBlock (X : Matrix (Fin 3) (Fin 3) F) (1 : Matrix (Fin 2) (Fin 2) F), by
    rw [kaL5B3_det_diagBlock, X.2, Matrix.det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    show diagBlock (1 : Matrix (Fin 3) (Fin 3) F) (1 : Matrix (Fin 2) (Fin 2) F) = 1
    exact diagBlock_one)
  map_mul' X Y := Subtype.ext (by
    show diagBlock ((X * Y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) (1 : Matrix (Fin 2) (Fin 2) F) =
      diagBlock (X : Matrix (Fin 3) (Fin 3) F) 1 * diagBlock (Y : Matrix (Fin 3) (Fin 3) F) 1
    rw [diagBlock_mul, mul_one, Matrix.SpecialLinearGroup.coe_mul])

@[expose] def kaL5B3Hom2 (F : Type) [Field F] : SL(2, F) →* SL(5, F) where
  toFun X := ⟨diagBlock (1 : Matrix (Fin 3) (Fin 3) F) (X : Matrix (Fin 2) (Fin 2) F), by
    rw [kaL5B3_det_diagBlock, X.2, Matrix.det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    show diagBlock (1 : Matrix (Fin 3) (Fin 3) F) (1 : Matrix (Fin 2) (Fin 2) F) = 1
    exact diagBlock_one)
  map_mul' X Y := Subtype.ext (by
    show diagBlock (1 : Matrix (Fin 3) (Fin 3) F) ((X * Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      diagBlock 1 (X : Matrix (Fin 2) (Fin 2) F) * diagBlock 1 (Y : Matrix (Fin 2) (Fin 2) F)
    rw [diagBlock_mul, mul_one, Matrix.SpecialLinearGroup.coe_mul])

theorem coe_kaL5B3Hom1 (X : SL(3, F)) :
    ((kaL5B3Hom1 F X : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) =
      diagBlock (X : Matrix (Fin 3) (Fin 3) F) (1 : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem coe_kaL5B3Hom2 (X : SL(2, F)) :
    ((kaL5B3Hom2 F X : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) =
      diagBlock (1 : Matrix (Fin 3) (Fin 3) F) (X : Matrix (Fin 2) (Fin 2) F) :=
  rfl

end Hom

section Blocks

variable {F : Type} [Field F]

theorem kaL5B3_mem_cent {g : SL(5, F)} :
    g ∈ kaSlCent5 (kaL5B3GL F) ↔
      (g : Matrix (Fin 5) (Fin 5) F) * kaL5B3Mat F = kaL5B3Mat F * g := by
  rw [kaSlCent5, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 := congrArg (fun u : GL (Fin 5) F => (u : Matrix (Fin 5) (Fin 5) F))
      (h (kaL5B3GL F) (Set.mem_singleton _))
    simp only [Units.val_mul, coe_kaL5B3GL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h1
    exact h1.symm
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Units.ext
    simp only [Units.val_mul, coe_kaL5B3GL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact h.symm

theorem kaL5B3_blk_forms (h2 : (2 : F) ≠ 0) {g : SL(5, F)} (hg : g ∈ kaSlCent5 (kaL5B3GL F)) :
    ∃ (a a' : Matrix (Fin 3) (Fin 3) F) (b b' : Matrix (Fin 2) (Fin 2) F),
      (g : Matrix (Fin 5) (Fin 5) F) = diagBlock a b ∧
      ((g⁻¹ : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) = diagBlock a' b' ∧
      a * a' = 1 ∧ b * b' = 1 := by
  obtain ⟨a, b, hg1⟩ : ∃ (a : Matrix (Fin 3) (Fin 3) F) (b : Matrix (Fin 2) (Fin 2) F),
      (g : Matrix (Fin 5) (Fin 5) F) = diagBlock a b :=
    ⟨_, _, kaL5B3_blocks h2 (kaL5B3_mem_cent.1 hg)⟩
  obtain ⟨a', b', hg2⟩ : ∃ (a : Matrix (Fin 3) (Fin 3) F) (b : Matrix (Fin 2) (Fin 2) F),
      ((g⁻¹ : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) = diagBlock a b :=
    ⟨_, _, kaL5B3_blocks h2 (kaL5B3_mem_cent.1 (inv_mem hg))⟩
  refine ⟨a, a', b, b', hg1, hg2, ?_⟩
  have hgg : (diagBlock (a * a') (b * b') : Matrix (Fin 5) (Fin 5) F) = diagBlock 1 1 := by
    rw [← diagBlock_mul, ← hg1, ← hg2, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, diagBlock_one]
  exact kaL5B3_diagBlock_inj hgg

theorem kaL5B3_conj_hom1 (h2 : (2 : F) ≠ 0) {g : SL(5, F)} (hg : g ∈ kaSlCent5 (kaL5B3GL F))
    (s : SL(3, F)) : ∃ t : SL(3, F), g * kaL5B3Hom1 F s * g⁻¹ = kaL5B3Hom1 F t := by
  obtain ⟨a, a', b, b', hg1, hg2, haa, hbb⟩ := kaL5B3_blk_forms h2 hg
  refine ⟨⟨a * (s : Matrix (Fin 3) (Fin 3) F) * a', ?_⟩, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, haa, Matrix.det_one]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_kaL5B3Hom1,
      hg1, hg2, diagBlock_mul, diagBlock_mul, mul_one, hbb]
    rfl

theorem kaL5B3_conj_hom2 (h2 : (2 : F) ≠ 0) {g : SL(5, F)} (hg : g ∈ kaSlCent5 (kaL5B3GL F))
    (s : SL(2, F)) : ∃ t : SL(2, F), g * kaL5B3Hom2 F s * g⁻¹ = kaL5B3Hom2 F t := by
  obtain ⟨a, a', b, b', hg1, hg2, haa, hbb⟩ := kaL5B3_blk_forms h2 hg
  refine ⟨⟨b * (s : Matrix (Fin 2) (Fin 2) F) * b', ?_⟩, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, hbb, Matrix.det_one]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_kaL5B3Hom2,
      hg1, hg2, diagBlock_mul, diagBlock_mul, mul_one, haa]
    rfl

end Blocks

section Subgroups

variable {F : Type} [Field F]

@[expose] def kaL5B3R0 (F : Type) [Field F] : Subgroup (projectiveSL 5 F) :=
  (kaSlCent5 (kaL5B3GL F)).map (proj 5 F)

@[expose] def kaL5B3L1 (F : Type) [Field F] : Subgroup (projectiveSL 5 F) :=
  ((proj 5 F).comp (kaL5B3Hom1 F)).range

@[expose] def kaL5B3L2 (F : Type) [Field F] : Subgroup (projectiveSL 5 F) :=
  ((proj 5 F).comp (kaL5B3Hom2 F)).range

@[expose] def kaL5B3L (F : Type) [Field F] : Subgroup (projectiveSL 5 F) :=
  kaL5B3L1 F ⊔ kaL5B3L2 F

theorem kaL5B3_hom1_mem_cent (s : SL(3, F)) : kaL5B3Hom1 F s ∈ kaSlCent5 (kaL5B3GL F) := by
  rw [kaL5B3_mem_cent, coe_kaL5B3Hom1, kaL5B3Mat, diagBlock_mul, diagBlock_mul]
  simp only [mul_one, one_mul]

theorem kaL5B3_hom2_mem_cent (s : SL(2, F)) : kaL5B3Hom2 F s ∈ kaSlCent5 (kaL5B3GL F) := by
  rw [kaL5B3_mem_cent, coe_kaL5B3Hom2, kaL5B3Mat, diagBlock_mul, diagBlock_mul]
  simp only [mul_one, mul_neg_one, neg_one_mul]

theorem kaL5B3_L1_le_R0 : kaL5B3L1 F ≤ kaL5B3R0 F := by
  rintro _ ⟨s, rfl⟩
  exact ⟨kaL5B3Hom1 F s, kaL5B3_hom1_mem_cent s, rfl⟩

theorem kaL5B3_L2_le_R0 : kaL5B3L2 F ≤ kaL5B3R0 F := by
  rintro _ ⟨s, rfl⟩
  exact ⟨kaL5B3Hom2 F s, kaL5B3_hom2_mem_cent s, rfl⟩

theorem kaL5B3_L_le_R0 : kaL5B3L F ≤ kaL5B3R0 F :=
  sup_le kaL5B3_L1_le_R0 kaL5B3_L2_le_R0

theorem kaL5B3_conj_mem_L1 (h2 : (2 : F) ≠ 0) {x l : projectiveSL 5 F} (hx : x ∈ kaL5B3R0 F)
    (hl : l ∈ kaL5B3L1 F) : x * l * x⁻¹ ∈ kaL5B3L1 F := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hl
  obtain ⟨t, ht⟩ := kaL5B3_conj_hom1 h2 hg s
  refine ⟨t, ?_⟩
  show proj 5 F (kaL5B3Hom1 F t) = proj 5 F g * proj 5 F (kaL5B3Hom1 F s) * (proj 5 F g)⁻¹
  rw [← ht, map_mul, map_mul, map_inv]

theorem kaL5B3_conj_mem_L2 (h2 : (2 : F) ≠ 0) {x l : projectiveSL 5 F} (hx : x ∈ kaL5B3R0 F)
    (hl : l ∈ kaL5B3L2 F) : x * l * x⁻¹ ∈ kaL5B3L2 F := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hl
  obtain ⟨t, ht⟩ := kaL5B3_conj_hom2 h2 hg s
  refine ⟨t, ?_⟩
  show proj 5 F (kaL5B3Hom2 F t) = proj 5 F g * proj 5 F (kaL5B3Hom2 F s) * (proj 5 F g)⁻¹
  rw [← ht, map_mul, map_mul, map_inv]

theorem kaL5B3_normalizes_L1 (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ kaL5B3R0 F, x ∈ normalizer (kaL5B3L1 F : Set (projectiveSL 5 F)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => kaL5B3_conj_mem_L1 h2 hx hl, fun hl => ?_⟩
  have := kaL5B3_conj_mem_L1 h2 (inv_mem hx) hl
  simpa [mul_assoc] using this

theorem kaL5B3_normalizes_L2 (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ kaL5B3R0 F, x ∈ normalizer (kaL5B3L2 F : Set (projectiveSL 5 F)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => kaL5B3_conj_mem_L2 h2 hx hl, fun hl => ?_⟩
  have := kaL5B3_conj_mem_L2 h2 (inv_mem hx) hl
  simpa [mul_assoc] using this

theorem kaL5B3_normalizes_L (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ kaL5B3R0 F, x ∈ normalizer (kaL5B3L F : Set (projectiveSL 5 F)) :=
  fun x hx => Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨kaL5B3_normalizes_L1 h2 x hx, kaL5B3_normalizes_L2 h2 x hx⟩

theorem kaL5B3_map_le_fix {x : projectiveSL 5 F} (hx : x ∈ kaL5B3R0 F) :
    conjAut 5 F (kaL5B3GL F) x = x := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hc := kaL5B3_mem_cent.1 hg
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, kaL5B3GL_inv, coe_kaL5B3GL, ← hc, Matrix.mul_assoc,
    kaL5B3Mat_mul_self, Matrix.mul_one]

end Subgroups

section Perfect

variable {F : Type} [Field F]

theorem kaL5B3_quasisimple {n : ℕ} (hn : 2 ≤ n) (h : 3 ≤ n ∨ ∃ s : Finset F, s.card = 4) :
    CFSG.IsQuasisimple SL(n, F) := by
  have hperf : Group.IsPerfect SL(n, F) := CFSG.LinearGroups.special_linear_isPerfect hn h
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := n) hn h
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative (SL(n, F) ⧸ Subgroup.center SL(n, F)) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (SL(n, F) ⧸ Subgroup.center SL(n, F)) this

omit [Field F] in
theorem kaL5B3_card_four [Finite F] (h4 : 4 ≤ Nat.card F) : ∃ s : Finset F, s.card = 4 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4)
  exact ⟨s, hs⟩

theorem kaL5B3_quasi3 [Finite F] : CFSG.IsQuasisimple SL(3, F) :=
  kaL5B3_quasisimple (by norm_num) (Or.inl le_rfl)

theorem kaL5B3_quasi2 [Finite F] (h4 : 4 ≤ Nat.card F) : CFSG.IsQuasisimple SL(2, F) :=
  kaL5B3_quasisimple le_rfl (Or.inr (kaL5B3_card_four h4))

theorem kaL5B3_perf1 [Finite F] : ⁅kaL5B3L1 F, kaL5B3L1 F⁆ = kaL5B3L1 F := by
  have hP := kaL5B3_quasi3 (F := F)
  have hJ : kaL5B3L1 F = (⊤ : Subgroup SL(3, F)).map ((proj 5 F).comp (kaL5B3Hom1 F)) :=
    MonoidHom.range_eq_map _
  rw [hJ, ← Subgroup.map_commutator, ← _root_.commutator_def, Group.isPerfect_def.mp hP.1]

theorem kaL5B3_perf2 [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅kaL5B3L2 F, kaL5B3L2 F⁆ = kaL5B3L2 F := by
  have hP := kaL5B3_quasi2 h4
  have hJ : kaL5B3L2 F = (⊤ : Subgroup SL(2, F)).map ((proj 5 F).comp (kaL5B3Hom2 F)) :=
    MonoidHom.range_eq_map _
  rw [hJ, ← Subgroup.map_commutator, ← _root_.commutator_def, Group.isPerfect_def.mp hP.1]

theorem kaL5B3_perf [Finite F] (h4 : 4 ≤ Nat.card F) : ⁅kaL5B3L F, kaL5B3L F⁆ = kaL5B3L F := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact (kaL5B3L F).mul_mem ((kaL5B3L F).mul_mem ((kaL5B3L F).mul_mem ha hb)
      ((kaL5B3L F).inv_mem ha)) ((kaL5B3L F).inv_mem hb)
  · calc kaL5B3L1 F = ⁅kaL5B3L1 F, kaL5B3L1 F⁆ := kaL5B3_perf1.symm
      _ ≤ ⁅kaL5B3L F, kaL5B3L F⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc kaL5B3L2 F = ⁅kaL5B3L2 F, kaL5B3L2 F⁆ := (kaL5B3_perf2 h4).symm
      _ ≤ ⁅kaL5B3L F, kaL5B3L F⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem kaL5B3_hLp [Finite F] (h4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup (projectiveSL 5 F), M ≤ kaL5B3L F →
      IsPGroup p ↥M → (∀ l ∈ kaL5B3L F, l ∈ normalizer (M : Set (projectiveSL 5 F))) →
        ∀ m ∈ M, ∀ l ∈ kaL5B3L F, m * l = l * m := by
  intro p hp _ M hML hMp hMn
  have hc1 : ∀ m ∈ M, ∀ l ∈ kaL5B3L1 F, m * l = l * m :=
    ka_centralizes_of_perfect (p := p) (kaL5B3L1 F) M kaL5B3_perf1
      (fun l hl => hMn l (Subgroup.mem_sup_left hl))
      (fun x hx => kaL5B3_normalizes_L1 h2 x (kaL5B3_L_le_R0 (hML hx))) hMp
      (fun M' hM'L hM'p hM'n =>
        ka_central_of_quasisimple_image ((proj 5 F).comp (kaL5B3Hom1 F)) kaL5B3_quasi3 hp M' hM'L
          hM'p hM'n)
  have hc2 : ∀ m ∈ M, ∀ l ∈ kaL5B3L2 F, m * l = l * m :=
    ka_centralizes_of_perfect (p := p) (kaL5B3L2 F) M (kaL5B3_perf2 h4)
      (fun l hl => hMn l (Subgroup.mem_sup_right hl))
      (fun x hx => kaL5B3_normalizes_L2 h2 x (kaL5B3_L_le_R0 (hML hx))) hMp
      (fun M' hM'L hM'p hM'n =>
        ka_central_of_quasisimple_image ((proj 5 F).comp (kaL5B3Hom2 F)) (kaL5B3_quasi2 h4) hp M'
          hM'L hM'p hM'n)
  intro m hm l hl
  have hcent : kaL5B3L F ≤ Subgroup.centralizer ({m} : Set (projectiveSL 5 F)) := by
    refine sup_le (fun l hl => ?_) (fun l hl => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hc1 m hm l hl
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hc2 m hm l hl
  have := hcent hl
  rw [Subgroup.mem_centralizer_iff] at this
  exact this m (Set.mem_singleton m)

end Perfect

section Fix

variable {F : Type} [Field F]

theorem kaL5B3_fix_scalar {n : ℕ} (A : GL (Fin n) F) (g : SL(n, F))
    (h : conjAut n F A (proj n F g) = proj n F g) :
    ∃ μ : F, (g : Matrix (Fin n) (Fin n) F) =
      μ • (A.val * (g : Matrix (Fin n) (Fin n) F) * A⁻¹.val) := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  refine ⟨(c : F), ?_⟩
  set S := ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A g with hS
  have hSmat : (S : Matrix (Fin n) (Fin n) F) =
      A.val * (g : Matrix (Fin n) (Fin n) F) * A⁻¹.val := by
    rw [hS, coe_slConjugation]
  have hscal : (Matrix.scalar (Fin n) (c : F) : Matrix (Fin n) (Fin n) F) = (c : F) • 1 := by
    rw [smul_one_eq_diagonal, Matrix.scalar_apply]
  calc (g : Matrix (Fin n) (Fin n) F) = ((S * (S⁻¹ * g) : SL(n, F)) : Matrix (Fin n) (Fin n) F) :=
        congrArg Subtype.val (mul_inv_cancel_left S g).symm
    _ = (S : Matrix (Fin n) (Fin n) F) * ((S⁻¹ * g : SL(n, F)) : Matrix (Fin n) (Fin n) F) :=
        Matrix.SpecialLinearGroup.coe_mul _ _
    _ = _ := by rw [hc, hscal, hSmat, Matrix.mul_smul, Matrix.mul_one]

theorem kaL5B3_commute_single {n : ℕ} (A : GL (Fin n) F) {i j : Fin n} (hij : i ≠ j)
    (g : SL(n, F)) (hg : (g : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single i j 1)
    (h : conjAut n F A (proj n F g) = proj n F g) :
    Commute (Matrix.single i j (1 : F)) A.val := by
  obtain ⟨μ, hμ⟩ := kaL5B3_fix_scalar A g h
  set N : Matrix (Fin n) (Fin n) F := Matrix.single i j 1 with hN
  have hN0 : N ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 i) j
    simp [hN] at this
  have hN2 : N * N = 0 := by
    rw [hN, Matrix.single_mul_single_of_ne (1 : F) i j i hij.symm 1]
  set Nt : Matrix (Fin n) (Fin n) F := A.val * N * A⁻¹.val with hNt
  have hNt2 : Nt * Nt = 0 := by
    calc Nt * Nt = A.val * (N * (A⁻¹.val * A.val) * N) * A⁻¹.val := by
          simp only [hNt, Matrix.mul_assoc]
      _ = 0 := by rw [Units.inv_mul, Matrix.mul_one, hN2, Matrix.mul_zero, Matrix.zero_mul]
  rw [hg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv] at hμ
  have hμ1 : μ = 1 :=
    ka_proj_scalar_eq_one N Nt hN0 hN2 hNt2 1 1 μ (by simpa only [one_smul] using hμ)
  rw [hμ1, one_smul] at hμ
  have hNN : N = Nt := add_left_cancel hμ
  show N * A.val = A.val * N
  calc N * A.val = Nt * A.val := by rw [← hNN]
    _ = A.val * N * (A⁻¹.val * A.val) := by simp only [hNt, Matrix.mul_assoc]
    _ = A.val * N := by rw [Units.inv_mul, Matrix.mul_one]

theorem kaL5B3_root_inl {i j : Fin 3} (hij : i ≠ j) (c : F) :
    ∃ g : SL(5, F), (g : Matrix (Fin 5) (Fin 5) F) =
        1 + Matrix.single (kaL5B3E (Sum.inl i)) (kaL5B3E (Sum.inl j)) c ∧
      proj 5 F g ∈ kaL5B3L F := by
  let t : SL(3, F) := ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩
  refine ⟨kaL5B3Hom1 F t, ?_, Subgroup.mem_sup_left ⟨t, rfl⟩⟩
  have h1 := kaL5B3_diagBlock_add (1 : Matrix (Fin 3) (Fin 3) F) (Matrix.single i j c)
    (1 : Matrix (Fin 2) (Fin 2) F) 0
  rw [diagBlock_one, add_zero] at h1
  rw [coe_kaL5B3Hom1, ← kaL5B3_single_inl]
  exact h1

theorem kaL5B3_root_inr {i j : Fin 2} (hij : i ≠ j) (c : F) :
    ∃ g : SL(5, F), (g : Matrix (Fin 5) (Fin 5) F) =
        1 + Matrix.single (kaL5B3E (Sum.inr i)) (kaL5B3E (Sum.inr j)) c ∧
      proj 5 F g ∈ kaL5B3L F := by
  let t : SL(2, F) := ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩
  refine ⟨kaL5B3Hom2 F t, ?_, Subgroup.mem_sup_right ⟨t, rfl⟩⟩
  have h1 := kaL5B3_diagBlock_add (1 : Matrix (Fin 3) (Fin 3) F) 0 (1 : Matrix (Fin 2) (Fin 2) F)
    (Matrix.single i j c)
  rw [diagBlock_one, add_zero] at h1
  rw [coe_kaL5B3Hom2, ← kaL5B3_single_inr]
  exact h1

end Fix

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def kaL5B3TorHom (F : Type) [Field F] : Fˣ →* GL (Fin 5) F :=
  (blockGL F 3 2).comp (GeneralLinearGroup.scalar (Fin 3))

theorem coe_kaL5B3TorHom (u : Fˣ) :
    ((kaL5B3TorHom F u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      diagBlock (Matrix.scalar (Fin 3) (u : F)) (1 : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem kaL5B3_scalar_eq (m : F) :
    (Matrix.scalar (Fin 5) m : Matrix (Fin 5) (Fin 5) F) =
      diagBlock (Matrix.scalar (Fin 3) m) (Matrix.scalar (Fin 2) m) := by
  ext x y
  obtain ⟨a, rfl⟩ := kaL5B3E.surjective x
  obtain ⟨b, rfl⟩ := kaL5B3E.surjective y
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [show (Matrix.scalar (Fin 5) m : Matrix (Fin 5) (Fin 5) F) (kaL5B3E a) (kaL5B3E b) =
    if a = b then m else 0 from scalar_apply_finSumFinEquiv (k := 3) (m := 2) m a b]
  rcases a with i | i <;> rcases b with j | j
  · rw [fromBlocks_apply₁₁, scalar_apply, diagonal_apply]
    simp
  · rw [fromBlocks_apply₁₂]
    simp
  · rw [fromBlocks_apply₂₁]
    simp
  · rw [fromBlocks_apply₂₂, scalar_apply, diagonal_apply]
    simp

theorem kaL5B3_conj_tor (A : GL (Fin 5) F) (l m : F)
    (hA : (A : Matrix (Fin 5) (Fin 5) F) =
      diagBlock (Matrix.scalar (Fin 3) l) (Matrix.scalar (Fin 2) m)) :
    ∃ u : Fˣ, conjAut 5 F A = conjAut 5 F (kaL5B3TorHom F u) := by
  have hdet : IsUnit (A : Matrix (Fin 5) (Fin 5) F).det := Matrix.isUnits_det_units A
  rw [hA, kaL5B3_det_diagBlock, scalar_apply, scalar_apply, det_diagonal, det_diagonal,
    Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fin] at hdet
  have hl : l ≠ 0 := by
    rintro rfl
    simp at hdet
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hdet
  have hu : l * m⁻¹ ≠ 0 := mul_ne_zero hl (inv_ne_zero hm)
  have hzl : m * (l * m⁻¹) = l := by field_simp
  have hAeq : A = GeneralLinearGroup.scalar (Fin 5) (Units.mk0 m hm) *
      kaL5B3TorHom F (Units.mk0 (l * m⁻¹) hu) := by
    apply Units.ext
    rw [Units.val_mul, hA, GeneralLinearGroup.coe_scalar, coe_kaL5B3TorHom, Units.val_mk0,
      Units.val_mk0, kaL5B3_scalar_eq, diagBlock_mul, mul_one, ← map_mul, hzl]
  refine ⟨Units.mk0 (l * m⁻¹) hu, ?_⟩
  rw [hAeq, map_mul, conjAut_scalar, one_mul]

theorem kaL5B3_eq_of_commute (M : Matrix (Fin 5) (Fin 5) F)
    (h1 : ∀ i j : Fin 3, i ≠ j →
      Commute (Matrix.single (kaL5B3E (Sum.inl i)) (kaL5B3E (Sum.inl j)) (1 : F)) M)
    (h2 : ∀ i j : Fin 2, i ≠ j →
      Commute (Matrix.single (kaL5B3E (Sum.inr i)) (kaL5B3E (Sum.inr j)) (1 : F)) M) :
    ∃ l m : F, M = diagBlock (Matrix.scalar (Fin 3) l) (Matrix.scalar (Fin 2) m) := by
  have hc1 : ∀ (j : Fin 3) (x : Fin 5), x ≠ kaL5B3E (Sum.inl j) →
      M x (kaL5B3E (Sum.inl j)) = 0 := by
    intro j x hx
    obtain ⟨j', hj'⟩ := exists_ne j
    exact Matrix.col_eq_zero_of_commute_single (h1 j j' hj'.symm) hx
  have hc2 : ∀ (j : Fin 2) (x : Fin 5), x ≠ kaL5B3E (Sum.inr j) →
      M x (kaL5B3E (Sum.inr j)) = 0 := by
    intro j x hx
    obtain ⟨j', hj'⟩ := exists_ne j
    exact Matrix.col_eq_zero_of_commute_single (h2 j j' hj'.symm) hx
  have hd1 : ∀ i : Fin 3, M (kaL5B3E (Sum.inl i)) (kaL5B3E (Sum.inl i)) =
      M (kaL5B3E (Sum.inl 0)) (kaL5B3E (Sum.inl 0)) := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · exact Matrix.diag_eq_of_commute_single (h1 i 0 hi)
  have hd2 : ∀ i : Fin 2, M (kaL5B3E (Sum.inr i)) (kaL5B3E (Sum.inr i)) =
      M (kaL5B3E (Sum.inr 0)) (kaL5B3E (Sum.inr 0)) := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · exact Matrix.diag_eq_of_commute_single (h2 i 0 hi)
  refine ⟨M (kaL5B3E (Sum.inl 0)) (kaL5B3E (Sum.inl 0)),
    M (kaL5B3E (Sum.inr 0)) (kaL5B3E (Sum.inr 0)), ?_⟩
  ext x y
  obtain ⟨a, rfl⟩ := kaL5B3E.surjective x
  obtain ⟨b, rfl⟩ := kaL5B3E.surjective y
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with i | i <;> rcases b with j | j
  · rw [fromBlocks_apply₁₁, scalar_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simpa using hd1 i
    · simpa [hij] using hc1 j _ (fun h => hij (Sum.inl.inj (kaL5B3E.injective h)))
  · rw [fromBlocks_apply₁₂]
    exact hc2 j _ (fun h => Sum.inl_ne_inr (kaL5B3E.injective h))
  · rw [fromBlocks_apply₂₁]
    exact hc1 j _ (fun h => Sum.inr_ne_inl (kaL5B3E.injective h))
  · rw [fromBlocks_apply₂₂, scalar_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simpa using hd2 i
    · simpa [hij] using hc2 j _ (fun h => hij (Sum.inr.inj (kaL5B3E.injective h)))

end Torus

section Hfix

variable {F : Type} [Field F]

theorem kaL5B3_hfix [Finite F] :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P' : Subgroup (MulAut (projectiveSL 5 F)), IsPGroup p ↥P' →
      (∀ e ∈ P', ∀ r ∈ kaL5B3L F, e r = r) → IsCyclic ↥P' := by
  intro p hp hp2 P' hP' hfixP
  let T : Fˣ →* MulAut (projectiveSL 5 F) := (conjAut 5 F).comp (kaL5B3TorHom F)
  have hle : P' ≤ T.range := by
    intro e he
    have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hp hp2 hP' he
    let N : Matrix (Fin 5) (Fin 5) F :=
      Matrix.single (kaL5B3E (Sum.inl 0)) (kaL5B3E (Sum.inl 1)) 1
    have hN0 : N ≠ 0 := by
      intro h0
      have := congrFun (congrFun h0 (kaL5B3E (Sum.inl 0))) (kaL5B3E (Sum.inl 1))
      simp [N] at this
    have hN2 : N * N = 0 :=
      Matrix.single_mul_single_of_ne (1 : F) (kaL5B3E (Sum.inl 0)) (kaL5B3E (Sum.inl 1))
        (kaL5B3E (Sum.inl 0)) (by decide) (1 : F)
    have hroot : ∀ c : F, ∃ g : SL(5, F), (g : Matrix (Fin 5) (Fin 5) F) = 1 + c • N ∧
        proj 5 F g ∈ kaL5B3L F := by
      intro c
      obtain ⟨g, hg, hgL⟩ := kaL5B3_root_inl (i := 0) (j := 1) (by decide) c
      refine ⟨g, ?_, hgL⟩
      rw [hg, Matrix.smul_single, smul_eq_mul, mul_one]
    obtain ⟨A, rfl⟩ := ka_fix_conjAut_proj (n := 5) (by norm_num) (kaL5B3L F) N hN0 hN2 hroot e
      hodd (hfixP e he)
    have h1 : ∀ i j : Fin 3, i ≠ j →
        Commute (Matrix.single (kaL5B3E (Sum.inl i)) (kaL5B3E (Sum.inl j)) (1 : F)) A.val := by
      intro i j hij
      obtain ⟨g, hg, hgL⟩ := kaL5B3_root_inl hij (1 : F)
      exact kaL5B3_commute_single A (fun h => hij (Sum.inl.inj (kaL5B3E.injective h))) g hg
        (hfixP _ he _ hgL)
    have h2 : ∀ i j : Fin 2, i ≠ j →
        Commute (Matrix.single (kaL5B3E (Sum.inr i)) (kaL5B3E (Sum.inr j)) (1 : F)) A.val := by
      intro i j hij
      obtain ⟨g, hg, hgL⟩ := kaL5B3_root_inr hij (1 : F)
      exact kaL5B3_commute_single A (fun h => hij (Sum.inr.inj (kaL5B3E.injective h))) g hg
        (hfixP _ he _ hgL)
    obtain ⟨l, m, hlm⟩ := kaL5B3_eq_of_commute A.val h1 h2
    obtain ⟨u, hu⟩ := kaL5B3_conj_tor A l m hlm
    exact ⟨u, hu.symm⟩
  have : IsCyclic ↥T.range := isCyclic_of_surjective T.rangeRestrict T.rangeRestrict_surjective
  exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end Hfix

section Main

variable {F : Type} [Field F]

theorem kaL5B3_main [Finite F] (hodd : ringChar F ≠ 2) (h5 : 5 ≤ Nat.card F) :
    KAAll (conjAut 5 F (kaL5B3GL F)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have h4 : 4 ≤ Nat.card F := by omega
  refine ka_all_of_torus_fix (ka_conj_inj_pl5 hodd) (kaL5B3R0 F) (kaL5B3L F) ?_ ?_
    kaL5B3_L_le_R0 (kaL5B3_normalizes_L h2) (kaL5B3_perf h4) (kaL5B3_hLp h4 h2) kaL5B3_hfix
    (ka_outCentral_pl5 hodd (kaL5B3GL F) (kaL5B3GL_mul_self F))
  · intro y hy
    exact mem_fixSub.2 (kaL5B3_map_le_fix hy)
  · intro c hc ho
    exact ka_odd_mem_map_cent_pl5 (kaL5B3GL F) (kaL5B3GL_mul_self F) (mem_fixSub.1 hc) ho

theorem kaL5B3_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

end Main

theorem kaL5B3_thm : KAL5B3 := by
  intro F _ _ hodd h5 B hB h3
  obtain ⟨P, rfl⟩ := kaL5B3_exists_frame hodd hB h3
  have h' := KAAll.of_mulEquiv (conjAut 5 F P : projectiveSL 5 F ≃* projectiveSL 5 F)
    (kaL5B3_main hodd h5)
  have key : MulAut.congr (conjAut 5 F P : projectiveSL 5 F ≃* projectiveSL 5 F)
      (conjAut 5 F (kaL5B3GL F)) = conjAut 5 F (P * kaL5B3GL F * P⁻¹) := by
    rw [kaL5B3_congr_eq_mul, map_mul, map_mul, map_inv]
  rwa [key] at h'

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
