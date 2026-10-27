module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open Matrix CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

theorem fromBlocks_symplectic_of_lower_zero {A E D : Matrix (Fin r) (Fin r) K}
    (h : (fromBlocks A E 0 D)ᵀ * fromBlocks 0 1 (-1) 0 * fromBlocks A E 0 D =
      fromBlocks 0 1 (-1) 0) :
    Aᵀ * D = 1 ∧ Eᵀ * D = Dᵀ * E := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨-, h₂, -, h₄⟩ := h
  simp only [transpose_zero, Matrix.mul_zero, Matrix.mul_one, add_zero, Matrix.zero_mul,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero] at h₂ h₄
  exact ⟨h₂, by rw [neg_add_eq_zero] at h₄; exact h₄.symm⟩

theorem exists_blockMat_of_toBlocks₂₁_eq_zero {g : StatedSp r K}
    (h : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₂₁ = 0) :
    IsUnit ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁.det ∧
      ∃ C : Matrix (Fin r) (Fin r) K, Cᵀ = C ∧
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          blockMat ((g : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁ C := by
  set M := ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set A := M.toBlocks₁₁
  set E := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  have hMb : M = fromBlocks A E 0 D := by
    rw [← h]
    exact (fromBlocks_toBlocks M).symm
  have hsp := SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  rw [← hM, hMb] at hsp
  obtain ⟨h₁, h₂⟩ := fromBlocks_symplectic_of_lower_zero hsp
  have hAt : IsUnit Aᵀ.det := isUnit_det_of_right_inverse h₁
  have hA : IsUnit A.det := by rwa [det_transpose] at hAt
  have hD : D = A⁻¹ᵀ := by
    rw [transpose_nonsing_inv]
    exact (inv_eq_right_inv h₁).symm
  refine ⟨hA, A⁻¹ * E, ?_, ?_⟩
  · rw [transpose_mul, transpose_nonsing_inv, ← transpose_nonsing_inv, ← hD, h₂, hD,
      transpose_transpose]
  · rw [hMb, blockMat, mul_nonsing_inv_cancel_left A E hA, hD]

theorem single_mem_isoFlag (j : Fin r) :
    (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K) ∈ isoFlag r K (j + 1) :=
  Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩

theorem toBlocks_of_mem_borelSubgroup {g : StatedSp r K} (hg : g ∈ borelSubgroup r K) :
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₂₁ = 0 ∧
      ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁.IsUpperTriangular := by
  have key : ∀ j : Fin r, ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ Pi.single (Sum.inl j) 1 ∈
        isoFlag r K (j + 1) := by
    intro j
    have hs := (mem_borelSubgroup_iff_isoFlag.mp hg) (j + 1) (Nat.succ_pos _) j.2
    rw [mem_stabilizer] at hs
    rw [← hs]
    exact ⟨_, single_mem_isoFlag j, rfl⟩
  refine ⟨?_, fun k j hjk => ?_⟩
  · ext k j
    have := (mem_isoFlag.mp (key j)).1 k
    rwa [mulVec_single_one, col_apply] at this
  · have := (mem_isoFlag.mp (key j)).2 k (Nat.succ_le_of_lt hjk)
    rwa [mulVec_single_one, col_apply] at this

theorem mem_borelSubgroup_iff {g : StatedSp r K} :
    g ∈ borelSubgroup r K ↔ ∃ A C : Matrix (Fin r) (Fin r) K, A.IsUpperTriangular ∧ IsUnit A.det ∧
      Cᵀ = C ∧
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockMat A C := by
  constructor
  · intro hg
    obtain ⟨h₂₁, hA⟩ := toBlocks_of_mem_borelSubgroup hg
    obtain ⟨hdet, C, hC, hgC⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h₂₁
    exact ⟨_, C, hA, hdet, hC, hgC⟩
  · rintro ⟨A, C, hA, hdet, -, hg⟩
    exact mem_borelSubgroup_of_coe_eq_blockMat hA hdet hg

theorem blockMat_inj {A C A' C' : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    (h : blockMat A C = blockMat A' C') : A = A' ∧ C = C' := by
  rw [blockMat, blockMat, fromBlocks_inj] at h
  obtain ⟨h₁, h₂, -, -⟩ := h
  subst h₁
  refine ⟨rfl, ?_⟩
  rw [← nonsing_inv_mul_cancel_left A C hA, h₂, nonsing_inv_mul_cancel_left A C' hA]

@[expose] def diagEntry (g : StatedSp r K) (i : Fin r) : K :=
  ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i) (Sum.inl i)

theorem diagEntry_ne_zero {g : StatedSp r K} (hg : g ∈ borelSubgroup r K) (i : Fin r) :
    diagEntry g i ≠ 0 := by
  obtain ⟨A, C, hA, hdet, -, hgA⟩ := mem_borelSubgroup_iff.mp hg
  have h := mul_inv_apply_self_of_isUpperTriangular hA hdet i
  rw [diagEntry, hgA, blockMat, fromBlocks_apply₁₁]
  exact left_ne_zero_of_mul_eq_one h

theorem diagEntry_mul {g h : StatedSp r K} (hg : g ∈ borelSubgroup r K) (hh : h ∈ borelSubgroup r K)
    (i : Fin r) : diagEntry (g * h) i = diagEntry g i * diagEntry h i := by
  obtain ⟨A, C, hA, -, -, hgA⟩ := mem_borelSubgroup_iff.mp hg
  obtain ⟨D, E, hD, hdet, -, hhD⟩ := mem_borelSubgroup_iff.mp hh
  simp only [diagEntry, Subgroup.coe_mul, Units.val_mul, hgA, hhD, blockMat_mul hdet]
  simp only [blockMat, fromBlocks_apply₁₁]
  exact mul_apply_self_of_isUpperTriangular hA hD i

variable (r K) in
@[expose] def diagHom : borelSubgroup r K →* (Fin r → Kˣ) where
  toFun g i := Units.mk0 (diagEntry (g : StatedSp r K) i) (diagEntry_ne_zero g.2 i)
  map_one' := by
    funext i
    apply Units.ext
    simp [diagEntry]
  map_mul' g h := by
    funext i
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mk0, Pi.mul_apply, Units.val_mul]
    exact diagEntry_mul g.2 h.2 i

theorem coe_diagHom_apply (g : borelSubgroup r K) (i : Fin r) :
    ((diagHom r K g i : Kˣ) : K) = (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i) (Sum.inl i) :=
  rfl

theorem diagHom_surjective : Function.Surjective (diagHom r K) := by
  intro t
  refine ⟨⟨SymplecticTorusWeyl.torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩, ?_⟩
  funext i
  apply Units.ext
  simp [diagHom, diagEntry, SymplecticTorusWeyl.coe_torusHom]

theorem ker_diagHom : (diagHom r K).ker = (unipotent r K).subgroupOf (borelSubgroup r K) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨A, C, hA, hdet, hC, hgA⟩ := mem_borelSubgroup_iff.mp g.2
  have hdiag : ∀ i, ((diagHom r K g i : Kˣ) : K) = A i i := fun i => by
    rw [coe_diagHom_apply, hgA, blockMat, fromBlocks_apply₁₁]
  constructor
  · intro h1
    refine ⟨A, C, ⟨hA, fun i => ?_⟩, hC, hgA⟩
    rw [← hdiag, h1]
    rfl
  · rintro ⟨A', C', hA', -, hgA'⟩
    obtain ⟨rfl, -⟩ := blockMat_inj hdet (hgA.symm.trans hgA')
    funext i
    apply Units.ext
    rw [hdiag, hA'.2]
    rfl

theorem unipotent_subgroupOf_borelSubgroup_normal :
    ((unipotent r K).subgroupOf (borelSubgroup r K)).Normal := by
  rw [← ker_diagHom]
  exact MonoidHom.normal_ker _

variable (r) in
@[expose] def flagOrder : Fin r ⊕ Fin r ≃ Fin (2 * r) :=
  (Equiv.sumCongr (Equiv.refl (Fin r)) Fin.revPerm).trans
    (finSumFinEquiv.trans (finCongr (two_mul r).symm))

theorem flagOrder_inl (i : Fin r) : (flagOrder r (Sum.inl i) : ℕ) = i := by
  simp [flagOrder]

theorem flagOrder_inr (i : Fin r) : (flagOrder r (Sum.inr i) : ℕ) = r + (r - (i + 1)) := by
  simp [flagOrder, Fin.val_rev]
  omega

theorem blockMat_blockTriangular {A C : Matrix (Fin r) (Fin r) K} (hA : A.IsUpperTriangular)
    (hdet : IsUnit A.det) : (blockMat A C).BlockTriangular (flagOrder r) := by
  have hAi := isUpperTriangular_inv hA hdet
  rintro (a | a) (b | b) hlt
  · rw [Fin.lt_def, flagOrder_inl, flagOrder_inl] at hlt
    exact hA (Fin.lt_def.mpr hlt)
  · rw [Fin.lt_def, flagOrder_inl, flagOrder_inr] at hlt
    omega
  · rfl
  · rw [Fin.lt_def, flagOrder_inr, flagOrder_inr] at hlt
    have hab : a < b := Fin.lt_def.mpr (by omega)
    exact hAi hab

theorem exists_blockMat_of_blockTriangular {g : StatedSp r K}
    (h : ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).BlockTriangular (flagOrder r)) :
    ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁.IsUpperTriangular ∧
      IsUnit ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁.det ∧
      ∃ C : Matrix (Fin r) (Fin r) K, Cᵀ = C ∧
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          blockMat ((g : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁ C := by
  have h₂₁ : ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₂₁ = 0 := by
    ext a b
    refine h (Fin.lt_def.mpr ?_)
    rw [flagOrder_inl, flagOrder_inr]
    omega
  refine ⟨fun a b hab => h (Fin.lt_def.mpr ?_), exists_blockMat_of_toBlocks₂₁_eq_zero h₂₁⟩
  rw [flagOrder_inl, flagOrder_inl]
  exact Fin.lt_def.mp hab

theorem mem_borelSubgroup_iff_reindex {g : StatedSp r K} :
    g ∈ borelSubgroup r K ↔ (reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).IsUpperTriangular := by
  rw [IsUpperTriangular, blockTriangular_reindex_iff, Function.id_comp]
  constructor
  · intro hg
    obtain ⟨A, C, hA, hdet, -, hgA⟩ := mem_borelSubgroup_iff.mp hg
    rw [hgA]
    exact blockMat_blockTriangular hA hdet
  · intro h
    obtain ⟨hA, hdet, C, -, hgC⟩ := exists_blockMat_of_blockTriangular h
    exact mem_borelSubgroup_of_coe_eq_blockMat hA hdet hgC

theorem mem_unipotent_iff_reindex {g : StatedSp r K} :
    g ∈ unipotent r K ↔
      (reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).IsUpperTriangular ∧
      ∀ a, reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a a = 1 := by
  rw [← mem_borelSubgroup_iff_reindex]
  have hdiag : (∀ a, reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a a = 1) ↔
      ∀ x, ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) x x = 1 := by
    simp only [reindex_apply, submatrix_apply]
    exact ⟨fun h x => by simpa using h (flagOrder r x), fun h a => h _⟩
  rw [hdiag]
  constructor
  · rintro ⟨A, C, hA, hC, hgA⟩
    refine ⟨mem_borelSubgroup_of_coe_eq_blockMat hA.1 hA.isUnit_det hgA, ?_⟩
    rintro (a | a)
    · rw [hgA, blockMat, fromBlocks_apply₁₁, hA.2]
    · rw [hgA, blockMat, fromBlocks_apply₂₂, transpose_apply, hA.inv.2]
  · rintro ⟨hg, hd⟩
    have hg' := mem_borelSubgroup_iff_reindex.mp hg
    rw [IsUpperTriangular, blockTriangular_reindex_iff, Function.id_comp] at hg'
    obtain ⟨hA, hdet, C, hC, hgC⟩ := exists_blockMat_of_blockTriangular hg'
    exact ⟨_, C, ⟨hA, fun a => hd (Sum.inl a)⟩, hC, hgC⟩


theorem symplectic_higher_triangular_structure :
    (∀ g : StatedSp r K, g ∈ borelSubgroup r K ↔ ∃ A C : Matrix (Fin r) (Fin r) K,
      A.IsUpperTriangular ∧ IsUnit A.det ∧ Cᵀ = C ∧
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          blockMat A C) ∧
    (∀ A C A' C' : Matrix (Fin r) (Fin r) K, IsUnit A.det → blockMat A C = blockMat A' C' →
      A = A' ∧ C = C') ∧
    (∀ (g : borelSubgroup r K) (i : Fin r), ((diagHom r K g i : Kˣ) : K) =
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl i) (Sum.inl i)) ∧
    Function.Surjective (diagHom r K) ∧
    (diagHom r K).ker = (unipotent r K).subgroupOf (borelSubgroup r K) ∧
    ((unipotent r K).subgroupOf (borelSubgroup r K)).Normal ∧
    (∀ g : StatedSp r K, g ∈ borelSubgroup r K ↔
      (reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).IsUpperTriangular) ∧
    (∀ g : StatedSp r K, g ∈ unipotent r K ↔
      (reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).IsUpperTriangular ∧
      ∀ a, reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a a = 1) :=
  ⟨fun _ => mem_borelSubgroup_iff, fun _ _ _ _ hA h => blockMat_inj hA h, coe_diagHom_apply,
    diagHom_surjective, ker_diagHom, unipotent_subgroupOf_borelSubgroup_normal,
    fun _ => mem_borelSubgroup_iff_reindex, fun _ => mem_unipotent_iff_reindex⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
