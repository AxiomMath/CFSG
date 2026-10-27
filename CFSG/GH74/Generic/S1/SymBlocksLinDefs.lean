module

public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.GH74.Generic.S1.FrameDefs

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def IsBlockAt (a b : Fin 4) (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ i j : Fin 4, ¬ ((i = a ∨ i = b) ∧ (j = a ∨ j = b)) →
    M i j = (1 : Matrix (Fin 4) (Fin 4) F) i j

theorem IsBlockAt.one (a b : Fin 4) : IsBlockAt a b (1 : Matrix (Fin 4) (Fin 4) F) :=
  fun _ _ _ => rfl

theorem IsBlockAt.mul {a b : Fin 4} {M N : Matrix (Fin 4) (Fin 4) F} (hM : IsBlockAt a b M)
    (hN : IsBlockAt a b N) : IsBlockAt a b (M * N) := by
  intro i j hij
  by_cases hi : i = a ∨ i = b
  · have hj : ¬ (j = a ∨ j = b) := fun hj => hij ⟨hi, hj⟩
    have hk : ∀ k, N k j = (1 : Matrix (Fin 4) (Fin 4) F) k j := fun k => hN k j (fun h => hj h.2)
    rw [Matrix.mul_apply]
    simp only [hk]
    rw [← Matrix.mul_apply, Matrix.mul_one]
    exact hM i j hij
  · have hk : ∀ k, M i k = (1 : Matrix (Fin 4) (Fin 4) F) i k := fun k => hM i k (fun h => hi h.1)
    rw [Matrix.mul_apply]
    simp only [hk]
    rw [← Matrix.mul_apply, Matrix.one_mul]
    exact hN i j hij

theorem IsBlockAt.of_mul_eq_one {a b : Fin 4} {M N : Matrix (Fin 4) (Fin 4) F}
    (hM : IsBlockAt a b M) (h1 : M * N = 1) (h2 : N * M = 1) : IsBlockAt a b N := by
  intro i j hij
  by_cases hi : i = a ∨ i = b
  · have hj : ¬ (j = a ∨ j = b) := fun hj => hij ⟨hi, hj⟩
    have hk : ∀ k, M k j = (1 : Matrix (Fin 4) (Fin 4) F) k j := fun k => hM k j (fun h => hj h.2)
    have h3 : (N * M) i j = N i j := by
      rw [Matrix.mul_apply]
      simp only [hk]
      rw [← Matrix.mul_apply, Matrix.mul_one]
    rw [← h3, h2]
  · have hk : ∀ k, M i k = (1 : Matrix (Fin 4) (Fin 4) F) i k := fun k => hM i k (fun h => hi h.1)
    have h3 : (M * N) i j = N i j := by
      rw [Matrix.mul_apply]
      simp only [hk]
      rw [← Matrix.mul_apply, Matrix.one_mul]
    rw [← h3, h1]

@[expose] def blkLin (a b : Fin 4) : Subgroup ↥(StatedSL 4 F) where
  carrier := {g | IsBlockAt a b ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)}
  one_mem' := IsBlockAt.one a b
  mul_mem' := fun {g h} hg hh => by
    have := IsBlockAt.mul hg hh
    simpa using this
  inv_mem' := fun {g} hg => by
    refine IsBlockAt.of_mul_eq_one hg ?_ ?_
    · exact g.1.val_inv
    · exact g.1.inv_val

theorem mem_blkLin {a b : Fin 4} {g : ↥(StatedSL 4 F)} :
    g ∈ blkLin a b ↔ IsBlockAt a b ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := Iff.rfl

theorem blkLin_symm (a b : Fin 4) : blkLin (F := F) a b = blkLin b a := by
  ext g
  rw [mem_blkLin, mem_blkLin]
  constructor <;> intro h i j hij <;> apply h i j <;> intro h' <;> apply hij <;>
    exact ⟨h'.1.symm, h'.2.symm⟩


@[expose] noncomputable def permGL (σ : Equiv.Perm (Fin 4)) : GL (Fin 4) F ≃* GL (Fin 4) F :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F F σ).toRingEquiv.toMulEquiv

theorem permGL_apply (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) F) (i j : Fin 4) :
    ((permGL σ g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i j =
      (g : Matrix (Fin 4) (Fin 4) F) (σ.symm i) (σ.symm j) := rfl

theorem det_permGL (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) F) :
    ((permGL σ g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (g : Matrix (Fin 4) (Fin 4) F).det :=
  Matrix.det_submatrix_equiv_self σ.symm (g : Matrix (Fin 4) (Fin 4) F)

theorem permGL_mem (σ : Equiv.Perm (Fin 4)) {g : GL (Fin 4) F} (hg : g ∈ StatedSL 4 F) :
    permGL σ g ∈ StatedSL 4 F := by
  rw [statedSL_eq_detOne, mem_detOne] at hg ⊢
  rw [det_permGL, hg]

@[expose] noncomputable def permS (σ : Equiv.Perm (Fin 4)) : ↥(StatedSL 4 F) ≃* ↥(StatedSL 4 F) where
  toFun g := ⟨permGL σ (g : GL (Fin 4) F), permGL_mem σ g.2⟩
  invFun g := ⟨permGL σ⁻¹ (g : GL (Fin 4) F), permGL_mem σ⁻¹ g.2⟩
  left_inv g := Subtype.ext (Units.ext (by
    ext i j
    simp only [permGL_apply, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]))
  right_inv g := Subtype.ext (Units.ext (by
    ext i j
    simp only [permGL_apply, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.apply_symm_apply]))
  map_mul' g h := Subtype.ext (map_mul (permGL σ) _ _)

theorem coe_permS (σ : Equiv.Perm (Fin 4)) (g : ↥(StatedSL 4 F)) :
    ((permS σ g : ↥(StatedSL 4 F)) : GL (Fin 4) F) = permGL σ (g : GL (Fin 4) F) := rfl

theorem permGL_inv_permGL (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) F) :
    permGL σ⁻¹ (permGL σ g) = g := by
  apply Units.ext
  ext i j
  simp only [permGL_apply, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem isBlockAt_permGL_iff (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) (g : GL (Fin 4) F) :
    IsBlockAt (σ a) (σ b) ((permGL σ g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ↔
      IsBlockAt a b (g : Matrix (Fin 4) (Fin 4) F) := by
  have key : ∀ (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) (g : GL (Fin 4) F),
      IsBlockAt a b (g : Matrix (Fin 4) (Fin 4) F) →
        IsBlockAt (σ a) (σ b) ((permGL σ g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro σ a b g hg i j hij
    rw [permGL_apply]
    have h1 : ¬ ((σ.symm i = a ∨ σ.symm i = b) ∧ (σ.symm j = a ∨ σ.symm j = b)) := by
      intro h
      apply hij
      refine ⟨?_, ?_⟩
      · rcases h.1 with h' | h'
        · exact Or.inl (by rw [← h']; simp)
        · exact Or.inr (by rw [← h']; simp)
      · rcases h.2 with h' | h'
        · exact Or.inl (by rw [← h']; simp)
        · exact Or.inr (by rw [← h']; simp)
    rw [hg _ _ h1]
    simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  refine ⟨fun h => ?_, key σ a b g⟩
  have := key σ⁻¹ (σ a) (σ b) (permGL σ g) h
  rw [permGL_inv_permGL] at this
  simpa using this

theorem permS_mem_blkLin_iff (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) (g : ↥(StatedSL 4 F)) :
    permS σ g ∈ blkLin (σ a) (σ b) ↔ g ∈ blkLin a b :=
  isBlockAt_permGL_iff σ a b (g : GL (Fin 4) F)

theorem map_permS_blkLin (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) :
    (blkLin (F := F) a b).map (permS σ).toMonoidHom = blkLin (σ a) (σ b) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (permS_mem_blkLin_iff σ a b h).2 hh
  · intro hg
    refine ⟨(permS σ).symm g, ?_, by simp⟩
    show (permS σ).symm g ∈ blkLin a b
    rw [← permS_mem_blkLin_iff σ a b, MulEquiv.apply_symm_apply]
    exact hg

open CFSG.ClassicalInvolution.WeakCT in
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockIdx) in
theorem mem_pair_iff (i : Fin 3) (r : Fin 4) :
    (r = Fin.castSucc i ∨ r = Fin.succ i) ↔ ((i : ℕ) ≤ r.val ∧ r.val < (i : ℕ) + 2) := by
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan in
theorem blkLin_succ_eq (i : Fin 3) :
    blkLin (F := F) (Fin.castSucc i) (Fin.succ i) =
      ((blockSL2 F 3 i).range).map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom := by
  ext g
  constructor
  · intro hg
    have hik : (i : ℕ) + 2 ≤ 4 := by have := i.isLt; omega
    set M : Matrix (Fin 4) (Fin 4) F := ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hM
    let A : Matrix (Fin 2) (Fin 2) F := fun x y => M (blockIdx (i : ℕ) hik x) (blockIdx (i : ℕ) hik y)
    have hMA : M = blockMat 4 (i : ℕ) A := by
      ext r s
      rw [blockMat_apply]
      split_ifs with h
      · simp only [A, blockIdx]
        congr 2 <;> ext <;> simp <;> omega
      · exact hg r s (fun h' => h ⟨(mem_pair_iff i r).1 h'.1, (mem_pair_iff i s).1 h'.2⟩)
    have hdet : A.det = 1 := by
      rw [← det_blockMat hik A, ← hMA]
      have h1 : (g : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact g.2
      exact mem_detOne.1 h1
    refine Subgroup.mem_map.2 ⟨blockSL2 F 3 i ⟨A, hdet⟩, ⟨⟨A, hdet⟩, rfl⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    exact hMA.symm
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    intro r s hrs
    change blockMat 4 (i : ℕ) (A : Matrix (Fin 2) (Fin 2) F) r s = _
    rw [blockMat_apply]
    rw [dite_eq_right]
    intro h
    exact hrs ⟨(mem_pair_iff i r).2 h.1, (mem_pair_iff i s).2 h.2⟩

theorem IsBlockAt.commute {a b c d : Fin 4} {M N : Matrix (Fin 4) (Fin 4) F}
    (hdisj : ∀ k, (k = a ∨ k = b) → ¬ (k = c ∨ k = d))
    (hM : IsBlockAt a b M) (hN : IsBlockAt c d N) : M * N = N * M := by
  have hX : ∀ i k, (M - 1) i k ≠ 0 → (i = a ∨ i = b) ∧ (k = a ∨ k = b) := by
    intro i k h
    by_contra hcon
    apply h
    rw [Matrix.sub_apply, hM i k hcon, sub_self]
  have hY : ∀ i k, (N - 1) i k ≠ 0 → (i = c ∨ i = d) ∧ (k = c ∨ k = d) := by
    intro i k h
    by_contra hcon
    apply h
    rw [Matrix.sub_apply, hN i k hcon, sub_self]
  have hXY : (M - 1) * (N - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : (M - 1) i k = 0
    · rw [h1, zero_mul]
    · by_cases h2 : (N - 1) k j = 0
      · rw [h2, mul_zero]
      · exact absurd (hY k j h2).1 (hdisj k (hX i k h1).2)
  have hYX : (N - 1) * (M - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : (N - 1) i k = 0
    · rw [h1, zero_mul]
    · by_cases h2 : (M - 1) k j = 0
      · rw [h2, mul_zero]
      · exact absurd (hY i k h1).2 (hdisj k (hX k j h2).1)
  have e1 : M * N = M + N - 1 := by
    rw [← sub_eq_zero]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul] at hXY
    rw [← hXY]
    abel
  have e2 : N * M = M + N - 1 := by
    rw [← sub_eq_zero]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul] at hYX
    rw [← hYX]
    abel
  rw [e1, e2]


theorem IsBlockAt.comm_reflDiagMat {a b c : Fin 4} (hca : c ≠ a) (hcb : c ≠ b)
    {M : Matrix (Fin 4) (Fin 4) F} (hM : IsBlockAt a b M) :
    M * reflDiagMat F c = reflDiagMat F c * M := by
  ext i j
  simp only [reflDiagMat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij
    exact mul_comm _ _
  · by_cases hin : (i = a ∨ i = b) ∧ (j = a ∨ j = b)
    · have hi : i ≠ c := by
        rintro rfl
        rcases hin.1 with h | h
        · exact hca h
        · exact hcb h
      have hj : j ≠ c := by
        rintro rfl
        rcases hin.2 with h | h
        · exact hca h
        · exact hcb h
      simp [hi, hj]
    · rw [hM i j hin, Matrix.one_apply_ne hij, zero_mul, mul_zero]


end CFSG.GH74.Generic.S1
