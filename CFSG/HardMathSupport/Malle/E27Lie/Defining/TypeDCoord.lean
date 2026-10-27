module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeC
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotent

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

variable {r : ℕ} {F : Type} [Field F]

theorem unitri_mul_apply_penult {A : Matrix (Fin r) (Fin r) F}
    (hA : SymplecticFlag.IsUnitriangular A) (hr : 2 ≤ r) (C : Matrix (Fin r) (Fin r) F)
    (hC : C ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ = 0) :
    (A * C) ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ = C ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ := by
  have hne : (⟨r - 2, by omega⟩ : Fin r) ≠ ⟨r - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
  rw [Matrix.mul_apply, Fintype.sum_eq_add _ _ hne]
  · rw [hA.2, one_mul, hC, mul_zero, add_zero]
  · rintro c ⟨h1, h2⟩
    have hlt : c < ⟨r - 2, by omega⟩ := by
      rw [Fin.lt_def]
      have h3 := c.2
      have h4 : c.val ≠ r - 2 := fun h => h1 (Fin.ext h)
      have h5 : c.val ≠ r - 1 := fun h => h2 (Fin.ext h)
      show c.val < r - 2
      omega
    rw [hA.1 hlt, zero_mul]

theorem fromBlocks_eq_blockMat (A : GL (Fin r) F) (C : Matrix (Fin r) (Fin r) F) :
    fromBlocks (A : Matrix (Fin r) (Fin r) F) ((A : Matrix (Fin r) (Fin r) F) * C) 0
      ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)ᵀ =
      SymplecticFlag.blockMat (A : Matrix (Fin r) (Fin r) F) C := by
  rw [Matrix.coe_units_inv]
  rfl

@[expose] noncomputable def orthCoord (hr : 2 ≤ r)
    (g : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)) : (Fin (r - 1) → F) × F :=
  (fun i => LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → F) →ₗ[F] (Fin r ⊕ Fin r → F))
      (.inl ⟨i, by omega⟩) (.inl ⟨i + 1, by omega⟩),
    LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → F) →ₗ[F] (Fin r ⊕ Fin r → F))
      (.inl ⟨r - 2, by omega⟩) (.inr ⟨r - 1, by omega⟩))

theorem orthCoord_of_blockMat (hr : 2 ≤ r) {g : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)}
    {A C : Matrix (Fin r) (Fin r) F} (hA : SymplecticFlag.IsUnitriangular A)
    (hC : C ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ = 0)
    (hg : LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → F) →ₗ[F] (Fin r ⊕ Fin r → F)) =
      SymplecticFlag.blockMat A C) :
    orthCoord hr g = (fun i : Fin (r - 1) => A ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
      C ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩) := by
  simp only [orthCoord, hg, SymplecticFlag.blockMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂]
  rw [unitri_mul_apply_penult hA hr C hC]

@[expose] noncomputable def orthUnipCoord (hr : 2 ≤ r) :
    (posUnip r F).subgroupOf (orthElementaryGroup (quadPlus r F)) →*
      Multiplicative ((Fin (r - 1) → F) × F) where
  toFun x := Multiplicative.ofAdd (orthCoord hr ((x : orthElementaryGroup (quadPlus r F)) :
    (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)))
  map_one' := by
    show Multiplicative.ofAdd
      (orthCoord hr (1 : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F))) = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_one]
    have h1 : LinearMap.toMatrix' ((1 : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)) :
        (Fin r ⊕ Fin r → F) →ₗ[F] (Fin r ⊕ Fin r → F)) = 1 := by
      exact LinearMap.toMatrix'_id
    refine Prod.ext (funext fun i => ?_) ?_
    · simp only [orthCoord, h1, Prod.fst_zero, Pi.zero_apply]
      exact Matrix.one_apply_ne (by simp [Fin.ext_iff])
    · simp only [orthCoord, h1, Prod.snd_zero]
      exact Matrix.one_apply_ne (by simp)
  map_mul' x y := by
    obtain ⟨A, C, hA, h1, hC, hd, hx⟩ := mem_posUnip_iff.mp (Subgroup.mem_subgroupOf.mp x.2)
    obtain ⟨D, E, hD, h1D, hE, hdE, hy⟩ := mem_posUnip_iff.mp (Subgroup.mem_subgroupOf.mp y.2)
    rw [fromBlocks_eq_blockMat] at hx hy
    have hAu : SymplecticFlag.IsUnitriangular (A : Matrix (Fin r) (Fin r) F) := ⟨hA, h1⟩
    have hDu : SymplecticFlag.IsUnitriangular (D : Matrix (Fin r) (Fin r) F) := ⟨hD, h1D⟩
    have hxy : LinearMap.toMatrix' (((x * y : (posUnip r F).subgroupOf _) :
        orthElementaryGroup (quadPlus r F)) : (Fin r ⊕ Fin r → F) →ₗ[F] (Fin r ⊕ Fin r → F)) =
        SymplecticFlag.blockMat ((A : Matrix (Fin r) (Fin r) F) * (D : Matrix (Fin r) (Fin r) F))
          (E + (D : Matrix (Fin r) (Fin r) F)⁻¹ * C * (D : Matrix (Fin r) (Fin r) F)⁻¹ᵀ) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.coe_toLinearMap_mul,
        LinearMap.toMatrix'_mul, hx, hy, SymplecticFlag.blockMat_mul hDu.isUnit_det]
    have hCl : C ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ = 0 := hd _
    have hEl : E ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ = 0 := hdE _
    have hDinv := hDu.inv
    have hconj_last := unitri_conj_apply_last hDinv (by omega) C
    have hEC : (E + (D : Matrix (Fin r) (Fin r) F)⁻¹ * C * (D : Matrix (Fin r) (Fin r) F)⁻¹ᵀ)
        ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ = 0 := by
      rw [Matrix.add_apply, hEl, zero_add, hconj_last, hCl]
    rw [← ofAdd_add, orthCoord_of_blockMat hr (hAu.mul hDu) hEC hxy,
      orthCoord_of_blockMat hr hAu hCl hx, orthCoord_of_blockMat hr hDu hEl hy]
    congr 1
    refine Prod.ext (funext fun i => ?_) ?_
    · simp only [Prod.fst_add, Pi.add_apply]
      exact unitri_mul_apply_succ hAu hDu i
    · simp only [Prod.snd_add, Matrix.add_apply]
      have hpen : ((D : Matrix (Fin r) (Fin r) F)⁻¹ * C * (D : Matrix (Fin r) (Fin r) F)⁻¹ᵀ)
          ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ = C ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ := by
        have hcol : ∀ a, (C * (D : Matrix (Fin r) (Fin r) F)⁻¹ᵀ) a ⟨r - 1, by omega⟩ =
            C a ⟨r - 1, by omega⟩ := fun a => by
          rw [Matrix.mul_apply, Finset.sum_eq_single ⟨r - 1, by omega⟩]
          · rw [Matrix.transpose_apply, hDinv.2, mul_one]
          · intro b _ hb
            rw [Matrix.transpose_apply, unitri_apply_last hDinv (by omega)]
            simp [hb]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [Matrix.mul_assoc, unitri_mul_apply_penult hDinv hr _ (by rw [hcol, hCl]), hcol]
      rw [hpen]
      ring

theorem orthUnipCoord_surjective (hr : 2 ≤ r) :
    Function.Surjective (orthUnipCoord (F := F) hr) := by
  intro x
  obtain ⟨M₀, hM₀⟩ := superdiag_surjective (n := r) (K := F) (Multiplicative.toAdd x).1
  set c := (Multiplicative.toAdd x).2
  have hA : SymplecticFlag.IsUnitriangular (1 + (M₀ : Matrix (Fin r) (Fin r) F)) := by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · have hba' : b < a := hba
      rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hba'), M₀.2 a b hba'.le, add_zero]
    · rw [Matrix.add_apply, Matrix.one_apply_eq, M₀.2 a a le_rfl, add_zero]
  let i₀ : Fin r := ⟨r - 2, by omega⟩
  let i₁ : Fin r := ⟨r - 1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]; omega
  let C : Matrix (Fin r) (Fin r) F := Matrix.single i₀ i₁ c - Matrix.single i₁ i₀ c
  have hCt : Cᵀ = -C := by
    simp only [C, Matrix.transpose_sub, Matrix.transpose_single, neg_sub]
  have hCd : ∀ i, C i i = 0 := fun i => by
    simp only [C, Matrix.sub_apply, Matrix.single_apply]
    by_cases h0 : i₀ = i <;> by_cases h1 : i₁ = i
    · exact absurd (h0.trans h1.symm) h01
    all_goals simp [h0, h1]
  let A' : GL (Fin r) F := Matrix.nonsingInvUnit _ hA.isUnit_det
  obtain ⟨g, hgU, hg⟩ := exists_posUnip_toMatrix' A' C hA.1 hA.2 hCt hCd
  refine ⟨⟨⟨g, posUnip_le_orthElementaryGroup hgU⟩, Subgroup.mem_subgroupOf.mpr hgU⟩, ?_⟩
  have hg' : LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → F) →ₗ[F] (Fin r ⊕ Fin r → F)) =
      SymplecticFlag.blockMat (1 + (M₀ : Matrix (Fin r) (Fin r) F)) C := by
    rw [hg, fromBlocks_eq_blockMat]
    rfl
  apply Multiplicative.toAdd.injective
  show orthCoord hr g = Multiplicative.toAdd x
  rw [orthCoord_of_blockMat hr hA (hCd i₁) hg']
  refine Prod.ext (funext fun i => ?_) ?_
  · have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, by omega⟩ := by simp [Fin.ext_iff]
    dsimp only
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, ← hM₀, superdiag_apply]
  · show C i₀ i₁ = c
    simp only [C, Matrix.sub_apply, Matrix.single_apply_same]
    rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => h01 h.2), sub_zero]

end CFSG.HardMathSupport.Malle.E27Lie
