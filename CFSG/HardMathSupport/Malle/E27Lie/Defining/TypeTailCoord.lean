module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeC
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin

variable {r : ℕ} {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A]
  {qA : QuadraticForm F A}

@[expose] noncomputable def tailCoord (hr : 1 ≤ r)
    (g : ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A)) : (Fin (r - 1) → F) × A :=
  (fun i => (g (hypVec F A (.inl ⟨i + 1, by omega⟩))).1 (.inl ⟨i, by omega⟩),
    (g (hypVec F A (.inr ⟨r - 1, by omega⟩))).2)

theorem tailCoord_dMap_uMap (hr : 1 ≤ r) (D : GL (Fin r) F) (L : Fin r → A)
    (C : Matrix (Fin r) (Fin r) F) :
    tailCoord hr (dMap D 1 * uMap qA L C) =
      (fun i : Fin (r - 1) => (D : Matrix (Fin r) (Fin r) F) ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        L ⟨r - 1, by omega⟩) := by
  refine Prod.ext (funext fun i => ?_) ?_
  · change (dMap D 1 (uMap qA L C (hypVec F A (.inl ⟨i + 1, by omega⟩)))).1
      (.inl ⟨i, by omega⟩) = _
    rw [uMap_apply_of_fst_inr L C (fun k => by simp [hypVec]) rfl, dMap_apply]
    have hx : (hypVec F A (.inl ⟨i + 1, by omega⟩) : (Fin r ⊕ Fin r → F) × A).1 ∘ Sum.inl =
        Pi.single ⟨i + 1, by omega⟩ 1 := by
      funext k
      simp [hypVec, Pi.single_apply]
    change ((D : Matrix (Fin r) (Fin r) F) *ᵥ _) ⟨i, by omega⟩ = _
    rw [hx, mulVec_single_one, col_apply]
  · change (dMap D 1 (uMap qA L C (hypVec F A (.inr ⟨r - 1, by omega⟩)))).2 = _
    rw [dMap_apply, uMap_apply, uLin_apply_snd]
    simp [hypVec, Pi.single_apply]

theorem conjL_apply_last (hr : 1 ≤ r) {D' : GL (Fin r) F}
    (hD' : SymplecticFlag.IsUnitriangular (D' : Matrix (Fin r) (Fin r) F)) (L : Fin r → A) :
    conjL D'⁻¹ (1 : A ≃ₗ[F] A)⁻¹ L ⟨r - 1, by omega⟩ = L ⟨r - 1, by omega⟩ := by
  have hinv :
      SymplecticFlag.IsUnitriangular (((D'⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) := by
    rw [Matrix.coe_units_inv]
    exact hD'.inv
  simp only [conjL, inv_one, LinearEquiv.coe_one, id_eq]
  rw [Finset.sum_eq_single ⟨r - 1, by omega⟩]
  · rw [hinv.2, one_smul]
  · intro i _ hi
    rw [unitri_apply_last hinv hr]
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable [FiniteDimensional F A] (hani : qA.Anisotropic)
include hani

@[expose] noncomputable def tailUnipCoord (hr : 1 ≤ r) :
    (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) →*
      Multiplicative ((Fin (r - 1) → F) × A) where
  toFun x := Multiplicative.ofAdd (tailCoord hr ((x : orthElementaryGroup (quadTail r qA)) :
    ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A)))
  map_one' := by
    show Multiplicative.ofAdd (tailCoord hr
      (1 : ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A))) = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_one]
    refine Prod.ext (funext fun i => ?_) ?_
    · simp [tailCoord, hypVec, Fin.ext_iff]
    · simp [tailCoord, hypVec]
  map_mul' x y := by
    obtain ⟨D, L, C, hD, h1, -, -, hx⟩ := (mem_tailUnipotent_iff hani).mp
      (Subgroup.mem_subgroupOf.mp x.2)
    obtain ⟨D', L', C', hD', h1', -, -, hy⟩ := (mem_tailUnipotent_iff hani).mp
      (Subgroup.mem_subgroupOf.mp y.2)
    have hDu : SymplecticFlag.IsUnitriangular (D : Matrix (Fin r) (Fin r) F) := ⟨hD, h1⟩
    have hD'u : SymplecticFlag.IsUnitriangular (D' : Matrix (Fin r) (Fin r) F) := ⟨hD', h1'⟩
    have hxy : (((x * y : (tailUnipotent r qA).subgroupOf _) :
        orthElementaryGroup (quadTail r qA)) :
        ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A)) =
        dMap (D * D') (1 * 1) * uMap qA (conjL D'⁻¹ (1 : A ≃ₗ[F] A)⁻¹ L + L')
          (mulParam qA (conjL D'⁻¹ (1 : A ≃ₗ[F] A)⁻¹ L) L'
            (conjC qA D'⁻¹ (1 : A ≃ₗ[F] A)⁻¹ L C) C') := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy]
      exact dMap_uMap_mul_dMap_uMap D D' 1 (one_mem _) L L' C C'
    rw [← ofAdd_add]
    congr 1
    rw [hxy, mul_one, tailCoord_dMap_uMap, hx, hy, tailCoord_dMap_uMap, tailCoord_dMap_uMap]
    refine Prod.ext (funext fun i => ?_) ?_
    · simp only [Prod.fst_add, Pi.add_apply, Units.val_mul]
      exact unitri_mul_apply_succ hDu hD'u i
    · simp only [Prod.snd_add, Pi.add_apply]
      rw [conjL_apply_last hr hD'u]

theorem tailUnipCoord_surjective (hr : 1 ≤ r) :
    Function.Surjective (tailUnipCoord (qA := qA) hani hr) := by
  intro x
  obtain ⟨M₀, hM₀⟩ := superdiag_surjective (n := r) (K := F) (Multiplicative.toAdd x).1
  have hA : SymplecticFlag.IsUnitriangular (1 + (M₀ : Matrix (Fin r) (Fin r) F)) := by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · have hba' : b < a := hba
      rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hba'), M₀.2 a b hba'.le, add_zero]
    · rw [Matrix.add_apply, Matrix.one_apply_eq, M₀.2 a a le_rfl, add_zero]
  let D : GL (Fin r) F := Matrix.nonsingInvUnit _ hA.isUnit_det
  let L : Fin r → A := Pi.single ⟨r - 1, by omega⟩ (Multiplicative.toAdd x).2
  have hmem := dMap_mul_uMap_mem_tailUnipotent (qA := qA) (D := D) hA.1 hA.2 L
    (C := 0) (by simp) (fun _ => rfl)
  refine ⟨⟨⟨_, tailUnipotent_le hmem⟩, Subgroup.mem_subgroupOf.mpr hmem⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  show tailCoord hr (dMap D 1 * uMap qA L 0) = Multiplicative.toAdd x
  rw [tailCoord_dMap_uMap]
  refine Prod.ext (funext fun i => ?_) ?_
  · have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, by omega⟩ := by simp [Fin.ext_iff]
    show (1 + (M₀ : Matrix (Fin r) (Fin r) F)) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ = _
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, ← hM₀, superdiag_apply]
  · simp [L]

end CFSG.HardMathSupport.Malle.E27Lie
