module

public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.RankThree.PartOne.KA5L.Frames

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.PinnedBlocks

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.KF4
  CFSG.ClassicalInvolution.WeakCT CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem mul_eq_one_of_pinned_sl2_hom {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (ψ : SL2 K →* ModGL τ K) (a b : K) (ha : a ≠ 0)
    (hu : ∀ t, ψ (uSL t) = pinnedX τ K α (a * t))
    (hv : ∀ t, ψ (vSL t) = pinnedX τ K (-α) (b * t)) : a * b = 1 := by
  have hS : Function.Injective (rootSL2 τ K α) := by
    intro A B h
    rw [rootSL2_apply, rootSL2_apply] at h
    exact simpleRootSL2_injective_of_charTwo _ (by simpa using h)
  have h := congrArg ψ (braid_one (K := K))
  simp only [map_mul, hu, hv, mul_one, mul_neg_one] at h
  have h' : rootSL2 τ K α (uSL a * vSL (-b) * uSL a) =
      rootSL2 τ K α (vSL (-b) * uSL a * vSL (-b)) := by
    simp only [map_mul, rootSL2_uSL_of_charTwo hα, rootSL2_vSL_of_charTwo hα]
    exact h
  exact braid_unit ha (hS h')

theorem exists_pinned_blocks (ρ : SL(3, K) →* ModGL τ K)
    (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ) (hF : IsA2Frame ρ σ) :
    ∃ d : Fin 3 → Kˣ,
      (ρ.comp (conjDiag3Hom d)).comp (blockSL K 3 2 0 (by omega)) =
        rootSL2 τ K (σ 0 1) ∧
      (ρ.comp (conjDiag3Hom d)).comp (blockSL K 3 2 1 (by omega)) =
        rootSL2 τ K (σ 1 2) := by
  obtain ⟨e01, he01⟩ := hF.transv 0 1 (by decide)
  obtain ⟨e10, he10⟩ := hF.transv 1 0 (by decide)
  obtain ⟨e12, he12⟩ := hF.transv 1 2 (by decide)
  obtain ⟨e21, he21⟩ := hF.transv 2 1 (by decide)
  have hu1 : (e01 : K) * e10 = 1 := by
    refine mul_eq_one_of_pinned_sl2_hom (hF.isRoot 0 1 (by decide))
      (ρ.comp (blockSL K 3 2 0 (by omega))) e01 e10 e01.ne_zero
      (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk0_uSL, he01]
    · rw [MonoidHom.comp_apply, blk0_vSL, he10, hF.neg 0 1]
  have hu2 : (e12 : K) * e21 = 1 := by
    refine mul_eq_one_of_pinned_sl2_hom (hF.isRoot 1 2 (by decide))
      (ρ.comp (blockSL K 3 2 1 (by omega))) e12 e21 e12.ne_zero
      (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk1_uSL, he12]
    · rw [MonoidHom.comp_apply, blk1_vSL, he21, hF.neg 1 2]
  let d : Fin 3 → Kˣ := ![(e01 * e12)⁻¹, e12⁻¹, 1]
  let θ : SL(3, K) →* ModGL τ K := ρ.comp (conjDiag3Hom d)
  have hθ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : K),
      θ (Matrix.SpecialLinearGroup.transvection hij t) =
      ρ (Matrix.SpecialLinearGroup.transvection hij
        ((d i : K) * t * ((d j)⁻¹ : Kˣ))) := by
    intro i j hij t
    rw [MonoidHom.comp_apply, conjDiag3Hom_apply, conjDiag3_transvection]
  have eq_root (α : Fin τ.rank → ℤ) (hα : IsRoot τ α)
      (ψ : SL2 K →* ModGL τ K)
      (hu : ∀ t, ψ (uSL t) = pinnedX τ K α t)
      (hv : ∀ t, ψ (vSL t) = pinnedX τ K (-α) t) : ψ = rootSL2 τ K α := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change ψ (uSL c) = rootSL2 τ K α (uSL c)
      rw [hu, rootSL2_uSL_of_charTwo hα]
    · change ψ (vSL c) = rootSL2 τ K α (vSL c)
      rw [hv, rootSL2_vSL_of_charTwo hα]
  refine ⟨d, ?_, ?_⟩
  · refine eq_root (σ 0 1) (hF.isRoot 0 1 (by decide)) _ (fun t => ?_) (fun t => ?_)
    · change θ ((blockSL K 3 2 0 (by omega)) (uSL t)) = _
      rw [blk0_uSL, hθ, he01]
      congr 1
      simp [d]
      field_simp
    · change θ ((blockSL K 3 2 0 (by omega)) (vSL t)) = _
      rw [blk0_vSL, hθ, he10, hF.neg 0 1]
      congr 1
      simp [d]
      field_simp
      linear_combination hu1 * t
  · refine eq_root (σ 1 2) (hF.isRoot 1 2 (by decide)) _ (fun t => ?_) (fun t => ?_)
    · change θ ((blockSL K 3 2 1 (by omega)) (uSL t)) = _
      rw [blk1_uSL, hθ, he12]
      congr 1
      simp [d]
    · change θ ((blockSL K 3 2 1 (by omega)) (vSL t)) = _
      rw [blk1_vSL, hθ, he21, hF.neg 1 2]
      congr 1
      simp [d]
      linear_combination hu2 * t

end CFSG.LieType.Chevalley.E7Three.PinnedBlocks
