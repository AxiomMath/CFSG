module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

section Torus

variable {F : Type} [Field F]

@[expose] def diagUnitSL2 (a : Fˣ) : SL(2, F) :=
  ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

@[expose] def diagUnitSL2Hom : Fˣ →* SL(2, F) where
  toFun := diagUnitSL2
  map_one' := by
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagUnitSL2]
  map_mul' a b := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagUnitSL2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagUnitSL2Hom_injective : Function.Injective (diagUnitSL2Hom (F := F)) := by
  intro a b h
  have := congrArg (fun A : SL(2, F) => A 0 0) h
  exact Units.ext (by simpa [diagUnitSL2Hom, diagUnitSL2] using this)

theorem exists_pair_torus_element (h2 : (2 : F) ≠ 0) {X : Type} [Group X] {W N L : Subgroup X}
    (h : LinearBlockStandardPair F W N L) {v : X} (hv : v ∈ N) (hv2 : orderOf v = 2) (ρ : Fˣ) :
    ∃ t ∈ L, t * v = v * t ∧ orderOf t = orderOf ρ := by
  obtain ⟨θ, -, hker, hN, hL⟩ := pair_normalize h
  rw [← hN] at hv
  have hvθ := eq_block_neg_one h2 hker (by omega : 0 + 2 ≤ 3) hv hv2
  refine ⟨θ (blockSL F 3 2 1 (by omega) (diagUnitSL2 ρ)), ?_, ?_, ?_⟩
  · rw [← hL]
    exact ⟨_, ⟨diagUnitSL2 ρ, rfl⟩, rfl⟩
  · rw [hvθ, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_blockSL_three_zero, coe_blockSL_three_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagUnitSL2, Matrix.mul_apply, Fin.sum_univ_three]
  · have hinj : Function.Injective
        ((θ.comp (blockSL F 3 2 1 (by omega : 1 + 2 ≤ 3))).comp (diagUnitSL2Hom (F := F))) :=
      (comp_blockSL_injective hker (by omega : 1 + 2 ≤ 3) (by omega : 2 < 3)).comp
        diagUnitSL2Hom_injective
    exact orderOf_injective _ hinj ρ

end Torus

end CFSG.ClassicalInvolution.RouteD.NonClassical
