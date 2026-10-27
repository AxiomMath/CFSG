module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixDim
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.RankThree.E6 (weylMatrix)


open scoped Classical in
theorem twE6FixDim_eq_of_monomial {K : Type} [Field K] {σ : K ≃+* K}
    {x : twistedE6RootGroup K σ} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ} {w : WeylGroup TwistTag.E6.tag}
    (hw3 : w ^ 3 = 1)
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0 = rootDiagUnit TwistTag.E6.tag a *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) :
    twE6FixDim K σ x =
      Module.finrank (AlgebraicClosure K) (LinearMap.ker
        (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → AlgebraicClosure K)) - 1)) +
      ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ = γ ∧
        ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
            rootVec TwistTag.E6.tag (AlgebraicClosure K) γ).card +
      ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ ≠ γ ∧
        (((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0) ^ 3 :
          ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
            rootVec TwistTag.E6.tag (AlgebraicClosure K) γ).card / 3 :=
  (finrank_ker_conj_baseChangeGL_sub_one g0 (x : ModGL TwistTag.E6.tag K)).symm.trans
    (finrank_ker_monomial_sub_one_of_eq rfl hw3 hx)

open scoped Classical in
theorem twE6FixDim_eq_of_monomial_of_pow_three {K : Type} [Field K] {σ : K ≃+* K}
    {x : twistedE6RootGroup K σ} (hx3 : x ^ 3 = 1)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ} {w : WeylGroup TwistTag.E6.tag}
    (hw3 : w ^ 3 = 1)
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0 = rootDiagUnit TwistTag.E6.tag a *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) :
    twE6FixDim K σ x =
      Module.finrank (AlgebraicClosure K) (LinearMap.ker
        (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → AlgebraicClosure K)) - 1)) +
      ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ = γ ∧
        ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
            rootVec TwistTag.E6.tag (AlgebraicClosure K) γ).card +
      ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ ≠ γ).card / 3 := by
  have hy3 : (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0) ^ 3 = 1 := by
    have h := conj_pow (a := g0⁻¹) (i := 3)
      (b := baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K))
    rw [inv_inv] at h
    rw [h, ← map_pow, ← Subgroup.coe_pow, hx3, Subgroup.coe_one, map_one, mul_one,
      inv_mul_cancel]
  rw [twE6FixDim_eq_of_monomial hw3 hx, hy3]
  simp only [Units.val_one, Module.End.one_apply, and_true]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
