module

public import CFSG.LieType.AlgebraicGroups.MatrixComponentQuotient
public import CFSG.LieType.AlgebraicGroups.ClosedSubgroupInnerCoordinate

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Subgroup WithConv
open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem threeConjugateNorm_mem_closedIdentityComponent
    (M Z : Subgroup (ModGL τ k))
    (hM : IsConnectedAlgebraicSubgroup k (M.map (modGLPoint τ k).toMonoidHom))
    (n : ModGL τ k)
    (hZ : ∀ s ∈ M, s * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) ∈ Z)
    {s : ModGL τ k} (hs : s ∈ M) :
    s * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) ∈ closedIdentityComponent Z := by
  let D := MatrixComponents.coordinateHopf M
  let : IsDomain D := hM.isDomain
  have hMc : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))) := by
    simpa only [subgroupPoints_map] using hM.isPointClosed
  let ε := MatrixComponents.coordinatePointsMulEquiv M hMc
  let q : GLCoord k (Label τ) →ₐ[k] D :=
    Ideal.Quotient.mkₐ k (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom))
  let t : (D →ₐ[k] k) → ModGL τ k := fun z => ε (toConv z)
  let a := modGLPoint τ k n
  let f : WithConv (GLCoord k (Label τ) →ₐ[k] D) :=
    toConv q * toConv (q.comp (innerCo a)) * toConv (q.comp (innerCo (a ^ 2)))
  let c : (D →ₐ[k] k) → ModGL τ k := fun z =>
    t z * (n * t z * n⁻¹) * (n ^ 2 * t z * (n ^ 2)⁻¹)
  have ht (z : D →ₐ[k] k) : modGLPoint τ k (t z) = toConv (z.comp q) := by
    rw [show t z = (ε (toConv z) : ModGL τ k) from rfl,
      MatrixComponents.coordinatePointsMulEquiv_coe, MulEquiv.apply_symm_apply]
  have heval (z : D →ₐ[k] k) :
      toConv (z.comp f.ofConv) = modGLPoint τ k (c z) := by
    have hprod : toConv (z.comp f.ofConv) =
        toConv (z.comp q) * toConv (z.comp (q.comp (innerCo a))) *
          toConv (z.comp (q.comp (innerCo (a ^ 2)))) := by
      simp only [f, AlgHom.comp_convMul_distrib, toConv_ofConv]
    have hq1 : toConv (z.comp (q.comp (innerCo a))) =
        a * modGLPoint τ k (t z) * a⁻¹ := by
      rw [← AlgHom.comp_assoc, point_comp_innerCo, ← ht]
    have hq2 : toConv (z.comp (q.comp (innerCo (a ^ 2)))) =
        a ^ 2 * modGLPoint τ k (t z) * (a ^ 2)⁻¹ := by
      rw [← AlgHom.comp_assoc, point_comp_innerCo, ← ht]
    rw [hprod, ← ht z, hq1, hq2]
    simp only [c, a, map_mul, map_inv, map_pow]
  have hentries : ∀ z a b, endMatrix τ (c z : Module.End k (RootModule τ k)) a b =
      z (f.ofConv (glEntry k (Label τ) a b)) := by
    intro z a b
    have h := congrArg (fun p : WithConv (GLCoord k (Label τ) →ₐ[k] k) =>
      p.ofConv (glEntry k (Label τ) a b)) (heval z)
    rw [modGLPoint_apply_glEntry] at h
    exact (by simpa only [AlgHom.comp_apply, ofConv_toConv, endMatrix_apply] using h.symm)
  let z₀ : D →ₐ[k] k := (ε.symm 1).ofConv
  have ht0 : t z₀ = 1 := by
    change (ε (toConv (ε.symm 1).ofConv) : ModGL τ k) = 1
    rw [toConv_ofConv, MulEquiv.apply_symm_apply]
    rfl
  have hz₀ : c z₀ = 1 := by simp only [c, ht0, mul_one, mul_inv_cancel]
  let z : D →ₐ[k] k := (ε.symm ⟨s,hs⟩).ofConv
  have hts : t z = s := by
    change (ε (toConv (ε.symm ⟨s,hs⟩).ofConv) : ModGL τ k) = s
    rw [toConv_ofConv, MulEquiv.apply_symm_apply]
  have hm := mem_closedIdentityComponent_of_matrix
    (Z := Z) (fun a b => f.ofConv (glEntry k (Label τ) a b))
    hentries (fun z => hZ (t z) (ε (toConv z)).property) hz₀ z
  simpa only [c, hts] using hm

end CFSG.LieType.AlgebraicGroups
