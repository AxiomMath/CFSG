module

public import CFSG.LieType.AlgebraicGroups.RealizedTangentCurves

import CFSG.LieType.AlgebraicGroups.InnerInvolutionTorus
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import Mathlib.Algebra.Polynomial.Roots

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem end_mul_entry {τ : Tag} {L : Type} [Field L]
    (A B : Module.End L (RootModule τ L)) (a b : Label τ) :
    (A * B) (Finsupp.single b 1) a =
      ∑ c : Label τ, A (Finsupp.single c 1) a * B (Finsupp.single b 1) c := by
  rw [← endMatrix_apply (A * B), endMatrix_mul, Matrix.mul_apply]
  simp only [endMatrix_apply]

private theorem innerCo_glEntry {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (g : ModGL τ L) (a' b' : Label τ) :
    innerCo ((modGLPoint τ L).toMonoidHom g) (glEntry L (Label τ) a' b') =
      ∑ c : Label τ, ((g : Module.End L (RootModule τ L)) (Finsupp.single c 1) a') •
        ∑ d : Label τ,
          (((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))
            (Finsupp.single b' 1) d) • glEntry L (Label τ) c d := by
  rw [show ((modGLPoint τ L).toMonoidHom g) = (modGLPoint τ L g) from rfl]
  apply sub_eq_zero.1
  refine eq_zero_of_forall_algHom L (GLCoord L (Label τ)) _ fun y => ?_
  rw [map_sub, sub_eq_zero]
  let e : ModGL τ L := (modGLPoint τ L).symm (toConv y)
  have hy : (modGLPoint τ L e).ofConv = y := by
    rw [MulEquiv.apply_symm_apply, ofConv_toConv]
  have hyy : toConv y = modGLPoint τ L e := by
    rw [← hy, toConv_ofConv]
  rw [← hy]
  have hpt := point_comp_innerCo (toConv y) (modGLPoint τ L g)
  rw [hyy] at hpt
  rw [← tauCeti_inv_eq] at hpt
  have hleft : (modGLPoint τ L e).ofConv
      (innerCo (modGLPoint τ L g) (glEntry L (Label τ) a' b')) =
      (modGLPoint τ L g * modGLPoint τ L e * (modGLPoint τ L g)⁻¹).ofConv
        (glEntry L (Label τ) a' b') := by
    have h := congrArg (fun w : WithConv (GLCoord L (Label τ) →ₐ[L] L) =>
      w.ofConv (glEntry L (Label τ) a' b')) hpt
    simpa using h
  rw [hleft]
  have hginv : (modGLPoint τ L g)⁻¹ = modGLPoint τ L g⁻¹ :=
    (MulEquiv.map_inv (modGLPoint τ L) g).symm
  rw [hginv, mul_assoc, convMul_apply_glEntry]
  simp only [convMul_apply_glEntry, modGLPoint_apply_glEntry, map_sum, map_smul,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

private theorem conj_pinnedE_of_conj_pinnedX {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {g : ModGL τ L} {α β : Fin τ.rank → ℤ} {μ : L}
    (h : ∀ c : L, g * pinnedX τ L α c * g⁻¹ = pinnedX τ L β (μ * c)) :
    (g : Module.End L (RootModule τ L)) * pinnedE τ L α *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) =
      μ • pinnedE τ L β := by
  let D : ℕ → Module.End L (RootModule τ L) := fun j =>
    (g : Module.End L (RootModule τ L)) * pinnedCoeff τ L α j *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) -
      μ ^ j • pinnedCoeff τ L β j
  have hc : ∀ c : L, (g : Module.End L (RootModule τ L)) *
      (∑ j ∈ Finset.range 4, c ^ j • pinnedCoeff τ L α j) *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) =
      ∑ j ∈ Finset.range 4, (μ * c) ^ j • pinnedCoeff τ L β j := by
    intro c
    have h' := congrArg (fun u : ModGL τ L => (u : Module.End L (RootModule τ L))) (h c)
    simpa only [Units.val_mul, pinnedX_eq_sum] using h'
  have hD : ∀ c : L, (∑ j ∈ Finset.range 4, c ^ j • D j) =
      (g : Module.End L (RootModule τ L)) *
        (∑ j ∈ Finset.range 4, c ^ j • pinnedCoeff τ L α j) *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) -
      ∑ j ∈ Finset.range 4, (μ * c) ^ j • pinnedCoeff τ L β j := by
    intro c
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [D, smul_sub, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_pow, mul_comm (c ^ j) (μ ^ j)]
  have hsum : ∀ c : L, ∑ j ∈ Finset.range 4, c ^ j • D j = 0 := by
    intro c
    rw [hD c, hc c, sub_self]
  have hcoeff : ∀ a' b' : Label τ, D 1 (Finsupp.single b' 1) a' = 0 := by
    intro a' b'
    have hentry : ∀ c : L, ∑ j ∈ Finset.range 4,
        c ^ j * (D j (Finsupp.single b' 1) a') = 0 := by
      intro c
      have h' := congrArg (fun (A : Module.End L (RootModule τ L)) =>
        A (Finsupp.single b' 1) a') (hsum c)
      simpa [Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h'
    let p : Polynomial L := ∑ j ∈ Finset.range 4,
      Polynomial.C (D j (Finsupp.single b' 1) a') * Polynomial.X ^ j
    have hp : p = 0 := by
      apply Polynomial.funext (q := 0)
      intro c
      rw [Polynomial.eval_zero]
      calc
        p.eval c = ∑ j ∈ Finset.range 4,
            D j (Finsupp.single b' 1) a' * c ^ j := by
          simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        _ = ∑ j ∈ Finset.range 4,
            c ^ j * D j (Finsupp.single b' 1) a' := by
          refine Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := hentry c
    have hp1 := congrArg (fun q : Polynomial L => q.coeff 1) hp
    simp only [Polynomial.coeff_zero] at hp1
    have hpc : p.coeff 1 = D 1 (Finsupp.single b' 1) a' := by
      simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro j _ hne
        rw [if_neg (fun h => hne h.symm)]
      · intro h
        exact absurd (Finset.mem_range.2 (by norm_num)) h
    rw [← hpc]
    exact hp1
  have hD1 : D 1 = 0 := by
    refine (Finsupp.basisSingleOne (R := L)).ext (f₁ := D 1) (f₂ := 0) ?_
    intro b
    refine Finsupp.ext fun a => ?_
    simpa using hcoeff a b
  have hD1' : (g : Module.End L (RootModule τ L)) * pinnedCoeff τ L α 1 *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) -
      μ ^ 1 • pinnedCoeff τ L β 1 = 0 := by
    simpa [D] using hD1
  have h' := sub_eq_zero.1 hD1'
  simpa [pinnedCoeff_one] using h'


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem adTangent_rootTangent_of_conj_pinnedX {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    {α β : Fin τ.rank → ℤ} {μ : L}
    (h : ∀ c : L, g * pinnedX τ L α c * g⁻¹ = pinnedX τ L β (μ * c)) :
    adTangent (adjointPointSubgroup τ L)
        (Subgroup.mem_map_of_mem (modGLPoint τ L).toMonoidHom hg) (rootTangent τ L α) =
      μ • rootTangent τ L β := by
  have hE := conj_pinnedE_of_conj_pinnedX (L := L) (g := g) h
  refine tangentEntries_injective (L := L) (Bialgebra.counitAlgHom L (realizedCoord τ L)) ?_
  ext a' b'
  rw [tangentEntries_apply, tangentEntries_apply]
  unfold adTangent
  rw [coe_tangentMap, LinearMap.comp_apply]
  have hq : ∀ (h' : ∀ y ∈ subgroupPoints (adjointPointSubgroup τ L),
      y.comp (innerCo ((modGLPoint τ L).toMonoidHom g)) ∈
        subgroupPoints (adjointPointSubgroup τ L)),
      (quotientCo (adjointPointSubgroup τ L)
        (innerCo ((modGLPoint τ L).toMonoidHom g)) h')
        (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
          (glEntry L (Label τ) a' b')) =
      Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
        (innerCo ((modGLPoint τ L).toMonoidHom g) (glEntry L (Label τ) a' b')) :=
    fun h' => rfl
  rw [AlgHom.toLinearMap_apply, hq, innerCo_glEntry]
  rw [← Ideal.Quotient.mkₐ_eq_mk (R₁ := L)]
  simp only [map_sum, map_smul, smul_eq_mul, Submodule.coe_smul, LinearMap.smul_apply]
  simp only [Ideal.Quotient.mkₐ_eq_mk, rootTangent_mk]
  have hEentry : ((g : Module.End L (RootModule τ L)) *
      (pinnedE τ L α * ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))))
      (Finsupp.single b' 1) a' = μ * pinnedE τ L β (Finsupp.single b' 1) a' := by
    have h' := congrArg (fun (A : Module.End L (RootModule τ L)) =>
      A (Finsupp.single b' 1) a') hE
    simpa [mul_assoc, LinearMap.smul_apply, smul_eq_mul] using h'
  rw [← hEentry]
  rw [end_mul_entry g (pinnedE τ L α * ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)))
    a' b']
  simp only [end_mul_entry]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

end CFSG.LieType.AlgebraicGroups
