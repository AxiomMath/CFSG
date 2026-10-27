module

public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerIdentity
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv

open scoped CFSG.ConvolutionPoints

section Frobenius

variable {τ : Tag} {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

theorem entrywiseFrobGL_rootDiagUnit (e : ℕ) {a : Fin τ.rank → kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) :
    entrywiseFrobGL τ k p e (rootDiagUnit τ a) = rootDiagUnit τ a := by
  apply Units.ext
  change entrywise (iterateFrobenius k p e) (rootDiag a) = rootDiag a
  rw [entrywise_rootDiag]
  congr 1
  funext i
  rcases ha i with h | h <;> rw [h] <;> ext <;> simp

theorem frobTwistGL_one_mem_toralCentralizer
    [IsAlgClosed k] (e : ℕ) {a : Fin τ.rank → kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {g : ModGL τ k} (hg : g ∈ toralCentralizer τ k a) :
    frobTwistGL τ k p e 1 g ∈ toralCentralizer τ k a := by
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  obtain ⟨hgG, hgc⟩ := mem_toralCentralizer.1 hg
  refine mem_toralCentralizer.2 ⟨entrywiseFrobGL_mem p e hgG, ?_⟩
  rw [← entrywiseFrobGL_rootDiagUnit p e ha, ← map_inv, ← map_mul, ← map_mul, hgc]

end Frobenius

theorem connected_exceptional_toral_centralizer_Lang
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (a : Fin τ.rank → kˣ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) :
    (IsConnectedAlgebraicSubgroup k (toralCentralizerPointSubgroup τ k a) ∧
      subgroupIdeal (adjointPointSubgroup τ k) ≤
        subgroupIdeal (toralCentralizerPointSubgroup τ k a) ∧
      Algebra.Smooth k
        (GLCoord k (Label τ) ⧸ subgroupIdeal (toralCentralizerPointSubgroup τ k a)) ∧
      ∃ eZ : WithConv ((GLCoord k (Label τ) ⧸
          subgroupIdeal (toralCentralizerPointSubgroup τ k a)) →ₐ[k] k) ≃*
            toralCentralizer τ k a, ∀ φ,
        ((eZ φ : toralCentralizer τ k a) : ModGL τ k) =
          (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) ∧
    ∀ e : ℕ, 1 ≤ e →
      ∃ σ : (GLCoord k (Label τ) ⧸ subgroupIdeal (toralCentralizerPointSubgroup τ k a)) →ₐc[k]
          (GLCoord k (Label τ) ⧸ subgroupIdeal (toralCentralizerPointSubgroup τ k a)),
        (∀ φ, (modGLPoint τ k).symm (toConv ((pointMap σ φ).ofConv.comp
            (Ideal.Quotient.mkₐ k _))) =
          Units.map (entrywiseHom (iterateFrobenius k p e))
            ((modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))))) ∧
        (∀ D ∈ tangentSpace k _ (Bialgebra.counitAlgHom k
            (GLCoord k (Label τ) ⧸ subgroupIdeal (toralCentralizerPointSubgroup τ k a))),
          D ∘ₗ (σ : (GLCoord k (Label τ) ⧸
              subgroupIdeal (toralCentralizerPointSubgroup τ k a)) →ₐ[k]
            (GLCoord k (Label τ) ⧸
              subgroupIdeal (toralCentralizerPointSubgroup τ k a))).toLinearMap = 0) ∧
        ∀ c ∈ toralCentralizer τ k a, ∃ z ∈ toralCentralizer τ k a,
          z⁻¹ * Units.map (entrywiseHom (iterateFrobenius k p e)) z = c := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨⟨-, hGZ, -, -, -, -, -, hpts, hsm⟩, ⟨hM, -, -, -, -⟩, -, -, hMZ, -, -⟩ :=
    exceptional_toral_centralizer_identity_component τ k hk a ha
  have hZ : IsConnectedAlgebraicSubgroup k (toralCentralizerPointSubgroup τ k a) := by
    rw [toralCentralizerPointSubgroup, ← hMZ hτ]
    exact hM
  refine ⟨⟨hZ, hGZ, hsm, hpts⟩, fun e he => ?_⟩
  obtain ⟨σ, hpt, hzero, hlang⟩ := exists_frobTwist_restriction p hZ he 1
    fun g hg => frobTwistGL_one_mem_toralCentralizer p e ha hg
  refine ⟨σ, fun φ => ?_, hzero, fun c hc => ?_⟩
  · rw [hpt, frobTwistGL_apply, one_mul, inv_one, mul_one]
  · obtain ⟨z, hz, hzc⟩ := hlang c hc
    refine ⟨z, hz, ?_⟩
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc
    exact hzc

end CFSG.LieType.AlgebraicGroups
