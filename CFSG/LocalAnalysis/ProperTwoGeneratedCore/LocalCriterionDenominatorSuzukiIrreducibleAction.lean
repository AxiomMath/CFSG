module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiPartition
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization

theorem projective_fixed_line_invariant {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (f : V ≃ₗ[K] V) (p : ℙ K V)
    (hfix : f • p = p) :
    ∀ v ∈ p.submodule, f v ∈ p.submodule := by
  have hmk : f • Projectivization.mk K p.rep p.rep_nonzero =
      Projectivization.mk K p.rep p.rep_nonzero := by
    simpa only [Projectivization.mk_rep] using hfix
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hmk
  obtain ⟨a, ha⟩ := hmk
  change (a : K) • p.rep = f p.rep at ha
  intro v hv
  rw [Projectivization.submodule_eq] at hv ⊢
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv
  apply Submodule.mem_span_singleton.mpr
  refine ⟨b * (a : K), ?_⟩
  rw [← hb, map_smul, ← ha, mul_smul]

theorem suzuki_degree_divisor_projective_fixedPointFree (m : ℕ)
    (g : SuzukiMatrixGroup m) (hg : g ≠ 1)
    (hdiv : orderOf g ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)
    (p : ℙ (BinaryGaloisField (2 * m + 1))
      (Fin 4 → BinaryGaloisField (2 * m + 1))) :
    (suzukiNaturalRepresentation m g).toLinearEquiv • p ≠ p := by
  intro hfix
  have hU := suzuki_degree_divisor_irreducible m g hg hdiv p.submodule
    (projective_fixed_line_invariant _ p hfix)
  have hdim := p.finrank_submodule
  rcases hU with hbot | htop
  · rw [hbot, finrank_bot] at hdim
    omega
  · rw [htop, finrank_top, Module.finrank_pi, Fintype.card_fin] at hdim
    omega

theorem suzuki_degree_divisor_derangement
    (m : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ≠ 1) (hdiv : orderOf g ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) :
    suzukiDerangement m g := by
  intro p hp
  exact suzuki_degree_divisor_projective_fixedPointFree m g hg hdiv p.val
    (congrArg Subtype.val hp)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
