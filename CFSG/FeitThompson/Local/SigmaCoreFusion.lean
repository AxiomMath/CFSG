module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep08

universe u

theorem exists_mem_conj_eq_of_conjBy_eq {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {M : Subgroup G} (hM : IsCoatom M) {x g c : G}
    (hc : x * c = c * x) (hconj : conjBy M c = MulAut.conj g • M) :
    ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m := by
  have hkey : ∀ y : G, c * y * c⁻¹ ∈ M ↔ g⁻¹ * y * g ∈ M := by
    intro y
    have h := SetLike.ext_iff.1 hconj y
    rw [mem_conjBy, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa [MulAut.conj, mul_assoc] using h
  refine ⟨c * g, ?_, ?_⟩
  ·
    rw [mem_iff_forall_conj_mem_of_isCoatom hna hM]
    intro y
    have h := hkey (c⁻¹ * y * c)
    have e1 : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
    have e2 : g⁻¹ * (c⁻¹ * y * c) * g = (c * g)⁻¹ * y * (c * g) := by group
    rwa [e1, e2] at h
  ·
    have hcxc : c⁻¹ * x * c = x := by rw [mul_assoc, hc, inv_mul_cancel_left]
    calc g⁻¹ * x * g = g⁻¹ * (c⁻¹ * x * c) * g := by rw [hcxc]
      _ = (c * g)⁻¹ * x * (c * g) := by group

theorem FTS_sigma_core_fusion
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u}) :
    Statements.FTS_sigma_core_fusion.{u} := by
  intro G _ _ hG M hM x hx g hxg
  rcases eq_or_ne x 1 with rfl | hx1
  · exact ⟨1, one_mem M, by simp⟩
  have hamb : IsFTAmbient G :=
    { isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      odd_natCard := hG.odd_natCard
      isSolvable := hG.isSolvable_of_ne_top }
  have := hG.isSimpleGroup
  have hxU : x ∈ sigmaSupport G := mem_sigmaSupport.2 ⟨M, hM, hx, hx1⟩
  have hNcoatom : IsCoatom (MulAut.conj g • M) := isCoatom_conj_smul hM g
  have hxN : x ∈ sigmaCore (MulAut.conj g • M) := by
    rw [sigmaCore_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.conj, mul_assoc] using hxg
  obtain ⟨r, hr, -⟩ := (h₁ G hamb x hxU).2.2.2.1 M (mem_sigmaSupportingMaximals.2 ⟨hM, hx⟩)
    (MulAut.conj g • M) (mem_sigmaSupportingMaximals.2 ⟨hNcoatom, hxN⟩)
  exact exists_mem_conj_eq_of_conjBy_eq hG.not_isMulCommutative hM
    (Subgroup.mem_centralizer_iff.1 (sigmaSignalizer_le_centralizer x r.2) x rfl) hr

end

end CFSG.FeitThompson.Proofs
