module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaFixedCoreMeetsNoConjugateMaximal
import CFSG.FeitThompson.Local.SigmaSubgroupConjugateCore
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem mem_conjSub_of_mem {Y : Subgroup G} {g y : G} (hy : y ∈ Y) :
    g⁻¹ * y * g ∈ conjSub g Y := by
  rw [mem_conjSub]; simpa [mul_assoc] using hy

theorem le_conjBy_inv_of_conjSub_le {X Y : Subgroup G} {g : G} (h : conjSub g Y ≤ X) :
    Y ≤ conjBy X g⁻¹ := fun _ hy => mem_conjBy.2 (by simpa using h (mem_conjSub_of_mem hy))

theorem conjBy_sigmaCore_inv_eq_self [Finite G] {M : Subgroup G} {g : G} (hg : g⁻¹ ∈ M) :
    conjBy (sigmaCore M) g⁻¹ = sigmaCore M :=
  mem_normalizer_iff_conj_inv_smul_eq.1 (le_normalizer_sigmaCore M hg)

theorem FTS_kappa_fixed_intersection_sigma_containment
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₆ : Statements.FTS_sigma_prime_separation.{u})
    (h₇ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FTS_kappa_fixed_intersection_sigma_containment.{u} := by
  intro G _ _ hG M hM hκ K hK Y hYπ hne
  have hG09 : IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hYbot : Y ≠ ⊥ := by rintro rfl; exact hne (by simp)
  obtain ⟨g, hg⟩ :=
    FTS_sigma_subgroup_conjugate_core h₃ h₄ h₅ h₆ G hG09 M hM Y hYbot hYπ
  have hYS : Y ≤ conjBy (sigmaCore M) g⁻¹ := le_conjBy_inv_of_conjSub_le hg
  have hYM : Y ≤ conjBy M g⁻¹ := hYS.trans (conjBy_le_conjBy_iff.2 (sigmaCore_le M))
  have hgM : g⁻¹ ∈ M := by
    by_contra hgo
    have hdis := FTS_kappa_fixed_core_outside_conjugate_disjoint h₁ h₂ h₇ G hG M hM hκ K hK g⁻¹ hgo
    refine hne (le_bot_iff.1 ?_)
    calc Y ⊓ (sigmaCore M ⊓ centralizer (K : Set G))
        ≤ (sigmaCore M ⊓ centralizer (K : Set G)) ⊓ conjBy M g⁻¹ :=
          le_inf inf_le_right (inf_le_left.trans hYM)
      _ = ⊥ := hdis
  rwa [conjBy_sigmaCore_inv_eq_self hgM] at hYS

end

end CFSG.FeitThompson.Proofs
