module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.SimpleSolvableNormalizerProper
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem centralizer_le_and_unique_coatom_of_isPlaneAt [Finite G]
    (h₁ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {M A X : Subgroup G} {p : ℕ} (hM : IsCoatom M)
    (hp : p.Prime) (hpσ : p ∉ sigmaPrimes M) (hAM : A ≤ M)
    (hA : CFSG.FeitThompson.Prep08.IsPlaneAt p A) (hXM : X ≤ M) (hX : X ≠ ⊥) (hXA : ⁅X, A⁆ = ⊥)
    (hcent : sigmaCore M ⊓ centralizer ((X : Subgroup G) : Set G) ≠ ⊥) :
    centralizer ((X : Subgroup G) : Set G) ≤ M ∧
      ∀ N : Subgroup G, IsCoatom N → centralizer ((X : Subgroup G) : Set G) ≤ N → N = M := by
  have := hG.isSimpleGroup
  have hplane : CFSG.FeitThompson.IsElementaryAbelianPlane p A :=
    nonempty_mulEquiv_pi_of_isElementaryAbelian hp hA.isElementaryAbelian hA.natCard
  have hosp : CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hM, hp, hpσ, hAM, hplane⟩
  have hAC : A ≤ centralizer ((X : Subgroup G) : Set G) :=
    le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hXA)
  have key : ∀ N : Subgroup G, IsCoatom N →
      centralizer ((X : Subgroup G) : Set G) ≤ N → N = M := by
    intro N hN hCN
    by_contra hNM
    have hdisj := h₁ G hG p M A N hosp hN hNM (hAC.trans hCN)
    exact hcent (le_bot_iff.1 (hdisj ▸ inf_le_inf_left _ hCN))
  refine ⟨?_, key⟩
  have hXtop : X ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hXM))
  have : Group.IsSolvable ↥X := hG.isSolvable_of_ne_top X hXtop
  have hlt : normalizer ((X : Subgroup G) : Set G) < ⊤ :=
    normalizer_coe_lt_top_of_isSolvable hG.not_isMulCommutative hX
  have hCtop : centralizer ((X : Subgroup G) : Set G) ≠ ⊤ :=
    fun h => hlt.ne (top_le_iff.1 (h ▸ centralizer_le_normalizer _))
  obtain ⟨N, hN, hCN⟩ := exists_isCoatom_ge_of_ne_top hCtop
  exact key N hN hCN ▸ hCN

theorem FTS_plane_centralizing_subgroup_unique_centralizer
    (h₁ : Statements.FNI_outside_sigma_plane_core_disjoint.{u}) :
    Statements.FTS_plane_centralizing_subgroup_unique_centralizer.{u} := by
  intro G _ _ hG M A X p hM hp hpσ hAM hA hXM hX hXA hcent
  exact centralizer_le_and_unique_coatom_of_isPlaneAt h₁
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    hM hp hpσ hAM hA hXM hX hXA hcent

end

end CFSG.FeitThompson.Proofs
