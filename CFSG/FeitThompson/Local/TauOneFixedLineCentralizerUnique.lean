module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TauOneFixedLineBetaOrDerived
import CFSG.FeitThompson.Local.TauOneHallFixedCentralizer
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type u} [Group G] [Finite G]

theorem isSylowIn_map_subtype_sigmaCore {q : ℕ} (hq : q.Prime) (M : Subgroup G)
    (S : Sylow q ↥(sigmaCore M)) :
    _root_.CFSG.FeitThompson.Prep06.IsSylowIn q
      ((S : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype) (sigmaCore M) := by
  have := Fact.mk hq
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective (sigmaCore M).subtype_injective]
  exact S.card_eq_multiplicity

theorem isMinimalOddSimple_of_isMinimalSimpleOddOrder (hG : IsMinimalSimpleOddOrder G) :
    _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G where
  odd := hG.odd_natCard
  simple := hG.isSimpleGroup
  nonabelian := hG.not_isMulCommutative
  solvable := hG.isSolvable_of_ne_top

theorem FTS_tau_one_fixed_line_centralizer_unique
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₄ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₆ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₇ : Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₈ : Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    Statements.FTS_tau_one_fixed_line_centralizer_unique.{u} := by
  intro G _ _ hG M hM E hEM hsd E₁ hE₁E hE₁hall P hPE₁ hPne q hq X hXc hXcard
  have : Fintype G := Fintype.ofFinite G
  have hE₁ne : E₁ ≠ ⊥ := fun h => hPne (le_bot_iff.1 (h ▸ hPE₁))
  have hfix := (FTS_tau_one_hall_fixed_centralizer h₁ h₃ h₈ G hG M hM E hEM hsd E₁ hE₁E
    hE₁hall).2 P hPE₁ hPne
  have hXE₁ : X ≤ centIn (sigmaCore M) (E₁ : Set G) := hfix ▸ hXc
  have hor := FTS_tau_one_fixed_line_beta_or_derived h₁ h₂ h₃ h₅ h₆ h₇ G hG M hM E hEM hsd E₁
    hE₁E hE₁ne hE₁hall q hq X hXE₁ hXcard
  have hXM : X ≤ M := (hXc.trans inf_le_left).trans (sigmaCore_le M)
  obtain ⟨hcent, hsyl⟩ :=
    h₄ G (isMinimalOddSimple_of_isMinimalSimpleOddOrder hG) M X hM q hq hXM hXcard hor
  exact ⟨hcent, fun S => hsyl _ (isSylowIn_map_subtype_sigmaCore hq M S)⟩

end

end CFSG.FeitThompson.Proofs
