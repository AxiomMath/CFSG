module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NormalizerComplementPlaneAssembly

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem inf_eq_bot_of_isInternalSemidirectProduct_inf {X S M : Subgroup G}
    (hX : FreeCore.IsInternalSemidirectProduct X S (M ⊓ X)) (hSX : S ≤ X) : S ⊓ M = ⊥ :=
  le_antisymm
    ((le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hSX))).trans hX.inf_eq_bot.le)
    bot_le

theorem FTS_sigma_normalizer_complement
    (h₁ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FTS_sigma_normalizer_complement.{u} := by
  intro G _ _ hG M N hM hN hMN q hqM Q hQM hQcard hNQ hqN
  have hG08 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hsemi := FTS_normalizer_complement_plane_assembly h₁ h₂ G hG08 M N Q q hM hN hMN hqM hQM
    hQcard hNQ hqN
  exact ⟨hsemi.coe_eq_mul.symm,
    inf_eq_bot_of_isInternalSemidirectProduct_inf hsemi (sigmaCore_le N), hsemi⟩

end

end CFSG.FeitThompson.Proofs
