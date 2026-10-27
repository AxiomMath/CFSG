module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKCtx
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKCtx.commutator_le_xSub
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {L L' I W : Subgroup G} (hL : L ∈ weakBlockSet M H) (hL' : L' ∈ weakBlockSet M H)
    (hne : L ≠ L') (hIL : I ≤ H ⊓ L) (hWL : W ≤ H ⊓ L') : ⁅I, W⁆ ≤ xSub p M H := by
  haveI : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  have hpcore : ⁅I, W⁆ ≤ pCoreOf 2 M :=
    (Subgroup.commutator_mono (hIL.trans inf_le_right) (hWL.trans inf_le_right)).trans
      (IsTwoPrimeComponent.commutator_le hL.toIsTwoPrimeComponent hL'.toIsTwoPrimeComponent hne)
  have hH : ⁅I, W⁆ ≤ H :=
    (Subgroup.commutator_le_sup I W).trans
      (sup_le (hIL.trans inf_le_left) (hWL.trans inf_le_left))
  have hcore : pCoreOf 2 M ⊓ H ≤ pCoreOf 2 (H ⊓ M) := by
    refine (le_inf (le_inf inf_le_right ?_) inf_le_left).trans
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (X := H ⊓ M) (H := M) inf_le_right)
    exact inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
  rw [← hc.ctx.pCore_two_inter] at hcore
  exact (le_inf hpcore hH).trans (hcore.trans
    ((CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore
      hc.ctx.p_odd H).trans (relPPrimeCore_le_xSub hc.ctx.p_prime M H)))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
