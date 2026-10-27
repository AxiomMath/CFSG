module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Elim

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

namespace S11

variable {G : Type} [Group G] [Finite G] {m : ℕ}

theorem mu_nonempty (hctx : ThmACtx G m) : ∃ q, q ∈ Mu G m := by
  obtain ⟨q, hq, hq2, hq3⟩ := hctx.1.delta_witness
  exact ⟨q, hq, hq2, hq3⟩

theorem prop114 (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs114 G)
    (hne : ∀ q ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax q B x L ∧ InnerDiagMarking B L) :
    ∃ p ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
      IsSStarMax p B x L ∧ SplitInnerDiagMarking16 p B L := by
  by_contra hno
  obtain ⟨q, hq⟩ := mu_nonempty hctx
  obtain ⟨B, x, L, hSS, hID⟩ := hne q hq
  exact no_R ⟨hctx, hsf, hin, hno⟩ ⟨hq, hSS, hID⟩

end S11

end CFSG.LocalAnalysis.GLTheoremA
