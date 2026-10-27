module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open CFSG.Open

theorem pRank_top_eq_of_mulEquiv_center_quotient {G T : Type} [Group G] [Finite G]
    [Group T] [Finite T] {q : ℕ} (hq : q.Prime) (e : G ⧸ Subgroup.center G ≃* T)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center G)) :
    CFSG.Open.pRank q (⊤ : Subgroup G) = CFSG.Open.pRank q (⊤ : Subgroup T) := by
  haveI : Fact q.Prime := ⟨hq⟩
  calc CFSG.Open.pRank q (⊤ : Subgroup G)
      = CFSG.Open.pRank q (⊤ : Subgroup (G ⧸ Subgroup.center G)) :=
        (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center G) hZ).symm
    _ = CFSG.Open.pRank q (⊤ : Subgroup T) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt e

end CFSG.ClassicalGroups.SpecialLinear

end
