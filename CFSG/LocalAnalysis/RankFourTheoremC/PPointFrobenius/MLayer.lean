module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MLayer2
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.PerfectLift

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_layer_eq_bot [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) :
    CFSG.layer (M ⧸ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := M) p) = ⊥ := by
  by_contra hne
  obtain ⟨J, hJperf, hJU, hxJ, hJconj, hJcyc⟩ := fr_exists_perfect_lift hK hG hl hne
  exact fr_false_of_perfect_lift hK hG hl hJperf hJU hxJ hJconj hJcyc

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
