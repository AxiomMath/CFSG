module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MLayer
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Hall

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem frobConclusion_of_kfacts (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    FrobConclusion p M x := by
  haveI : Fact p.Prime := ⟨hl.loc.beta.1⟩
  exact frobConclusion_of_parts hK.coprimeAut hG hl (fr_layer_eq_bot hK hG hl)
    (fr_fpf hK hG hl)

theorem ysPPointFrobenius_of_kfacts (hK : FrobKFacts) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointFrobenius :=
  ysPPointFrobenius_of_local fun _ _ _ hG _ _ _ _ hl => frobConclusion_of_kfacts hK hG hl

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
