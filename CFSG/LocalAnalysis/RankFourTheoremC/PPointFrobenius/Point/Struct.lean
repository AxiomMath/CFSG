module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Cyc

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem pt_structure [Fact p.Prime] (hk : PtKFacts) (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) : PtStruct p P M x := by
  obtain ⟨n, R, K, hD⟩ := pt_data hk hG hl
  have h3 := hD.three_le
  exact ⟨⟨inferInstance, n, by omega, pt_layer_equiv hs hG hl hD⟩, pt_layer_not_le hs hG hl hD,
    pt_cyclic hs hG hl hD⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
