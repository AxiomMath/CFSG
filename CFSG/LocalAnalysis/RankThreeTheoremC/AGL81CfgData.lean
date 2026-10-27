module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure AGL81CfgData (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  escape : ∃ H₁ R₁ : Subgroup G, D1Escape p P M H₁ R₁
  maxH : GLBIsMaxTwoLocal H
  base : IsAGLQ p M Q
  le_H : Q ≤ H
  not_le : ¬ H ≤ M
  not_le_X0 : ¬ K ≤ d1X0 p M H
  primeCore_le : (primeComplementCore (G := H) p).map H.subtype ≤ M
  kbar : K = d1KBar p M H
  b3 : Hyp111B3 p H Q K
  sylowK : ∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
    (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K
  star : ∀ R : Subgroup G, IsMaxInvariantTwoIn Q R (d1PlusCore p H K) → R ≠ ⊥ →
    CFSG.Quasithin.CGS R ≤ H ∧ CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo Q R

theorem AGL81ElevenData.toCfg {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81ElevenData p P M H Q K) :
    AGL81CfgData p P M H Q K :=
  ⟨hd.escape, hd.maxH, hd.pair.base, hd.pair.le_H, hd.pair.not_le, hd.pair.not_le_X0,
    hd.pair.primeCore_le, hd.kbar, hd.b3, hd.sylowK, hd.star⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
