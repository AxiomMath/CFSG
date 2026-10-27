module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairSolvable

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2IndexCaseStrongAt3 (G : Type) [Group G] [Finite G] (i : TauCeti.CFSGIndex)
    (Pp : ℕ → Prop) : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, Pp p → ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R → D2EscapeMax p P M R →
    rankThreeGamma 1 p (P : Subgroup G) ≤ M →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) → False

theorem d2IndexCaseStrongAt3_of_indexCaseAt3 {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : D2IndexCaseAt3 G i Pp) : D2IndexCaseStrongAt3 G i Pp :=
  fun hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax _ Rbar K hRbar hK he =>
    h hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he

theorem d2IndexCaseAt3_of_pair {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (hPp : ∀ p, Pp p → p = 3) (hpair : D2PairAt i Pp) (h84 : Asc81bEightFour)
    (hX : D1NoXBlock3 G) (h : D2IndexCaseStrongAt3 G i Pp) : D2IndexCaseAt3 G i Pp := by
  intro hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  obtain rfl := hPp p hpp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpr : AGLPair 3 M H R := hesc.toPair (aglGlobal_of_setting hSet)
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq
      (hesc.primeCore_inf_eq_iff.mpr (hpair _ 3 hpp Rbar _ _ K hK he)))
  have hns : ¬ Group.IsSolvable M := fun hsolv =>
    hpr.false_of_isSolvable h84 (noXBlockFor_of_setting hX hSet) hsolv
  exact h hSet hD1 M hM ha hb 3 hp hpp P A H R hMP hesc hmax ((hb hp P hMP).2 hns) Rbar K hRbar
    hK he

end CFSG.LocalAnalysis.RankThreeTheoremC
