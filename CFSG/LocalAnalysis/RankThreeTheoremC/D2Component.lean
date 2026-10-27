module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Reduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore HasPrimeConstraint)

variable {G : Type} [Group G] [Finite G]

theorem d2Escape_almostSimple3 (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R) :
    ∃ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K :=
  h.almostSimple_of hS.simple hS.nonab hS.kProper

@[expose] def D2ComponentCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K → False

theorem d2EscapeCase3_of_componentCase3 (hcomp : D2ComponentCase3 G) : D2EscapeCase3 G := by
  intro hS hD1 M hM ha hb p hp P A H R hMP hesc
  obtain ⟨Rbar, K, hRbar, hK⟩ := d2Escape_almostSimple3 hS hesc
  exact hcomp hS hD1 M hM ha hb p hp P A H R hMP hesc Rbar K hRbar hK

theorem theoremD2_of_componentCase3 (hS : Setting G) (hD1 : TheoremD1 G)
    (hcomp : D2ComponentCase3 G) : TheoremD2 G :=
  theoremD2_of_escapeCase3 hS hD1 (d2EscapeCase3_of_componentCase3 hcomp)

@[expose] def D2ComponentCaseMax3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R → D2EscapeMax p P M R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K → False

theorem d2EscapeCase3_of_componentCaseMax3 (hcomp : D2ComponentCaseMax3 G) : D2EscapeCase3 G := by
  intro hS hD1 M hM ha hb p hp P A H R hMP hesc
  obtain ⟨A', H', R', hesc', hmax⟩ := hesc.exists_max
  obtain ⟨Rbar, K, hRbar, hK⟩ := d2Escape_almostSimple3 hS hesc'
  exact hcomp hS hD1 M hM ha hb p hp P A' H' R' hMP hesc' hmax Rbar K hRbar hK

theorem d2ComponentCase3_of_max (h : D2ComponentCaseMax3 G) : D2ComponentCase3 G :=
  fun hS hD1 M hM ha hb p hp P A H R hMP hesc _ _ _ _ =>
    d2EscapeCase3_of_componentCaseMax3 h hS hD1 M hM ha hb p hp P A H R hMP hesc

end CFSG.LocalAnalysis.RankThreeTheoremC
