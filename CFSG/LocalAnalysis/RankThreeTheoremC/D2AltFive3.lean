module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LieAlt3
import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSevenPrime

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2AltFive3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (p : ℕ) [Fact p.Prime], p ∈ rankThreeSigmaA G → p = 5 →
    ∀ (P : Sylow p G) (A H : Subgroup G), IsCoreMaxLocal p P M → D2Escape p P M A H A →
    D2EscapeMax p P M A →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) → False

theorem d2AltNoConfig3_of_five3 (h5 : D2AltFive3 G) : D2AltNoConfig3 G := by
  intro hS hD1 M hM hfc hthree p _ hσ hp5 P A H hcore hesc hmax Rbar K hRbar hK ⟨e⟩
  by_cases hp : p = 5
  · exact h5 hS hD1 M hM hfc hthree p hσ hp P A H hcore hesc hmax Rbar K hRbar hK ⟨e⟩
  · have hp6 : p ≠ 6 := by
      rintro rfl
      exact absurd (Fact.out : Nat.Prime 6) (by norm_num)
    exact hesc.false_of_alt_seven_le (aglGlobal_of_setting hS) (d1For_of_setting hS) hRbar hK e
      (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC
