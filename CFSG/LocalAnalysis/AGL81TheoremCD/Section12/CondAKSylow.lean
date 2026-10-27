module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem not_hypA_of_cStarGen (hC : CStarGen G) : ¬ HypA G := by
  rintro ⟨-, M, hM, p, hpσ, H, hH, h3, hHM⟩
  have hp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hpσ.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEHM, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (H := H ⊓ M) (k := 2) h3.le
  have hEp : IsPGroup p E :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hE
  have hErank : 2 ≤ CFSG.Open.pRank p E :=
    CFSG.SectionRank.le_pRank hp.one_lt (H := E) (E := E) le_rfl hE (k := 2) hEcard
  exact hHM (hC.embed p hpσ.1 M hM E (hEHM.trans inf_le_right) hEp hErank
    H hH (hEHM.trans inf_le_left))

theorem TwelveCtx.isSylowOf_inf_kSub {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) :
    CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ kSub p M H) (kSub p M H) := by
  rcases h.H_mem_H4.2.1 with h1 | ⟨-, -, hA, -⟩
  · exact h1
  · exact absurd hA (not_hypA_of_cStarGen h.cstar)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
