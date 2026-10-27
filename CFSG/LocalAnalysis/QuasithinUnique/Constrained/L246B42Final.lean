module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Types

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open CFSG.SectionRank

namespace L238

section TauCeti

variable {G : Type} [Group G] [Finite G]

@[expose] def AltBlockStatementJ : Prop :=
  ∀ X T L : Subgroup G, CharTwo X → IsSQTKTC X → IsSylowTwoOf T X → IsBlock2 X L →
    blockU L ≤ VZ T X → thompsonJ T ≤ Subgroup.normalizer (L : Set G) →
    ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) →
    (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m) →
      IsChiBlock X L ∨ IsExcA7Block L

theorem altBlockStatementJ_of_asB42 (h42 : AsB42) (facts : Bridge.Alt57ModelFacts) :
    AltBlockStatementJ (G := G) := by
  intro X T L hX hSQ hT hL hUV hJN hnot ⟨m, hm, hm3, halt⟩
  exact L246.altBlock_of_odd Bridge.kClosed_native (Bridge.asB42With_kGroup.2 h42) facts hX hSQ.1
    (hSQ.2 3 Nat.prime_three (by norm_num)) hT hL hUV hJN hnot hm hm3 halt

end TauCeti

end L238

end CFSG.QuasithinUnique
