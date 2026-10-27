module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma43Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma43Core
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_lemma43 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hP : Sz32Struct P x J a c y)
    (hL : Sz32Lines P x (a ^ 5)) (hZ : Sz32ZFacts P M x (a ^ 5))
    (hnorm : M ≤ Subgroup.normalizer ((P : Subgroup G) ⊔ rankThreePrimeCore 5 M : Subgroup G))
    {U : Subgroup G} (hU : Sz32Plane P x a c y U) :
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ Subgroup.normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ rankThreePrimeCore 5 M) (rankThreePrimeCore 5 M) →
      Subgroup.normalizer (Y : Set G) ≤ M := by
  intro Y hY2 hYM hUY hYB
  haveI : Fact (Nat.Prime 5) := ⟨hc.prime⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  obtain ⟨hRM, hRn, hRcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 5 M
  have hM2loc : IsTwoLocal M := hc.core.1.1
  have hCharM : CFSG.QuasithinUnique.CharTwo M := hS.charTwo M hM2loc
  have hM2 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P₂, hP₂1, hP₂2, hP₂M⟩ := hM2loc
    have hP₂le : P₂ ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP₂M ▸ Subgroup.le_normalizer)
        hP₂M.le hP₂2
    intro h
    exact hP₂1 (le_bot_iff.1 (hP₂le.trans h.le))
  have hO2R : pCoreOf 2 M ≤ rankThreePrimeCore 5 M :=
    Generic49U3.pCoreOf_two_le_relPPrimeCore (by have := hc.five; omega) M
  have hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 5 (H ⊓ M) → H ≤ M :=
    fun H hH hr => le_of_three_le_pRank_inf hD1 hc.sigma hc.core hH hr
  exact szj_case1_core hc.five hD1' hM2 hCharM hRM hRn hRcop hO2R hPM P.isPGroup' hnorm hU.le_P
    hY2 hYM hUY hYB
    (fun l hUS A B hAS hBS hUA hUB hAB => szj_rank_conj hP hZ hU l hUS hAS hBS hUA hUB hAB)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
