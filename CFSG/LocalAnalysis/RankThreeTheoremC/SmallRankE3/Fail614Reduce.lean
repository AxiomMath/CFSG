module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fail614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fail614Stage
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Prime
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83SmallRankProp614Three (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H : Subgroup G, IsTwoLocal H → zpowers x ⊔ zpowers z ≤ H →
        (∃ S : Subgroup G, S ≤ H ⊓ M ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
          zpowers x ⊔ zpowers z ≤ normalizer (S : Set G)) → H ≤ M

theorem prop614Three_of_core (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK : KFactBlockFactorThreePrime)
    (hdich : ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z →
        HasPrimeConstraint (G := M) 3 ∨ SmallRankCaseDelta3 P M)
    (hnrδ : ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z → SmallRankCaseDelta3 P M →
        Fail614NormalizerRank P M (zpowers x ⊔ zpowers z))
    (hcore : Prop614FailCore G) : GL83SmallRankProp614Three G := by
  intro P M hsit x z hx hz H hH hBH hex
  obtain ⟨S, hSHM, hS2, hS1, hBS⟩ := hex
  by_contra hHM
  have hdi := hdich P M hsit x z hx hz
  have hnr : Fail614NormalizerRank P M (zpowers x ⊔ zpowers z) := by
    rcases hdi with hα | hδ
    · exact fail614NormalizerRank_of_alpha hS hsit hα hx hz
    · exact hnrδ P M hsit x z hx hz hδ
  have hB3 : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) (SmallRankPlane.of_situation hS hsit hx hz).card_eq
  obtain ⟨S', hSS', hS'⟩ := exists_isMaxTwoInvariantIn_of_le
    (B := zpowers x ⊔ zpowers z) (X := H ⊓ M) (S := S) ⟨hSHM, hS2, hBS⟩
  have hpair : Prop614Pair M (zpowers x ⊔ zpowers z) H S' :=
    ⟨hH, hBH, hHM, hS', ne_bot_of_le_ne_bot hS1 hSS'⟩
  obtain ⟨H₀, S₀, hopt⟩ := exists_fail614Optimal hS hU0 hD1 hsit hx hz hnr ⟨H, S', hpair⟩
  exact hcore P M hsit hdi x z hx hz H₀ S₀ hopt
    (primeCore_le_of_isMaxTwoInvariantIn hS hK hopt.ext.pair.isTwoLocal hB3 hopt.ext.pair.le
      hopt.maxInv hopt.char_le)

theorem prop614_failing_three_of_prop614Three (h : GL83SmallRankProp614Three G) :
    ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 3 P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
        zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M := by
  intro P M x z T hf S₀ hS₀S hS₀1 hzS₀
  have hS₀T : S₀ ≤ T := hS₀S.trans inf_le_left
  have hS₀2 : IsPGroup 2 S₀ := hf.sylowTwo.isPGroup.to_le hS₀T
  have hxc : x ∈ centralizer (S₀ : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hS₀S hs : s ∈ T ⊓ centralizer ({x} : Set G)).2
  have hxS₀ : zpowers x ≤ normalizer (S₀ : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hxc)
  exact h P M hf.situation x z hf.point hf.central (normalizer (S₀ : Set G))
    ⟨S₀, hS₀1, hS₀2, rfl⟩ (sup_le hxS₀ hzS₀)
    ⟨S₀, le_inf le_normalizer (hS₀T.trans hf.T_le_M), hS₀2, hS₀1, sup_le hxS₀ hzS₀⟩

theorem prop614_failing_three_of_core (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hK : KFactBlockFactorThreePrime)
    (hdich : ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z →
        HasPrimeConstraint (G := M) 3 ∨ SmallRankCaseDelta3 P M)
    (hnrδ : ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z → SmallRankCaseDelta3 P M →
        Fail614NormalizerRank P M (zpowers x ⊔ zpowers z))
    (hcore : Prop614FailCore G) :
    ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 3 P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
        zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M :=
  prop614_failing_three_of_prop614Three (prop614Three_of_core hS hU0 hD1 hK hdich hnrδ hcore)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
