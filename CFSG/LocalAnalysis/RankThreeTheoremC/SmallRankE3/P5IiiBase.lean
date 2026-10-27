module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def Prop614FiveOf (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 5 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G 5 P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M

structure L630Setting3 (G : Type) [Group G] [Finite G] (P : Sylow 5 G) (M : Subgroup G)
    (x z : G) (T : Subgroup G) (f : ℕ) : Prop where
  setting : Setting G
  d1 : TheoremD1 G
  situation : SmallRankSituation G 5 P M
  point : SmallRankPoint P M x
  central : SmallRankCentral P z
  prop614 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set G) →
    normalizer (S₀ : Set G) ≤ M
  sylowTwo : SmallRankSylowTwo P M T
  cover : SmallRankCover 5 M x
  lemma628 : Lemma628Concl 5 M x z T
  prime : f.Prime
  ne_two : f ≠ 2
  core_ne_bot : pCoreOf f (smallRankD 5 x) ≠ ⊥
  lemma629 : Lemma629Concl 5 M x z T f

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x z : G}
  {T : Subgroup G} {f : ℕ}

theorem L630Setting3.of_hyp (hS : Setting G) (hD1 : TheoremD1 G) (h614 : Prop614FiveOf G)
    (hyp : Lemma630Hyp G 5 P M x z T f) : L630Setting3 G P M x z T f :=
  ⟨hS, hD1, hyp.failure.situation, hyp.failure.point, hyp.failure.central,
    fun S₀ h1 h2 h3 => h614 P M x z T hyp.failure S₀ h1 h2 h3, hyp.failure.sylowTwo, hyp.cover,
    hyp.lemma628, hyp.prime, hyp.ne_two, hyp.core_ne_bot, hyp.lemma629⟩

theorem Prop627Failure.mk_five (hsit : SmallRankSituation G 5 P M) (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) (hT : SmallRankSylowTwo P M T) : Prop627Failure G 5 P M x z T :=
  ⟨hsit, hx, hz, hT, fun h => absurd h.1 (by norm_num)⟩

theorem L630Setting3.failure (hL : L630Setting3 G P M x z T f) : Prop627Failure G 5 P M x z T :=
  Prop627Failure.mk_five hL.situation hL.point hL.central hL.sylowTwo

theorem L630Setting3.centralizer_z_le (hL : L630Setting3 G P M x z T f) :
    centralizer ({z} : Set G) ≤ M := fun g hg =>
  (hL.failure.normalizer_zpowers_le hL.setting)
    (centralizer_singleton_le_normalizer_zpowers z hg)

@[expose] def L613f3E3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (P : Sylow 5 G) (M : Subgroup G) (x z : G), SmallRankSituation G 5 P M →
      SmallRankPoint P M x → SmallRankCentral P z → ¬ CFSG.ABGLocalTools.IsPConstrained 5 ↥M →
        ∀ (H K : Subgroup G), H ≤ M ⊓ centralizer ({x} : Set G) →
          CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection H K →
          5 ∣ K.relIndex H → 3 ∣ K.relIndex H → CFSG.Open.GLBStronglyEmbedded 3 M

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
