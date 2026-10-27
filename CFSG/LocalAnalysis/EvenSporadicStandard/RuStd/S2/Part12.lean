module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.PartOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Fano
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.JankoFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.FanoA5

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

theorem a5Lemma : A5Lemma := fun e U hU => exists_three_normalizing_of_a5 e U hU

theorem fanoLemma : FanoLemma := by
  intro G _ E U U₁ t u r r₁ hE8 hE2 hU hU4 hU₁ hU₁4 htE htU huU huU₁ _ hrU hrt hr3 hrx _ hr₁U
    hr₁u hr₁3 hr₁x
  exact fano_transitive E U U₁ t u r r₁ hE8 hE2 hU hU4 hU₁ hU₁4 htE htU huU huU₁ hrU hrt hr3 hrx
    hr₁U hr₁u hr₁3 hr₁x

theorem jankoFiveLemma : JankoFiveLemma := fun {_ _ _ _ _ _ _ _ _} => janko_five_dvd

theorem partThreeData_of_stage2' {G : Type} [Group G] [Finite G] {L L₁ : Subgroup G} {t u : G}
    (hc : Config G L t) (hc₁ : Config G L₁ u) (huL : u ∈ L) (hu2 : orderOf u = 2)
    (hcard : Nat.card (centralizer ({(⟨u, huL⟩ : L)} : Set L)) = 116480)
    (hK : kComponent L ⟨u, huL⟩ ≤ L₁)
    (h2B : RuTwoBFacts L) (h5L : RuFiveFacts L) (h5L₁ : RuFiveFacts L₁) :
    Nonempty (PartThreeData G L t) :=
  partThreeData_of_stage2 a5Lemma fanoLemma hc hc₁ huL hu2 hcard hK h2B h5L h5L₁ jankoFiveLemma

end CFSG.EvenSporadicStandard.RuStd.S2
