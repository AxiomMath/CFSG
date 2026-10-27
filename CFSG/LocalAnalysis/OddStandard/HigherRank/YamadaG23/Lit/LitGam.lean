module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

structure LitGam {Γ : Type} [Group Γ] (Gh Zh Ah : Subgroup Γ) (t : Γ) : Prop where
  Z_le_G : Zh ≤ Gh
  Z_central : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x
  Z_le_A : Zh ≤ Ah
  A_le_G : Ah ≤ Gh
  card_A : Nat.card Ah = 64
  comm_mem : ∀ a ∈ Ah, ∀ b ∈ Ah, ⁅a, b⁆ ∈ Zh
  sylow : IsSylowIn 2 (Gh ⊓ centralizerSection Ah Zh) Ah
  ord_t : orderOf t = 2
  t_G : t ∈ normalizer (Gh : Set Γ)
  t_Z : t ∈ normalizer (Zh : Set Γ)
  five_a : Ah ≤ Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh
  five_b : Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ≤ normalizer (Ah : Set Γ)
  seven : ∀ n ∈ normIn Gh Ah, ∃ m ∈ normIn Gh Ah, ∃ c ∈ Gh ⊓ centralizerSection Ah Zh,
    n = m * c ∧ ⁅m, t⁆ ∈ Ah

end CFSG.OddStandard.HigherRank.YamadaG23
