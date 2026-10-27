module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Defs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup AltStdCycTwo

@[expose] def Sec4WreathFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      HData θ c.hn8 z T → WreathStruct z T → False

theorem false_of_chainW (h1 : Sec4FusionN0) (h2 : Sec4N0Struct) (h3 : Sec4N0Elementary)
    (h4 : Sec4HSetup) (h5 : Sec4HbarCases) (h6 : Sec4HbarNotSmall) (h7 : Sec4HbarNotSL)
    (h8 : Sec4Wreath49) (hW : Sec4WreathFalse) {G : Type} [Group G] [Finite G]
    {L Q : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
    (c : Config G L Q n θ z) : False := by
  obtain ⟨T, hT⟩ := h2 G L Q n θ z c (h1 G L Q n θ z c)
  have hH : HData θ c.hn8 z T := h4 G L Q n θ z c T hT (h3 G L Q n θ z c T hT)
  have hWc : Nat.card (Hbar T) = 56448 := by
    rcases h5 G L Q n θ z c T hH with h | h | h | h | h
    · exact absurd h (h6 G L Q n θ z c T hH).1
    · exact absurd h (h6 G L Q n θ z c T hH).2
    · exact h
    · exact absurd h (h7 G L Q n θ z c T hH).1
    · exact absurd h (h7 G L Q n θ z c T hH).2
  exact hW G L Q n θ z c T hH (h8 G L Q n θ z c T hH hWc)

theorem cycTwoInnerSmallFalseE_of_chainW (h1 : Sec4FusionN0) (h2 : Sec4N0Struct)
    (h3 : Sec4N0Elementary) (h4 : Sec4HSetup) (h5 : Sec4HbarCases) (h6 : Sec4HbarNotSmall)
    (h7 : Sec4HbarNotSL) (h8 : Sec4Wreath49) (hW : Sec4WreathFalse) :
    ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
      (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwoE G L Q n θ z → n ≤ 11 →
        centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) → False := by
  intro G _ _ L Q n θ z hT h11 hin
  exact false_of_chainW h1 h2 h3 h4 h5 h6 h7 h8 hW
    (⟨hT, h11, Or.inl hin⟩ : Config G L Q n θ z)

theorem cycTwoShapeTwoSmallFalse_of_chainW (h1 : Sec4FusionN0) (h2 : Sec4N0Struct)
    (h3 : Sec4N0Elementary) (h4 : Sec4HSetup) (h5 : Sec4HbarCases) (h6 : Sec4HbarNotSmall)
    (h7 : Sec4HbarNotSL) (h8 : Sec4Wreath49) (hW : Sec4WreathFalse) :
    ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
      (θ : L ≃* alternatingGroup (Fin n)) (z u : G), OrderTwoE G L Q n θ z → n ≤ 9 →
        u ∈ centralizer ({z} : Set G) → u ∉ L ⊔ centralizer (L : Set G) → u ^ 2 = 1 → False := by
  intro G _ _ L Q n θ z u hT h9 huC huO hu1
  exact false_of_chainW h1 h2 h3 h4 h5 h6 h7 h8 hW
    (⟨hT, by omega, Or.inr ⟨h9, u, huC, huO, hu1⟩⟩ : Config G L Q n θ z)

end CFSG.OddStandard.AltStdSmall4

