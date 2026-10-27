module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsData
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.AltHSInduction

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.OddStandard.AltStdSec CFSG.EvenSporadicStandard.HSStd

@[expose] def AltStdBalancedOrder2InnerSmallAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → n ≤ 11 → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
          (∀ z : G, z ∈ centralizer (L : Set G) → orderOf z = 2 →
            centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) → False

@[expose] def ShapeTwoSmallNineAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L Q : Subgroup G) (n : ℕ) (z u : G),
    Setting G L n → Cyc L Q z → ShapeTwo L Q z u → n ≤ 9 → False

end CFSG.OddStandard.AltHSInduction
