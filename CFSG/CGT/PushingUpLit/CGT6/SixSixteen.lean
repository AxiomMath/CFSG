module

public import CFSG.CGT.PushingUpLit.SixThreeBasic
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

@[expose] def AschbacherSixSixteenPR : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G), InClassX ↥Y → Y = ⁅jIn (T : Subgroup G), Y⁆ →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∀ S : Subgroup G, IsSylowOf 2 S (Subgroup.normalizer (R : Set G)) →
            IsSylowOf 2 (S ⊓ Subgroup.normalizer (Y : Set G)) (Subgroup.normalizer (Y : Set G)) →
            ⁅omegaOneCenterIn S, Y⁆ ≠ ⊥ → oTwoIn (Subgroup.normalizer (R : Set G)) = R

variable {G : Type} [Group G] [Finite G]

end CFSG.CGT.PushingUpLit.CGT6
