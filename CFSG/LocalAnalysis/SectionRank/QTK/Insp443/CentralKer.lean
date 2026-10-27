module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def CentralKer {K : Type} [Group K] (L V : Subgroup K) : Prop :=
  ⁅L ⊓ Subgroup.centralizer (V : Set K), L⁆ ≤ pCoreOf 2 L

@[expose] def ForKF (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (L V MK : Subgroup K),
    KConf K L V MK → CentralKer L V → P (K ⧸ Subgroup.center K) → ConclK K L V MK

end CFSG.SectionRank.QTK.Insp443
