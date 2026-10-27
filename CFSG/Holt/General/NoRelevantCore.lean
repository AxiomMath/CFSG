module

public import CFSG.Holt.General.NoRelevantBasic
import CFSG.Assembly.Defs

public section

namespace CFSG.Holt.General.NoRelevant

open MulAction Subgroup CFSG.ABGLocalTools

@[expose] def preFStar (G : Type*) [Group G] : Subgroup G :=
  (generalizedFitting (G ⧸ pPrimeCore 2 G)).comap (QuotientGroup.mk' (pPrimeCore 2 G))

variable {G : Type} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

instance preFStar_normal : (preFStar G).Normal := by
  have := generalizedFitting_normal (X := G ⧸ pPrimeCore 2 G)
  unfold preFStar
  exact Normal.comap this _

end CFSG.Holt.General.NoRelevant
