module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyEight

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaC₅ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaR₅ d t ⊓ yamadaCstar d t

@[expose] noncomputable def yamadaL₅ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₃ d t ⊔ yamadaL₄ d t

@[expose] noncomputable def yamadaE₅ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₅ d t ⊓ yamadaC₅ d t

@[expose] noncomputable def yamadaS₅ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaS₃ d t ⊔ yamadaS₄ d t

@[expose] noncomputable def yamadaM₅ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaM₃ d t ⊔ yamadaM₄ d t

@[expose] noncomputable def yamadaD₅ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaD₃ d t ⊔ yamadaD₄ d t

@[expose] noncomputable def yamadaF₅ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaF₃ d t ⊔ yamadaF₄ d t

@[expose] noncomputable def yamadaL₆ (d : G2Data L K) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaL₂ d t : Set G))

@[expose] noncomputable def yamadaR₆ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₆ d t ⊔ d.S

theorem yamadaL₆_le (d : G2Data L K) (t : G) :
    yamadaL₆ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaL₆ (d : G2Data L K) (t : G) :
    normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaL₆ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

end Defs

end CFSG.LocalAnalysis.EvenBN.G2
