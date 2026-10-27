module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalPDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section DefsStar

variable {G : Type*} [Group G]
  {L : Subgroup G} {K : Type} [Field K]

noncomputable abbrev yamadaC₇ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaCstar d t

noncomputable abbrev yamadaR₇ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaRstar d t

end DefsStar

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaM₆ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaM₅ d t ⊔ (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom

@[expose] noncomputable def yamadaS₆ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaM₆ d t ⊔ d.S

@[expose] noncomputable def yamadaR₈ (d : G2Data L K) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaR₅ d t : Set G))

@[expose] noncomputable def yamadaP (d : G2Data L K) (t : G) : Subgroup G :=
  ⁅yamadaR₈ d t, d.J⁆

@[expose] noncomputable def yamadaS₇ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaP d t ⊓ yamadaR₇ d t

@[expose] noncomputable def yamadaD₇ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaP d t ⊓ yamadaC₇ d t

theorem yamadaM₅_le_yamadaM₆ (d : G2Data L K) (t : G) : yamadaM₅ d t ≤ yamadaM₆ d t :=
  le_sup_left

theorem yamadaM₆_le_yamadaS₆ (d : G2Data L K) (t : G) : yamadaM₆ d t ≤ yamadaS₆ d t :=
  le_sup_left

theorem S_le_yamadaS₆ (d : G2Data L K) (t : G) : d.S ≤ yamadaS₆ d t :=
  le_sup_right

theorem yamadaR₈_le (d : G2Data L K) (t : G) :
    yamadaR₈ d t ≤ normalizer (yamadaR₅ d t : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaR₈ (d : G2Data L K) (t : G) :
    normalizer (yamadaR₅ d t : Set G) ≤ normalizer (yamadaR₈ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem yamadaD₇_le_yamadaP (d : G2Data L K) (t : G) : yamadaD₇ d t ≤ yamadaP d t :=
  inf_le_left

theorem yamadaD₇_le_yamadaC₇ (d : G2Data L K) (t : G) : yamadaD₇ d t ≤ yamadaC₇ d t :=
  inf_le_right

end Defs

end CFSG.LocalAnalysis.EvenBN.G2
