module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G]

@[expose] def oTwoPrimeTwo (X : Subgroup G) : Subgroup G :=
  ((CFSG.pCore 2 (↥X ⧸ GLAPPrimeCore 2 ↥X)).comap
    (QuotientGroup.mk' (GLAPPrimeCore 2 ↥X))).map X.subtype

@[expose] def layerPreimage (X : Subgroup G) : Subgroup G :=
  GLAPLayer 2 X ⊔ oTwoPrimeTwo X

@[expose] def centerOf (P : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥P).map P.subtype

@[expose] def IsUGroup [Finite G] (p : ℕ) (P U : Subgroup G) : Prop :=
  U ≤ P ∧ P ≤ Subgroup.normalizer (U : Set G) ∧ IsPPlane p U ∧
    (1 < pRank p (centerOf P) → U ≤ centerOf P)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
