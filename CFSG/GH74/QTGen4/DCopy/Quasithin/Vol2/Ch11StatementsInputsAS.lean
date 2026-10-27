module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Pointwise

@[expose] def AS_C_1_32_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
      IsG2Block L ∨ IsAltBlockType L 6 ∨ IsSp4Block L ∨ IsHatA6Block L ∨
        ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
          Fintype.card F = 2 ^ n ∧ IsModO2Surj L α

end CFSG.Quasithin.ASInputs
