module

public import CFSG.GH74.GLS.SP.Local.SPLNotation

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local
open scoped Pointwise commutatorElement

section Ct

variable {G : Type} [Group G]

@[expose] def SPLNot1.Ict (D : SPLNot1 G) : Subgroup G := ⁅D.Ct ⊓ D.K, D.Ct ⊓ D.K⁆

@[expose] def SPLNot1.Act (D : SPLNot1 G) : Subgroup G := pPrimeCoreOf 2 D.Ct

@[expose] def SPLPumpAt (D : SPLNot1 G) : Prop := pLayerOf 2 D.Ct ≤ D.Act ⊔ D.Ict

@[expose] def SPLCenIAt (D : SPLNot1 G) : Prop :=
  ∀ c ∈ D.Ct, (∀ i ∈ D.Ict, ⁅i, c⁆ ∈ D.Act) → ∃ k : ℕ, c ^ (2 ^ k) ∈ D.Act

end Ct

end CFSG.GH74.GLS.SP.Local
