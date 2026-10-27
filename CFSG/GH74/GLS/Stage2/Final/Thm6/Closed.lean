module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def SL2OddCentBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ),
    Stage2Ctx G z (Kind.l4 ε) S → TypeL4 z (Kind.l4 ε) S ε q →
    ∀ K₁ K₂ : Subgroup G, IsCentralProd K₁ K₂ (Em (Cen z)) → HasSL2Model ↥K₁ (fun r => r = q) →
      HasSL2Model ↥K₂ (fun r => r = q) →
      ∀ t : G, IsConj z t → t ∈ S → t ∈ normalizer (K₁ : Set G) → (t ∈ K₁ ⊔ K₂ ↔ Fused ε q) →
        Nat.card ↥(pPrimeCoreOf 2 (K₁ ⊓ centralizer ({t} : Set G))) ∣ (if ε then q - 1 else q + 1)

end CFSG.GH74.GLS.Stage2.Final.Thm6
