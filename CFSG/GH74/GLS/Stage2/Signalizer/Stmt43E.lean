module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Concl

variable {A : Type} [Group A] [Finite A]

@[expose] def C43d1 (k : Kind) (z : A) (X : Subgroup A) : Prop :=
  (k = Kind.mcl ∨ k = Kind.ly) ∧ Nat.card ↥X = 3 ∧
    (IsPGL3Four ↥(ncl X) ∧ ncl X ⊓ centralizer ({z} : Set A) = ⁅ncl X, ncl X⁆ ⊓ centralizer (X : Set A) ∧
      IVK.IsL2 ↥(ncl X ⊓ centralizer ({z} : Set A)) (fun q => q = 4) ∧
      (ncl X ⊔ zpowers z) ⊓ centralizer ((ncl X ⊓ centralizer ({z} : Set A) : Subgroup A) : Set A) =
        X ⊔ zpowers z)

@[expose] def Concl43E (k : Kind) (z : A) (p : ℕ) (X : Subgroup A) : Prop :=
  C43b p X ∨ C43c z p X ∨ C43d1 k z X ∨ C43e X

end Concl

@[expose] def Prop4_3E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      ⁅layer (Sec H₀ H₁), X⁆ ≠ ⊥ →
      Concl43E k (zSec z H₀ hz H₁) p X

end CFSG.GH74.GLS.Stage2.Signalizer
