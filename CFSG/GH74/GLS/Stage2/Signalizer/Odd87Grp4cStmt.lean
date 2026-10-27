module

public import CFSG.GH74.GLS.Stage2.Local.Concl
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Prop4_1c_i : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      ∀ W : Subgroup (Sec H₀ H₁), IsPGroup 2 ↥W → X ≤ normalizer (W : Set (Sec H₀ H₁)) →
        zSec z H₀ hz H₁ ∈ normalizer (W : Set (Sec H₀ H₁)) → ⁅W, X⁆ = W → W ≠ ⊥ →
        4 ≤ Nat.card ↥(zOf W ⊓ centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁))) →
        (k = Kind.mcl ∨ k = Kind.ly) ∧ IsL34Two ↥W ∧
          (centralizer (W : Set (Sec H₀ H₁))).relIndex X = 3 ∧
          CFSG.ABGLocalTools.IsSylowOf 2 (zOf W) (centralizer (W : Set (Sec H₀ H₁))) ∧
          oddPart (AutOrd ⊤ W) ∣ 9

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
