module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AutCfg

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section FTwoOpen

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

@[expose] def Prop85e : Prop :=
  Prop4_1a → Prop4_1b →
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X → Hyp42 (zSec z H₀ hz H₁) X →
      LieModel (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) .PSU 3 2 2 → False

@[expose] def Prop85g : Prop :=
  Prop4_1a → Prop4_1b →
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X → Hyp42 (zSec z H₀ hz H₁) X →
      LieModel (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) .PSL 3 2 2 →
      center ↥(layer (Sec H₀ H₁)) = ⊥ →
      IVK.IsL2 ↥(layer (Sec H₀ H₁) ⊓ centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁))) (fun q => q = 4) →
      k = Kind.mcl ∨ k = Kind.ly

@[expose] def MinIndexL34 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .PSL 3 2 2 → ∀ H : Subgroup Y, H ≠ ⊤ → 11 < H.index

@[expose] def innSub (Y : Type) [Group Y] : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range

@[expose] def TwoAutVac : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (LieModel Y .PSL 2 2 3 ∨ LieModel Y .PSL 2 2 4 ∨ LieModel Y .twistedB2 0 2 3) →
    ∀ (α : MulAut Y) (p : ℕ) (X : Subgroup (MulAut Y)), ¬ AutCfg Y α p X

@[expose] def L34Aut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .PSL 3 2 2 →
    ∀ (α : MulAut Y) (p : ℕ) (X : Subgroup (MulAut Y)), AutCfg Y α p X →
      Nat.card ↥X = 3 ∧ X ⊓ innSub Y = ⊥ ∧ α ∉ innSub Y ⊔ X ∧ IsPGL3Four ↥(innSub Y ⊔ X) ∧
      innSub Y ⊓ centralizer ({α} : Set (MulAut Y)) = innSub Y ⊓ centralizer (X : Set (MulAut Y)) ∧
      IVK.IsL2 ↥(innSub Y ⊓ centralizer ({α} : Set (MulAut Y))) (fun q => q = 4) ∧
      (innSub Y ⊔ X ⊔ zpowers α) ⊓ centralizer ((innSub Y ⊓ centralizer ({α} : Set (MulAut Y)) : Subgroup (MulAut Y)) : Set (MulAut Y)) =
        X ⊔ zpowers α

end FTwoOpen


section G2D4

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def G2ThreeMax : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .G2 0 3 1 → ∀ α : MulAut Y, α * α = 1 → α ≠ 1 →
    IsCoatom (α.toMonoidHom.eqLocus (MonoidHom.id Y))

@[expose] def G2ThreeMult : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → IsPGroup 2 ↥(Subgroup.center L) →
    LieModel (L ⧸ Subgroup.center L) .G2 0 3 1 → Subgroup.center L = ⊥

@[expose] def D4Mult : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → IsPGroup 2 ↥(Subgroup.center L) →
    ∀ p f : ℕ, p.Prime → 1 ≤ f → p ≠ 2 → LieModel (L ⧸ Subgroup.center L) .trialityD4 0 p f →
      Subgroup.center L = ⊥

end G2D4


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
