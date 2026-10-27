module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Prop4_1a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      ∀ r : ℕ, r.Prime → r ≠ 2 →
        X ≤ centralizer ((pCore r (Sec H₀ H₁) : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁))

@[expose] def Prop4_1b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      X ⊓ centralizer ((pCore 2 (Sec H₀ H₁) ⊔ layer (Sec H₀ H₁) : Subgroup (Sec H₀ H₁)) :
        Set (Sec H₀ H₁)) = ⊥

@[expose] def Prop4_1c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      ∀ W : Subgroup (Sec H₀ H₁), IsPGroup 2 ↥W → X ≤ normalizer (W : Set (Sec H₀ H₁)) →
        zSec z H₀ hz H₁ ∈ normalizer (W : Set (Sec H₀ H₁)) → ⁅W, X⁆ ≠ ⊥ →
        X ≤ centralizer ((zOf ⁅W, X⁆ : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁)) ∧
        (centralizer (W : Set (Sec H₀ H₁))).relIndex X = 3 ∧
        (((k = Kind.mcl ∨ k = Kind.ly) ∧ IsL34Two ↥⁅W, X⁆ ∧
            CFSG.ABGLocalTools.IsSylowOf 2 (zOf ⁅W, X⁆) (centralizer ((⁅W, X⁆ : Subgroup (Sec H₀ H₁)) :
              Set (Sec H₀ H₁))) ∧ oddPart (AutOrd ⊤ ⁅W, X⁆) ∣ 9) ∨
          (Nonempty (↥⁅W, X⁆ ≃* QuaternionGroup 2) ∧
            (∃ (s : G) (hs : s ∈ H₀), IsCentralInvolution s ∧
              (QuotientGroup.mk ⟨s, hs⟩ : Sec H₀ H₁) ∈ zOf ⁅W, X⁆) ∧
            NormIso ⁅W, X⁆ (Equiv.Perm (Fin 4))))

@[expose] def Prop4_1 : Prop := Prop4_1a ∧ Prop4_1b ∧ Prop4_1c

section Concl

variable {A : Type} [Group A] [Finite A]

@[expose] def C43a (X : Subgroup A) : Prop :=
  ncl X = ⁅pCore 2 A, X⁆ ⊔ X ∧ Nonempty (↥⁅pCore 2 A, X⁆ ≃* QuaternionGroup 2) ∧
    HasSL2Model ↥(ncl X) (fun q => q = 3)

@[expose] def C43b (p : ℕ) (X : Subgroup A) : Prop :=
  ∃ n : ℕ, 3 < p ^ n ∧ HasSL2Model ↥(ncl X) (fun q => q = p ^ n) ∧
    CFSG.ABGLocalTools.IsSylowOf p X (ncl X)

@[expose] def C43c (z : A) (p : ℕ) (X : Subgroup A) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ LieModel (↥(ncl X) ⧸ center ↥(ncl X)) .PSL 3 p n ∧ X ⊔ zpowers z ≤ ncl X ∧
    IsMaxParabolicP p (ncl X) (X ⊔ ncl X ⊓ centralizer ({z} : Set A)) ∧
    X = Op p (X ⊔ ncl X ⊓ centralizer ({z} : Set A)) ∧ IsElementaryAbelian p ↥X ∧
    Nat.card ↥X = p ^ (2 * n)

@[expose] def C43d (k : Kind) (z : A) (X : Subgroup A) : Prop :=
  (k = Kind.mcl ∨ k = Kind.ly) ∧ Nat.card ↥X = 3 ∧
    ((IsPGL3Four ↥(ncl X) ∧ ncl X ⊓ centralizer ({z} : Set A) = ⁅ncl X, ncl X⁆ ⊓ centralizer (X : Set A) ∧
        IVK.IsL2 ↥(ncl X ⊓ centralizer ({z} : Set A)) (fun q => q = 4) ∧
        (ncl X ⊔ zpowers z) ⊓ centralizer ((ncl X ⊓ centralizer ({z} : Set A) : Subgroup A) : Set A) =
          X ⊔ zpowers z) ∨
      (ncl X = ⁅pCore 2 A, X⁆ ⊔ X ∧ IsL34Two ↥⁅pCore 2 A, X⁆))

@[expose] def C43e (X : Subgroup A) : Prop := HasSL2Model ↥(ncl X) (fun q => q = 5) ∧ Nat.card ↥X = 3

@[expose] def Concl43 (k : Kind) (z : A) (p : ℕ) (X : Subgroup A) : Prop :=
  C43a X ∨ C43b p X ∨ C43c z p X ∨ C43d k z X ∨ C43e X

@[expose] def Hyp42 (z : A) (X : Subgroup A) : Prop :=
  layer A ⊔ X ⊔ zpowers z = ⊤ ∧ IsQuasisimple ↥(layer A) ∧ center ↥(layer A) = pCore 2 ↥(layer A) ∧
    ¬ ⁅layer A, X⁆ ≤ (center ↥(layer A)).map (layer A).subtype

@[expose] def Concl42 (k : Kind) (z : A) (p : ℕ) (X : Subgroup A) : Prop :=
  (HasSL2Model ↥(layer A) (fun q => q = 5) ∧ Nat.card ↥X = 3 ∧ p = 3 ∧ X ≤ layer A ∧
    layer A ⊓ normalizer (X : Set A) ≤ X ⊔ layer A ⊓ centralizer ({z} : Set A)) ∨
  (∃ n : ℕ, 3 < p ^ n ∧ HasSL2Model ↥(layer A) (fun q => q = p ^ n) ∧
    CFSG.ABGLocalTools.IsSylowOf p X (layer A) ∧
    layer A ⊓ normalizer (X : Set A) ≤ X ⊔ layer A ⊓ centralizer ({z} : Set A)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ LieModel ↥(layer A) .PSL 3 p n ∧
    z ∈ layer A ⊔ centralizer ((layer A : Subgroup A) : Set A) ∧ IsElementaryAbelian p ↥X ∧
    Nat.card ↥X = p ^ (2 * n) ∧
    ∃ P : Subgroup A, IsMaxParabolicP p (layer A) P ∧ X = Op p P ∧
      P = X ⊔ layer A ⊓ centralizer ({z} : Set A)) ∨
  ((k = Kind.mcl ∨ k = Kind.ly) ∧ IsPGL3Four ↥(layer A ⊔ X) ∧ LieModel ↥(layer A) .PSL 3 2 2 ∧
    Nat.card ↥X = 3 ∧
    layer A ⊓ centralizer ({z} : Set A) = layer A ⊓ centralizer (X : Set A) ∧
    IVK.IsL2 ↥(layer A ⊓ centralizer ({z} : Set A)) (fun q => q = 4) ∧
    (layer A ⊔ X ⊔ zpowers z) ⊓ centralizer ((layer A ⊓ centralizer ({z} : Set A) : Subgroup A) : Set A) =
      X ⊔ zpowers z)

end Concl

@[expose] def Prop4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X → Hyp42 (zSec z H₀ hz H₁) X →
      Concl42 k (zSec z H₀ hz H₁) p X

@[expose] def Prop4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      Concl43 k (zSec z H₀ hz H₁) p X

@[expose] def Lemma4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      ¬ Concl43 k (zSec z H₀ hz H₁) p X → Em (ncl X) = ⊥

@[expose] def Lemma4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      ¬ Concl43 k (zSec z H₀ hz H₁) p X → Em (ncl X) = ⊥ → ⁅pCore 2 (Sec H₀ H₁), X⁆ = ⊥

end CFSG.GH74.GLS.Stage2.Signalizer
