module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W0
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2Defs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Model

@[expose] def innGrp (X : Type) [Group X] : Subgroup (MulAut X) :=
  (MulAut.conj : X →* MulAut X).range

@[expose] def quatInvolution {X : Type} [Group X] {Q : Subgroup X} (r : ℕ)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) : X :=
  ((e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : X)

@[expose] def LieLinkSectionR (r : ℕ) {X : Type} [Group X] (Φ : Set (Subgroup X)) : Prop :=
  TypeRFam r Φ ∧ classicalInvolutionOddCore X = ⊥ ∧ omegaGen Φ = ⊤ ∧
    ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L'

structure Z2BigLinkModel (r : ℕ) (X : Type) [Group X] [Finite X] (p f : ℕ) : Prop where
  simple : IsSimpleGroup ↥(genFittingFStar X)
  index : (genFittingFStar X).index ≤ 2
  prime : p.Prime
  odd : p ≠ 2
  even : Even f
  model : LieModel (FStarQuot X) .PSL 2 p f
  arith : p ^ f % 2 ^ (r + 1) = 2 ^ r + 1

@[expose] def Z2BigModelArith (r : ℕ) : Prop :=
  4 ≤ r → ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), LieLinkSectionR r Φ →
    IsSimpleGroup ↥(genFittingFStar X) → (genFittingFStar X).index ≤ 2 →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f → LieModel (FStarQuot X) .PSL 2 p f →
      p ^ f % 2 ^ (r + 1) = 2 ^ r + 1

@[expose] def Z2BigModelPiCyc (r : ℕ) : Prop :=
  4 ≤ r → ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), Z2BigLinkModel r X p f →
    ∀ (Q : Subgroup X) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (H : Subgroup (MulAut X)),
      IsPGroup 2 ↥H → (∀ β ∈ H, ∀ x ∈ Q, β x ∈ Q) →
        ∀ g ∈ H, 2 ^ padicValNat 2 f < orderOf g →
          g ^ (orderOf g / 2) = MulAut.conj (quatInvolution r e)

@[expose] def Z2BigModelPiQuat (r : ℕ) : Prop :=
  4 ≤ r → ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), Z2BigLinkModel r X p f →
    ∀ (Q : Subgroup X) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (H : Subgroup (MulAut X)),
      IsPGroup 2 ↥H → (∀ β ∈ H, ∀ x ∈ Q, β x ∈ Q) →
        ∀ (m : ℕ), 1 ≤ m → ∀ B : Subgroup (MulAut X), B ≤ H →
          ∀ eB : ↥B ≃* QuaternionGroup (2 ^ m),
            ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : MulAut X) =
              MulAut.conj (quatInvolution r e)

@[expose] def Z2BigModelPi4 (r : ℕ) : Prop :=
  4 ≤ r → ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), Z2BigLinkModel r X p f →
    ∀ (Q : Subgroup X) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (H : Subgroup (MulAut X)),
      IsPGroup 2 ↥H → (∀ β ∈ H, ∀ x ∈ Q, β x ∈ Q) →
        ∀ g ∈ H, ∀ K : ℕ, 2 ≤ K → orderOf g = 2 ^ K →
          g ^ 2 ^ (K - 1) = MulAut.conj (quatInvolution r e) ∨ g ^ 2 ^ (K - 1) ∉ innGrp X

@[expose] def Z2BigModelCent (r : ℕ) : Prop :=
  4 ≤ r → ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), Z2BigLinkModel r X p f →
    ∀ (Q : Subgroup X) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))),
      (∀ x : X, (∀ y ∈ Q, x * y = y * x) → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        x = 1 ∨ x = quatInvolution r e) ∧
        ∀ H : Subgroup (MulAut X), IsPGroup 2 ↥H → (∀ β ∈ H, ∀ x ∈ Q, β x = x) →
          IsCyclic ↥H ∧ Nat.card ↥H ∣ 4 ∧
            ∀ β ∈ H, β * β = 1 → β ≠ 1 → β = MulAut.conj (quatInvolution r e)

end Model

section Defs

variable {Y : Type} [Group Y]

@[expose] def NoA1All (R : Subgroup Y) (t : Y) (J : Subgroup Y) (u : Y) : Prop :=
  ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) → R₁ ≤ Subgroup.centralizer ({u} : Set Y) →
    IsSylow2In T₁ J → T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) →
      NoA1 t u R₁ T₁

@[expose] def InvOutsideA (P : Subgroup Y) (t u : Y) : Prop :=
  ∃ b ∈ P, b ∉ edgeCent P t u ∧ b * b = 1

end Defs

section Cit3


structure Z2SetR (r n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y) : Prop where
  large : TightLargeHypR r n Y R S t
  conn : DConnected (CoreAssembly.conjClass (tightCore R))
  noTri : ¬ TriNbrAll R t
  z2 : LinkZ2 R t
  simple : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t))
  index : (genFittingFStar ↥(linkGrp R t)).index ≤ 2
  model : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
    LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f
  hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  hu : IsUniqueInvolution J u
  hR₀ : IsSylow2In R₀ (tightCore R)
  hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y)
  hT₀ : IsSylow2In T₀ J
  hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)
  noA1 : NoA1 t u R₀ T₀
  hR₀P : R₀ ≤ (P : Subgroup Y)
  hT₀P : T₀ ≤ (P : Subgroup Y)

@[expose] def Z2BigAdapted (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
        IsUniqueInvolution J u →
        ∃ R₀ T₀ : Subgroup Y, IsSylow2In R₀ (tightCore R) ∧
          R₀ ≤ Subgroup.centralizer ({u} : Set Y) ∧ IsSylow2In T₀ J ∧
          T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) ∧
          ∃ P : Sylow 2 Y, R₀ ≤ (P : Subgroup Y) ∧ T₀ ≤ (P : Subgroup Y)

@[expose] def Z2BigC264One (r n : ℕ) : Prop :=
  4 ≤ r → NoQ16E4 → Thm4RBelow r n →
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
      (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y), Z2SetR r n R S t J u R₀ T₀ P →
        C264One (CoreAssembly.conjClass (tightCore R)) t u

@[expose] def Z2BigProp7a (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
      InvOutsideA (P : Subgroup Y) t u → False

@[expose] def Z2BigProp6a4 (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
      NoA1All R t J u → ¬ InvOutsideA (P : Subgroup Y) t u → False

@[expose] def Z2BigStar (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P →
      ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ y : Y, IsUniqueInvolution L y →
        2 < Nat.card ↥(L ⊓ (P : Subgroup Y)) → y = t ∨ y = u

@[expose] def Z2BigHweak (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
      ∀ y ∈ R₀, y ≠ 1 → ∀ g : Y, g⁻¹ * y * g ∈ (P : Subgroup Y) →
        g⁻¹ * y * g ∈ edgeCent (P : Subgroup Y) t u

@[expose] def Z2BigNotConjTU (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P →
      ∀ b ∈ (P : Subgroup Y), b ∉ edgeCent (P : Subgroup Y) t u → b * b = 1 →
        ∀ g : Y, g * b * g⁻¹ ≠ t * u

@[expose] def Z2BigSplit (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → NoA1All R t J u →
      ∀ x ∈ edgeCent (P : Subgroup Y) t u, InnerModOdd (linkLayer R t) x →
        ∃ s ∈ edgeCent (P : Subgroup Y) t u, ActsLike (linkLayer R t) s x ∧
          ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) s

@[expose] def Z2BigChoiceB (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → NoA1All R t J u → ¬ InvOutsideA (P : Subgroup Y) t u →
      ∃ b ∈ (P : Subgroup Y), b ∉ edgeCent (P : Subgroup Y) t u ∧
        t * u ∈ Subgroup.zpowers b

@[expose] def Z2BigT1 (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
      NoA1All R t J u → ¬ InvOutsideA (P : Subgroup Y) t u →
        ∀ b ∈ (P : Subgroup Y), b ∉ edgeCent (P : Subgroup Y) t u →
          t * u ∈ Subgroup.zpowers b → ∀ g : Y, g⁻¹ * b * g ∉ edgeCent (P : Subgroup Y) t u

@[expose] def Z2BigT2 (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
      NoA1All R t J u → ¬ InvOutsideA (P : Subgroup Y) t u →
        ∀ b ∈ (P : Subgroup Y), b ∉ edgeCent (P : Subgroup Y) t u →
          t * u ∈ Subgroup.zpowers b → ∀ (g : Y) (k : ℕ), g⁻¹ * b ^ (2 * k) * g ∈ (P : Subgroup Y) →
            g⁻¹ * b ^ (2 * k) * g ∈ edgeCent (P : Subgroup Y) t u

@[expose] def Z2BigXPlusA (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
    Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
      NoA1All R t J u → ¬ InvOutsideA (P : Subgroup Y) t u →
        ∀ x ∈ edgeCent (P : Subgroup Y) t u, x * x = 1 →
          (¬ InnerModOdd (linkLayer R t) x ∨
            ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x) →
          ∀ g : Y, g * x * g⁻¹ ≠ t * u

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
