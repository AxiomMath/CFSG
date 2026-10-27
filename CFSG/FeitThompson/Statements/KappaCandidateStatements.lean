module

public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.TheWitnessedPConfiguration
public import CFSG.FeitThompson.Definitions.LocalTypeI
public import CFSG.FeitThompson.Definitions.CanonicalCentralizerSignalizerFrom
public import CFSG.FeitThompson.Definitions.DadeSupportExtension
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {G : Type*} [Group G]

noncomputable local instance subgroupFintype {H : Type*} [Group H] [Fintype H] (X : Subgroup H) :
    Fintype ↥X := Fintype.ofFinite _

namespace Prep03

structure IsAmbient (G : Type*) [Group G] [Fintype G] : Prop where
  odd_natCard : Odd (Nat.card G)
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  forall_isSolvable : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H

@[expose]
def conjSet (A : Set G) (g : G) : Set G := (fun x => g⁻¹ * x * g) '' A

@[expose]
def sat (A : Set G) : Set G := ⋃ g : G, conjSet A g

@[expose]
def conjSub (Y : Subgroup G) (g : G) : Subgroup G := Y.map (MulAut.conj g⁻¹ : G →* G)

@[expose]
def cent (X : Subgroup G) (A : Set G) : Subgroup G := X ⊓ Subgroup.centralizer A

@[expose]
def cent1 (X : Subgroup G) (a : G) : Subgroup G := X ⊓ Subgroup.centralizer {a}

@[expose]
def hallCoreIn (M : Subgroup G) : Subgroup G := (hallCore ↥M).map M.subtype

@[expose]
def fittingIn [Finite G] (M : Subgroup G) : Subgroup G := (fittingRaw ↥M).map M.subtype

@[expose]
noncomputable def piCoreIn [Finite G] (π : Set ℕ) (X : Subgroup G) : Subgroup G :=
  (piCore π ↥X).map X.subtype

@[expose]
def IsSylowOf (p : ℕ) (P X : Subgroup G) : Prop :=
  P ≤ X ∧ Nat.card ↥P = p ^ (Nat.card ↥X).factorization p

@[expose]
def IsSylowTop (p : ℕ) (P : Subgroup G) : Prop :=
  Nat.card ↥P = p ^ (Nat.card G).factorization p

@[expose]
def IsHallPiOf (π : Set ℕ) (Y X : Subgroup G) : Prop :=
  Y ≤ X ∧ (∀ r ∈ (Nat.card ↥Y).primeFactors, r ∈ π) ∧
    ∀ r ∈ (Y.relIndex X).primeFactors, r ∉ π

@[expose]
def IsHallOf (Y X : Subgroup G) : Prop :=
  Y ≤ X ∧ (Nat.card ↥Y).Coprime (Y.relIndex X)

@[expose]
def IsSemidirect (X Y Z : Subgroup G) : Prop :=
  Y ≤ X ∧ Z ≤ X ∧ X ≤ Subgroup.normalizer (Y : Set G) ∧ Y ⊔ Z = X ∧ Y ⊓ Z = ⊥

@[expose]
def IsDirect (X Y Z : Subgroup G) : Prop :=
  Y ≤ X ∧ Z ≤ X ∧ Y ⊔ Z = X ∧ Y ⊓ Z = ⊥ ∧ ⁅Y, Z⁆ = ⊥

@[expose]
def IsPlane (p : ℕ) (A : Subgroup G) : Prop :=
  Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p)))

@[expose]
def maximalFamily (G : Type*) [Group G] : Set (Subgroup G) := {M | IsCoatom M}

@[expose]
noncomputable def kMult [Finite G] (a : G) : ℕ :=
  supportMultiplicity (maximalFamily G) sigmaCore a

@[expose]
noncomputable def sigR [Finite G] (a : G) : Subgroup G :=
  canonicalSignalizer (maximalFamily G) sigmaCore a

@[expose]
def sigmaCoreSupport (G : Type*) [Group G] [Finite G] : Set G :=
  coreFamilySupport (maximalFamily G) sigmaCore

@[expose]
noncomputable def sigmaDelta [Finite G] (T : Subgroup G) : Set G :=
  ⋃ a ∈ ((sigmaCore T : Set G) \ {1}), sat (({a} : Set G) * (sigR a : Set G))

@[expose]
noncomputable def hallDadeSupport [Finite G] (L : Subgroup G) : Set G :=
  totalDadeSupport ((hallCoreIn L : Set G) \ {1}) sigR

@[expose]
noncomputable def tauHall [Finite G] (L : Subgroup G) (f : ↥L → ℂ) : G → ℂ :=
  dadeSupportExtension ((hallCoreIn L : Set G) \ {1}) sigR (extendByZero L f)

@[expose]
noncomputable def sumSqOn [Fintype G] (A : Set G) (f : G → ℂ) : ℝ :=
  ∑ x : G, Set.indicator A (fun y => ‖f y‖ ^ 2) x

@[expose]
def sharp (X : Subgroup G) : Set G := (X : Set G) \ ({1} : Set G)

@[expose]
noncomputable def indG [Fintype G] (S : Subgroup G) (f : ↥S → ℂ) : G → ℂ := indClassFun S f

@[expose]
def resSub {X : Subgroup G} (W : Subgroup G) (f : ↥X → ℂ) : ↥(W.subgroupOf X) → ℂ :=
  fun y => f (y : ↥X)

@[expose]
def IsSignedIrr (H : Type*) [Group H] (φ : H → ℂ) : Prop :=
  ∃ χ ∈ Irr H, φ = χ ∨ φ = -χ

@[expose]
def IsNonreal {α : Type*} (φ : α → ℂ) : Prop := φ ≠ fun x => (starRingEnd ℂ) (φ x)

@[expose]
def IsRealValued {α : Type*} (φ : α → ℂ) : Prop := ∀ x, (starRingEnd ℂ) (φ x) = φ x

@[expose]
noncomputable def hallIndFamily [Fintype G] (L : Subgroup G) : Set (↥L → ℂ) :=
  {f | ∃ θ ∈ Irr ↥(hallCore ↥L), θ ≠ 1 ∧ indClassFun (hallCore ↥L) θ = f}

@[expose]
noncomputable def detectInd [Fintype G] (M Y H : Subgroup G) : Set (↥M → ℂ) :=
  {f | ∃ θ ∈ Irr ↥(Y.subgroupOf M),
    (∃ x : ↥(Y.subgroupOf M), ((x : ↥M) : G) ∈ H ∧ θ x ≠ θ 1) ∧
      indClassFun (Y.subgroupOf M) θ = f}

@[expose]
def IsAdditiveIsometryOn [Fintype G] {L : Subgroup G} (S : Set (↥L → ℂ))
    (ν : (↥L → ℂ) → (G → ℂ)) : Prop :=
  (∀ f ∈ Submodule.span ℤ S, ∀ g ∈ Submodule.span ℤ S, ν (f + g) = ν f + ν g) ∧
  (∀ f ∈ Submodule.span ℤ S, ν f ∈ virtualChars G) ∧
  (∀ f ∈ Submodule.span ℤ S, ∀ g ∈ Submodule.span ℤ S, cfInner (ν f) (ν g) = cfInner f g)

@[expose]
def IsCoherentOn [Fintype G] {L : Subgroup G} (S : Set (↥L → ℂ))
    (τ ν : (↥L → ℂ) → (G → ℂ)) : Prop :=
  IsAdditiveIsometryOn S ν ∧ (∀ f ∈ Submodule.span ℤ S, f 1 = 0 → ν f = τ f)

@[expose]
def cyclicTIsetConjIn (W₁ W₂ S : Subgroup G) : Set G :=
  ⋃ s ∈ (S : Set G), conjSet (cyclicTIset W₁ W₂) s

@[expose]
def mixedSupport (S W₁ W₂ : Subgroup G) : Set G :=
  ((hallCoreIn S : Set G) \ {1}) ∪ cyclicTIsetConjIn W₁ W₂ S

@[expose]
def kappaFamily (M K : Subgroup G) : Set (Subgroup G) :=
  {M} ∪ {T | IsCoatom T ∧ ∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
    Subgroup.normalizer (X : Set G) ≤ T}

@[expose]
noncomputable def kappaA [Finite G] (KT : Subgroup G → Subgroup G) (T : Subgroup G) :
    Subgroup G := cent (sigmaCore T) (KT T : Set G)

@[expose]
noncomputable def mixedTorusSet [Finite G] (Z : Subgroup G) (I : Set (Subgroup G))
    (KT : Subgroup G → Subgroup G) : Set G :=
  ((Z : Set G) \ {1}) \ ⋃ V ∈ I, ((kappaA KT V : Set G) \ {1})

structure IsKappaSetup (G : Type*) [Group G] [Fintype G] (M K A Z : Subgroup G) : Prop where
  ambient : IsAmbient G
  isCoatom : IsCoatom M
  kappa_nonempty : (kappaPrimes M).Nonempty
  isHall_K : IsHallPiOf (kappaPrimes M) K M
  A_eq : A = cent (sigmaCore M) (K : Set G)
  Z_eq : Z = K ⊔ A

structure IsKappaFamilySetup (G : Type*) [Group G] [Fintype G] (M K A Z : Subgroup G)
    (I : Set (Subgroup G)) (KT : Subgroup G → Subgroup G) : Prop where
  base : IsKappaSetup G M K A Z
  I_eq : I = kappaFamily M K
  KT_self : KT M = K
  KT_hall : ∀ T ∈ I, T ≠ M → IsHallPiOf (kappaPrimes T) (KT T) T ∧ A ≤ KT T

structure IsSigmaComplementSetup (G : Type*) [Group G] [Fintype G] (M E K U : Subgroup G) :
    Prop where
  ambient : IsAmbient G
  isCoatom : IsCoatom M
  decomp : IsSemidirect M (sigmaCore M) E
  le_E_K : K ≤ E
  isHall_K : IsHallPiOf (kappaPrimes M) K M
  le_E_U : U ≤ E
  decomp_E : IsSemidirect E U K

structure IsPlaneSetup (G : Type*) [Group G] [Fintype G] (p : ℕ) (M A E : Subgroup G) :
    Prop where
  ambient : IsAmbient G
  isCoatom : IsCoatom M
  prime : p.Prime
  notMem_sigma : p ∉ sigmaPrimes M
  le_M_A : A ≤ M
  isPlane : IsPlane p A
  decomp : IsSemidirect M (sigmaCore M) E
  le_E_A : A ≤ E

structure IsPConfigSetup (G : Type*) [Group G] [Fintype G] (M U W₁ W₂ : Subgroup G) : Prop where
  ambient : IsAmbient G
  isCoatom : IsCoatom M
  config : IsWitnessedPConfiguration M U W₁ W₂

structure IsThreeHallSetup (G : Type*) [Group G] [Fintype G] (M E E₁ E₂ E₃ : Subgroup G) :
    Prop where
  ambient : IsAmbient G
  isCoatom : IsCoatom M
  decomp : IsSemidirect M (sigmaCore M) E
  isHall_E₁ : IsHallPiOf (tau1Primes M) E₁ E
  isHall_E₂ : IsHallPiOf (tauTwoPrimes M) E₂ E
  isHall_E₃ : IsHallPiOf (tau3Primes M) E₃ E
  decomp_outer : IsSemidirect E E₃ (E₂ ⊔ E₁)
  decomp_inner : IsSemidirect (E₂ ⊔ E₁) E₂ E₁
  isCyclic_E₁ : IsCyclic ↥E₁
  isCyclic_E₃ : IsCyclic ↥E₃
  le_derived_E₃ : E₃ ≤ ⁅E, E⁆
  normal_E₂E₃ : E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G)
  cent_E₃ : cent E₃ (E : Set G) = ⊥

structure IsTIExtension [Fintype G] (W₁ W₂ : Subgroup G) (X : Subgroup G)
    (Φ : (↥(W₁ ⊔ W₂) → ℂ) → (↥X → ℂ)) : Prop where
  map_add : ∀ f g, Φ (f + g) = Φ f + Φ g
  map_smul : ∀ (c : ℂ) f, Φ (c • f) = c • Φ f
  maps_classFun : ∀ f ∈ classFun ↥(W₁ ⊔ W₂), Φ f ∈ classFun ↥X
  inner_eq : ∀ f g, cfInner (Φ f) (Φ g) = cfInner f g
  maps_virtualChars : ∀ f ∈ virtualChars ↥(W₁ ⊔ W₂), Φ f ∈ virtualChars ↥X
  map_one : Φ 1 = 1
  eq_ind : ∀ f : ↥(W₁ ⊔ W₂) → ℂ,
    (∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ → f z = 0) →
      Φ f = indClassFun ((W₁ ⊔ W₂).subgroupOf X)
        (fun y : ↥((W₁ ⊔ W₂).subgroupOf X) => f ⟨((y : ↥X) : G), y.2⟩)

end Prep03

namespace Statements

open Prep03

@[expose]
def FCH_type_I_P_packet_separation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ S U W₁ W₂ : Subgroup G, IsPConfigSetup G S U W₁ W₂ →
    ∀ L : Subgroup G, IsCoatom L → IsTypeI L →
      Nat.Coprime (Nat.card ↥(hallCoreIn L))
          (Nat.card ↥W₂ * Nat.card ↥W₁) ∧
        hallDadeSupport L ∩
            (sat (hallCoreIn S : Set G) ∪ sat ((W₁ ⊔ W₂ : Subgroup G) : Set G)) = ∅ ∧
        ∀ f : ↥L → ℂ,
          (∀ x : ↥L, (x : G) ∉ (hallCoreIn L : Set G) \ {1} → f x = 0) →
            ∀ x ∈ sat (hallCoreIn S : Set G) ∪ sat ((W₁ ⊔ W₂ : Subgroup G) : Set G),
              tauHall L f x = 0

@[expose]
def FCH_type_I_frobenius_coherent_family : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ L : Subgroup G, IsCoatom L → IsTypeI L →
      {a : G | a ∈ L ∧ a ≠ 1 ∧ cent1 (hallCoreIn L) a ≠ ⊥} = (hallCoreIn L : Set G) \ {1} ∧
      sigmaCore L = hallCoreIn L ∧
      1 < Nat.card ↥(hallCoreIn L) ∧
      1 < (hallCoreIn L).relIndex L ∧
      2 * (hallCoreIn L).relIndex L ≤ Nat.card ↥(hallCoreIn L) - 1 ∧
      IsDadeData L ((hallCoreIn L : Set G) \ {1}) sigR ∧
      (∀ a ∈ (hallCoreIn L : Set G) \ {1}, ∀ b ∈ (hallCoreIn L : Set G) \ {1},
        IsConj a b → ∃ x ∈ L, x * a * x⁻¹ = b) ∧
      (∀ a ∈ (hallCoreIn L : Set G) \ {1},
        ((sigR a).subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal ∧
        (sigR a) ⊔ cent1 L a = Subgroup.centralizer ({a} : Set G) ∧
        (sigR a) ⊓ cent1 L a = ⊥) ∧
      (∀ a ∈ (hallCoreIn L : Set G) \ {1}, ∀ b ∈ (hallCoreIn L : Set G) \ {1},
        Nat.Coprime (Nat.card ↥(sigR a)) (Nat.card ↥(cent1 L b))) ∧
      hallIndFamily L ⊆ Irr ↥L ∧
      (∀ f ∈ hallIndFamily L, (fun x => (starRingEnd ℂ) (f x)) ∈ hallIndFamily L) ∧
      2 ≤ (hallIndFamily L).ncard ∧
      (∃ ν : (↥L → ℂ) → (G → ℂ), IsCoherentOn (hallIndFamily L) (fun f => tauHall L f) ν) ∧
      ∃ φ ∈ hallIndFamily L, φ 1 = ((hallCoreIn L).relIndex L : ℂ)

@[expose]
def FCH_type_p_action_kernel_ratio : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M U W₁ W₂ : Subgroup G, IsPConfigSetup G M U W₁ W₂ →
    ∀ p q u c : ℕ,
      p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
      u = (cent U (hallCoreIn M : Set G)).relIndex U →
      c = Nat.card ↥(cent U (hallCoreIn M : Set G)) →
    ∀ m : ℚ,
      m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
            + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) →
    (∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1) →
    m * (p : ℚ) ^ ((q : ℕ) - 1) / (q : ℚ) < (u : ℚ) / (c : ℚ)

@[expose]
def FCH_type_p_actual_bridge_remainder : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ S U W₁ W₂ : Subgroup G, IsPConfigSetup G S U W₁ W₂ →
    ∀ u p q : ℕ, u = Nat.card ↥U → p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
    ∀ (I J : Type) (_ : Fintype I) (_ : Fintype J) (i0 : I) (j0' : J)
      (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ),
      (∀ i, α i ∈ Irr ↥W₁) → (∀ j, β j ∈ Irr ↥W₂) →
      Function.Injective α → Function.Injective β →
      (∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) → (∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ) →
      α i0 = 1 → β j0' = 1 →
    ∀ (w : I → J → ↥(W₁ ⊔ W₂) → ℂ),
      (∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
        w i j z = α i x * β j y) →
    ∀ (σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)),
      IsTIExtension W₁ W₂ S σ → IsTIExtension W₁ W₂ (⊤ : Subgroup G)
        (fun f x => ω f (x : G)) →
    ∀ (δ : J → ℂ) (μ : J → ↥S → ℂ) (η : I → J → G → ℂ),
      (∀ j, δ j = 1 ∨ δ j = -1) →
      (∀ j, μ j = δ j • σ (w i0 j)) → (∀ j, μ j ∈ Irr ↥S) →
      (∀ i j, η i j = ω (w i j)) →
    ∀ γ b : J → ↥S → ℂ,
      (∀ j, γ j = indClassFun (((hallCoreIn S) ⊔ W₁).subgroupOf S)
        (fun _ => (1 : ℂ))) →
      (∀ j, b j = γ j - μ j) →
      (∀ j, j ≠ j0' → δ j = 1 ∧
        (∃ χ : ↥(⁅S, S⁆ : Subgroup G) → ℂ, χ ∈ Irr ↥(⁅S, S⁆ : Subgroup G) ∧
          (∀ y : ↥(⁅S, S⁆ : Subgroup G), χ y = μ j ⟨(y : G),
            (Subgroup.commutator_le_self S) y.2⟩) ∧
          χ 1 = (u : ℂ) ∧
          ∀ y : ↥(⁅S, S⁆ : Subgroup G), (y : G) ∉ hallCoreIn S → χ y = 0) ∧
        b j ∈ virtualChars ↥S ∧
        (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → b j x = 0) ∧
        cfInner (b j) (b j) = (((u : ℚ) - 1) / (q : ℚ) + 2 : ℚ)) ∧
      (q ∣ u - 1) ∧
      ∀ j₀ : J, j₀ ≠ j0' →
        ∀ Γ : G → ℂ,
          Γ = indG S (b j₀) - 1 + η i0 j₀ →
          Γ ∈ virtualChars G ∧ IsRealValued Γ ∧ cfInner Γ (1 : G → ℂ) = 0 ∧
          ∀ j : J, j ≠ j0' →
            (∀ x : G, indG S (b j) x = 1 - η i0 j x + Γ x) ∧
            cfInner (indG S (b j)) (indG S (b j)) = (((u : ℚ) - 1) / (q : ℚ) + 2 : ℚ) ∧
            (∀ x : G, x ∉ sat (hallCoreIn S : Set G) ∪ sat ((W₁ ⊔ W₂ : Subgroup G) : Set G) →
              indG S (b j) x = 0)

@[expose]
def FCH_type_p_complementary_fitting_norm : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M U W₁ W₂ : Subgroup G, IsPConfigSetup G M U W₁ W₂ →
    ∀ u : ℕ, u = (cent U (hallCoreIn M : Set G)).relIndex U →
    ∀ (I J : Type) (_ : Fintype I) (_ : Fintype J) (i0 : I) (j0 : J)
      (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ),
      (∀ i, α i ∈ Irr ↥W₁) → (∀ j, β j ∈ Irr ↥W₂) →
      Function.Injective α → Function.Injective β →
      (∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) → (∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ) →
      α i0 = 1 → β j0 = 1 →
    ∀ w : I → J → ↥(W₁ ⊔ W₂) → ℂ,
      (∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
        w i j z = α i x * β j y) →
    ∀ (σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)),
      IsTIExtension W₁ W₂ M σ →
      IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)) →
    ∀ (δ : J → ℂ) (μ0 : J → ↥M → ℂ) (ell : I → ↥M → ℂ) (μ : I → J → ↥M → ℂ)
      (Mrow : J → ↥M → ℂ) (η : I → J → G → ℂ),
      (∀ j, δ j = 1 ∨ δ j = -1) →
      (∀ j, μ0 j = δ j • σ (w i0 j)) → (∀ j, μ0 j ∈ Irr ↥M) →
      (∀ (i : I) (k : ↥(⁅M, M⁆ : Subgroup G)) (x : ↥W₁) (z : ↥M),
        (z : G) = (k : G) * (x : G) → ell i z = α i x) →
      (∀ i j, μ i j = ell i * μ0 j) →
      (∀ j, Mrow j = ∑ i : I, μ i j) →
      (∀ i j, η i j = ω (w i j)) →
    ∀ Sfam Tfam : Set (↥M → ℂ),
      Sfam = detectInd M (⁅M, M⁆ : Subgroup G) (hallCoreIn M) →
      Tfam = detectInd M (fittingIn M) (hallCoreIn M) →
    ∀ (Q : Subgroup G) (G0 : Set G),
      G0 = Set.univ \ (sat (fittingIn M : Set G) ∪ sat (Q : Set G)) →
    ∀ ν : (↥M → ℂ) → (G → ℂ),
      IsAdditiveIsometryOn Sfam ν →
      Tfam ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ)) →
      (∀ f ∈ Tfam, f 1 = ((Nat.card ↥W₁ * u : ℕ) : ℂ)) →
      (∀ f ∈ Submodule.span ℤ Tfam, f 1 = 0 → ν f = fun x => indG M f x) →
    ∀ (j₁ j₂ : J) (ε : ℂ),
      j₁ ≠ j0 → j₂ ≠ j0 → (ε = 1 ∨ ε = -1) →
      Mrow j₁ ∈ Tfam →
      ν (Mrow j₁) = (fun x => ε * ∑ i : I, η i j₂ x) →
    ∀ lam ∈ Tfam, ∀ iStar : I, iStar ≠ i0 →
      (G0.ncard : ℝ) ≤
        ∑ x : G, Set.indicator G0 (fun y => ‖ν lam y‖ ^ 2 + ‖η iStar j0 y‖ ^ 2) x

@[expose]
def FCH_type_p_core_mixed_ti : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ S U W₁ W₂ : Subgroup G, IsPConfigSetup G S U W₁ W₂ →
      (mixedSupport S W₁ W₂).Nonempty ∧
      (∀ s ∈ (S : Set G), conjSet (mixedSupport S W₁ W₂) s = mixedSupport S W₁ W₂) ∧
      mixedSupport S W₁ W₂ ⊆ (S : Set G) \ {1} ∧
      IsTIWithNormalizer (mixedSupport S W₁ W₂) S ∧
      (∀ a ∈ mixedSupport S W₁ W₂, Subgroup.centralizer ({a} : Set G) = cent1 S a) ∧
      (∀ f t : ↥S → ℂ, f ∈ classFun ↥S → t ∈ classFun ↥S →
        (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) →
        (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → t x = 0) →
        cfInner (indG S f)
          (indG S t) = cfInner f t) ∧
      (∀ f ∈ virtualChars ↥S,
        (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) →
        (indG S f) ∈ virtualChars G) ∧
      (∀ A0 : Set G, ∀ J : G → Subgroup G,
        mixedSupport S W₁ W₂ ⊆ A0 → A0 ⊆ (S : Set G) \ {1} →
        (∀ s ∈ (S : Set G), conjSet A0 s = A0) →
        IsDadeData S A0 J →
        ∀ f : ↥S → ℂ, f ∈ classFun ↥S →
          (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) →
          dadeSupportExtension A0 J (extendByZero S f)
            = fun x : G => indG S f x)

@[expose]
def FCH_type_p_no_fitting_induced_witness : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M U W₁ W₂ : Subgroup G, IsPConfigSetup G M U W₁ W₂ →
    ∀ p q u : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
      u = (cent U (hallCoreIn M : Set G)).relIndex U →
    (¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1) →
    p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧
      cent U (hallCoreIn M : Set G) = ⊥ ∧
      fittingIn M = hallCoreIn M ∧
      Nat.card ↥U = u ∧ u * (p - 1) = p ^ q - 1 ∧
      (∀ N : Subgroup G, N ≤ hallCoreIn M →
        (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → (∀ x ∈ N, x ^ p = 1) →
        (∀ g ∈ U, conjSub N g = N) → N = ⊥ ∨ N = hallCoreIn M) ∧
      ∃ (E : Type) (_ : Field E) (_ : Fintype E) (ι : ↥(hallCoreIn M) → E),
        Nat.card E = p ^ q ∧ Function.Bijective ι ∧
        (∀ x y : ↥(hallCoreIn M), ι (x * y) = ι x + ι y) ∧
        (∀ g ∈ U, ∃ a : E,
          a ^ (∑ k ∈ Finset.range q, p ^ k) = 1 ∧
          ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : g⁻¹ * h * g ∈ hallCoreIn M),
            ι ⟨g⁻¹ * h * g, hc⟩ = a * ι ⟨h, hh⟩) ∧
        (∀ a : E, a ^ (∑ k ∈ Finset.range q, p ^ k) = 1 →
          ∃ g ∈ U, ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : g⁻¹ * h * g ∈ hallCoreIn M),
            ι ⟨g⁻¹ * h * g, hc⟩ = a * ι ⟨h, hh⟩) ∧
        (∀ w ∈ W₁, ∃ φ : E ≃+* E,
          (∀ c : E, (∃ n : ℕ, c = (n : E)) → φ c = c) ∧
          ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : w⁻¹ * h * w ∈ hallCoreIn M),
            ι ⟨w⁻¹ * h * w, hc⟩ = φ (ι ⟨h, hh⟩)) ∧
        ∀ φ : E ≃+* E, (∀ c : E, (∃ n : ℕ, c = (n : E)) → φ c = c) →
          ∃ w ∈ W₁, ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : w⁻¹ * h * w ∈ hallCoreIn M),
            ι ⟨w⁻¹ * h * w, hc⟩ = φ (ι ⟨h, hh⟩)

@[expose]
def FCH_type_p_oriented_core_family : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M U W₁ W₂ : Subgroup G, IsPConfigSetup G M U W₁ W₂ →
    ∀ u : ℕ, u = (cent U (hallCoreIn M : Set G)).relIndex U →
    ∀ (I J : Type) (_ : Fintype I) (_ : Fintype J) (i0 : I) (j0' : J)
      (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ),
      (∀ i, α i ∈ Irr ↥W₁) → (∀ j, β j ∈ Irr ↥W₂) →
      Function.Injective α → Function.Injective β →
      (∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) → (∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ) →
      α i0 = 1 → β j0' = 1 →
    ∀ bar : J → J,
      (∀ j, β (bar j) = fun y => (starRingEnd ℂ) (β j y)) →
    ∀ w : I → J → ↥(W₁ ⊔ W₂) → ℂ,
      (∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
        w i j z = α i x * β j y) →
    ∀ (σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)),
      IsTIExtension W₁ W₂ M σ →
      IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)) →
    ∀ (δj : J → ℂ) (μ0 : J → ↥M → ℂ) (ell : I → ↥M → ℂ) (μ : I → J → ↥M → ℂ)
      (Mrow : J → ↥M → ℂ) (η : I → J → G → ℂ),
      (∀ j, δj j = 1 ∨ δj j = -1) →
      (∀ j, μ0 j = δj j • σ (w i0 j)) → (∀ j, μ0 j ∈ Irr ↥M) →
      (∀ (i : I) (k : ↥(⁅M, M⁆ : Subgroup G)) (x : ↥W₁) (z : ↥M),
        (z : G) = (k : G) * (x : G) → ell i z = α i x) →
      (∀ i j, μ i j = ell i * μ0 j) →
      (∀ j, Mrow j = ∑ i : I, μ i j) →
      (∀ i j, η i j = ω (w i j)) →
    ∀ Sfam Tfam : Set (↥M → ℂ),
      Sfam = detectInd M (⁅M, M⁆ : Subgroup G) (hallCoreIn M) →
      Tfam = detectInd M (fittingIn M) (hallCoreIn M) →
    (∃ (σ₀ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)) (ω₀ : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)),
      IsTIExtension W₁ W₂ M σ₀ ∧
      IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω₀ f (x : G))) ∧
    ∃ (ν : (↥M → ℂ) → (G → ℂ)) (δ : ℂ) (e : ℕ),
      (δ = 1 ∨ δ = -1) ∧ (e = 0 ∨ e = 1) ∧
      IsAdditiveIsometryOn Sfam ν ∧
      Tfam ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ)) ∧
      (∀ f ∈ Tfam, f 1 = ((Nat.card ↥W₁ * u : ℕ) : ℂ)) ∧
      (∀ f ∈ Submodule.span ℤ Tfam, f 1 = 0 →
        ν f = fun x => indG M f x) ∧
      (∀ j : J, j ≠ j0' → δj j = δ) ∧
      (∀ j : J, j ≠ j0' →
        ν (Mrow j) = fun x => (-1 : ℂ) ^ e * δ * ∑ i : I, η i (if e = 0 then j else bar j) x) ∧
      (e = 1 → Nat.card ↥W₂ = 3) ∧
      (∀ ξ ∈ Sfam ∩ Irr ↥M,
        IsSignedIrr G (ν ξ) ∧ IsNonreal (ν ξ) ∧
        ν (fun x => (starRingEnd ℂ) (ξ x)) = (fun x => (starRingEnd ℂ) (ν ξ x)) ∧
        (∀ i j, cfInner (ν ξ) (η i j) = 0) ∧
        (∀ x ∈ cyclicTIset W₁ W₂, ν ξ x = 0)) ∧
      (∀ i : I, i ≠ i0 → ∀ ζ ∈ Tfam, cfInner (ν ζ) (η i j0') = 0) ∧
      (∀ j₀ : J, j₀ ≠ j0' →
        Mrow (if e = 0 then j₀ else bar j₀) ∈ Tfam ∧
        cfInner (Mrow (if e = 0 then j₀ else bar j₀))
          (Mrow (if e = 0 then j₀ else bar j₀)) = (Nat.card ↥W₁ : ℂ) ∧
        cfInner (ν (Mrow (if e = 0 then j₀ else bar j₀))) (η i0 j₀) = (-1 : ℂ) ^ e * δ ∧
        ∀ ζ ∈ Tfam, ζ ≠ Mrow (if e = 0 then j₀ else bar j₀) →
          cfInner (ν ζ) (η i0 j₀) = 0)

@[expose]
def FCH_type_p_three_fitting_norm_bounds : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M U W₁ W₂ : Subgroup G, IsPConfigSetup G M U W₁ W₂ →
    ∀ u : ℕ, u = (cent U (hallCoreIn M : Set G)).relIndex U →
    ∀ (I J : Type) (_ : Fintype I) (_ : Fintype J) (i0 : I) (j0' : J)
      (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ),
      (∀ i, α i ∈ Irr ↥W₁) → (∀ j, β j ∈ Irr ↥W₂) →
      Function.Injective α → Function.Injective β →
      (∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) → (∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ) →
      α i0 = 1 → β j0' = 1 →
    ∀ bar : J → J,
      (∀ j, β (bar j) = fun y => (starRingEnd ℂ) (β j y)) →
    ∀ w : I → J → ↥(W₁ ⊔ W₂) → ℂ,
      (∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
        w i j z = α i x * β j y) →
    ∀ (σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)),
      IsTIExtension W₁ W₂ M σ →
      IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)) →
    ∀ (δj : J → ℂ) (μ0 : J → ↥M → ℂ) (ell : I → ↥M → ℂ) (μ : I → J → ↥M → ℂ)
      (Mrow : J → ↥M → ℂ) (η : I → J → G → ℂ),
      (∀ j, δj j = 1 ∨ δj j = -1) →
      (∀ j, μ0 j = δj j • σ (w i0 j)) → (∀ j, μ0 j ∈ Irr ↥M) →
      (∀ (i : I) (k : ↥(⁅M, M⁆ : Subgroup G)) (x : ↥W₁) (z : ↥M),
        (z : G) = (k : G) * (x : G) → ell i z = α i x) →
      (∀ i j, μ i j = ell i * μ0 j) →
      (∀ j, Mrow j = ∑ i : I, μ i j) →
      (∀ i j, η i j = ω (w i j)) →
    ∀ (Sfam Tfam : Set (↥M → ℂ)) (ν : (↥M → ℂ) → (G → ℂ)) (δ : ℂ) (e : ℕ),
      Sfam = detectInd M (⁅M, M⁆ : Subgroup G) (hallCoreIn M) →
      Tfam = detectInd M (fittingIn M) (hallCoreIn M) →
      (δ = 1 ∨ δ = -1) → (e = 0 ∨ e = 1) →
      IsAdditiveIsometryOn Sfam ν →
      Tfam ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ)) →
      (∀ f ∈ Tfam, f 1 = ((Nat.card ↥W₁ * u : ℕ) : ℂ)) →
      (∀ f ∈ Submodule.span ℤ Tfam, f 1 = 0 →
        ν f = fun x => indG M f x) →
      (∀ ξ ∈ Sfam ∩ Irr ↥M,
        IsSignedIrr G (ν ξ) ∧ IsNonreal (ν ξ) ∧
        (∀ x ∈ cyclicTIset W₁ W₂, ν ξ x = 0) ∧ ∀ i j, cfInner (ν ξ) (η i j) = 0) →
      (∀ j : J, j ≠ j0' →
        ν (Mrow j) = fun x => (-1 : ℂ) ^ e * δ * ∑ i : I,
          η i (if e = 0 then j else bar j) x) →
      (∀ i : I, i ≠ i0 → ∀ ζ ∈ Tfam, cfInner (ν ζ) (η i j0') = 0) →
      (∀ j₀ : J, j₀ ≠ j0' →
        Mrow (if e = 0 then j₀ else bar j₀) ∈ Tfam ∧
        cfInner (ν (Mrow (if e = 0 then j₀ else bar j₀))) (η i0 j₀) = (-1 : ℂ) ^ e * δ ∧
        ∀ ζ ∈ Tfam, ζ ≠ Mrow (if e = 0 then j₀ else bar j₀) →
          cfInner (ν ζ) (η i0 j₀) = 0) →
      (∀ j₀ : J, j₀ ≠ j0' →
        cfInner (Mrow (if e = 0 then j₀ else bar j₀))
          (Mrow (if e = 0 then j₀ else bar j₀)) = (Nat.card ↥W₁ : ℂ)) →
      ∀ i0' : I, i0' ≠ i0 → ∀ j₀ : J, j₀ ≠ j0' →
        ((Nat.card ↥(fittingIn M) : ℝ) - 1 ≤
          sumSqOn (sharp (fittingIn M)) (η i0' j0')) ∧
        ((Nat.card ↥(⁅M, M⁆ : Subgroup G) : ℝ) - (u : ℝ) ^ 2 ≤
          sumSqOn (sharp (fittingIn M)) (η i0 j₀)) ∧
        ∀ lam ∈ Tfam ∩ Irr ↥M,
          ((Nat.card ↥M : ℝ) - ((Nat.card ↥W₁ : ℝ) * (u : ℝ)) ^ 2 ≤
            sumSqOn (sharp (fittingIn M)) (ν lam))

@[expose]
def FNI_abelian_ambient_normal_hall_inertia_and_exponent : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M E K U : Subgroup G, IsSigmaComplementSetup G M E K U →
      U ≠ ⊥ →
      (∀ p ∈ tauTwoPrimes M, ∀ P : Subgroup G, IsSylowTop p P → IsMulCommutative ↥P) →
      ∃ U₁ U₀ : Subgroup G, U₁ ≤ U ∧ U₀ ≤ U ∧
        IsMulCommutative ↥U₁ ∧
        U ≤ Subgroup.normalizer (U₁ : Set G) ∧
        (∀ h ∈ sigmaCore M, h ≠ 1 → cent1 U h ≤ U₁) ∧
        Monoid.exponent ↥U₀ = Monoid.exponent ↥U ∧
        ∀ x ∈ U₀, x ≠ 1 → cent1 (sigmaCore M) x = ⊥

@[expose]
def FNI_abelian_normal_hall_full_exponent_cycle : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (M A E K U P : Subgroup G),
      IsPlaneSetup G p M A E →
      IsHallPiOf (kappaPrimes M) K M → K ≤ E → U ≤ E → IsSemidirect E U K →
      IsSylowTop p P → IsMulCommutative ↥P → A ≤ P → P ≤ U →
      ∃ Z : Subgroup G, Z ≤ P ∧ IsCyclic ↥Z ∧
        U ≤ Subgroup.normalizer (Z : Set G) ∧
        Monoid.exponent ↥Z = Monoid.exponent ↥P ∧
        ∀ z ∈ Z, z ≠ 1 → cent1 (sigmaCore M) z = ⊥

@[expose]
def FNI_abelian_normal_hall_noncentral_action_split : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (M A E K U P : Subgroup G),
      IsPlaneSetup G p M A E →
      IsHallPiOf (kappaPrimes M) K M → K ≤ E → U ≤ E → IsSemidirect E U K →
      IsSylowTop p P → IsMulCommutative ↥P → A ≤ P → P ≤ U →
      ¬ P ≤ cent U (U : Set G) →
      ∃ P₀ P₁ : Subgroup G, P₀ ≠ ⊥ ∧ P₁ ≠ ⊥ ∧ P₀ ≤ P ∧ P₁ ≤ P ∧
        Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (P₀ : Set G) ∧
        Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (P₁ : Set G) ∧
        P₀ ⊔ P₁ = P ∧ P₀ ⊓ P₁ = ⊥

@[expose]
def FNI_abelian_plane_overlap_normalizer_rank : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (M A E P : Subgroup G),
      IsPlaneSetup G p M A E →
      IsSylowTop p P → IsMulCommutative ↥P → A ≤ P →
      ∀ q : ℕ, q.Prime →
        q ∣ (cent E (A : Set G)).relIndex E →
        q ∣ Nat.card ↥(cent E (A : Set G)) →
        elementaryAbelianPRank q ↥(Subgroup.normalizer (P : Set G)) = 2

@[expose]
def FNI_ambient_maximal_plane_derived_prime_complement : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (R A : Subgroup G), p.Prime → IsSylowTop p R →
      A ≤ R → IsElementaryAbelianSubgroup p A → elementaryAbelianPRank p ↥A = 2 →
      (∀ B : Subgroup G, IsElementaryAbelianSubgroup p B → A ≤ B → B = A) →
      ∀ X : Subgroup G, X < ⊤ → R ≤ X →
        ∃ D : Subgroup G, D ≤ ⁅X, X⁆ ∧
          (⁅X, X⁆ : Subgroup G) ≤ Subgroup.normalizer (D : Set G) ∧
          ¬ p ∣ Nat.card ↥D ∧
          ∃ n : ℕ, D.relIndex (⁅X, X⁆ : Subgroup G) = p ^ n

@[expose]
def FNI_kappa_candidate_cyclic_torus : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ (M K A Z : Subgroup G) (I : Set (Subgroup G)) (KT : Subgroup G → Subgroup G),
      IsKappaFamilySetup G M K A Z I KT →
      IsCyclic ↥Z ∧ IsCyclic ↥K ∧ IsCyclic ↥A ∧
      (∃ Mstar : Subgroup G, I = {M, Mstar} ∧ A = KT Mstar ∧ kappaA KT Mstar = K ∧
        (HasNontrivialResidualWitness M K ∨ HasNontrivialResidualWitness Mstar (KT Mstar))) ∧
      ((¬ ∃ U : Subgroup G, U ≠ ⊥ ∧ IsSemidirect M (sigmaCore M) (U ⊔ K) ∧
        IsSemidirect (U ⊔ K) U K) → (Nat.card ↥A).Prime)
where
  HasNontrivialResidualWitness {G : Type u} [Group G] [Fintype G] (V L : Subgroup G) : Prop :=
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsSemidirect V (sigmaCore V) (U ⊔ L) ∧ IsSemidirect (U ⊔ L) U L

@[expose]
def FNI_kappa_candidate_family_common_factors : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ (M K A Z : Subgroup G) (I : Set (Subgroup G)),
      IsKappaSetup G M K A Z → I = kappaFamily M K →
      (∃ KT : Subgroup G → Subgroup G, KT M = K ∧
        ∀ T ∈ I, T ≠ M → IsHallPiOf (kappaPrimes T) (KT T) T ∧ A ≤ KT T) ∧
      2 ≤ I.ncard ∧
      (∀ KT : Subgroup G → Subgroup G, KT M = K →
        (∀ T ∈ I, T ≠ M → IsHallPiOf (kappaPrimes T) (KT T) T ∧ A ≤ KT T) →
        (∀ T ∈ I, (kappaPrimes T).Nonempty) ∧
        (∀ T ∈ I, kappaA KT T ≠ ⊥ ∧
          IsDirect Z (KT T) (kappaA KT T) ∧
          Z = Subgroup.normalizer ((KT T : Subgroup G) : Set G) ⊓ T ∧
          Z < T ∧
          IsHallPiOf (sigmaPrimes T)ᶜ (KT T) Z ∧ Z ≤ Subgroup.normalizer ((KT T : Set G)) ∧
          IsHallPiOf (sigmaPrimes T) (kappaA KT T) Z ∧
          Z ≤ Subgroup.normalizer ((kappaA KT T : Subgroup G) : Set G)) ∧
        (∀ T ∈ I, ∀ V ∈ I, T ≠ V →
          kappaA KT T ⊓ kappaA KT V = ⊥ ∧ kappaA KT T ≤ KT V ∧
          ¬ ∃ g : G, conjSub T g = V)) ∧
      (∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
        ∃ T ∈ I, T ≠ M ∧ Subgroup.normalizer (X : Set G) ≤ T ∧ X ≤ sigmaCore T)

@[expose]
def FNI_kappa_candidate_has_nontrivial_residual : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ (M K A Z : Subgroup G) (I : Set (Subgroup G)) (KT : Subgroup G → Subgroup G),
      IsKappaFamilySetup G M K A Z I KT →
      ∃ V ∈ I, ∃ U : Subgroup G, U ≠ ⊥ ∧
        IsSemidirect V (sigmaCore V) (U ⊔ KT V) ∧ IsSemidirect (U ⊔ KT V) U (KT V)

@[expose]
def FNI_kappa_candidate_mixed_set_description : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ (M K A Z : Subgroup G) (I : Set (Subgroup G)) (KT : Subgroup G → Subgroup G),
      IsKappaFamilySetup G M K A Z I KT →
      mixedTorusSet Z I KT =
          ⋃ V ∈ I, {x : G | ∃ a ∈ kappaA KT V, a ≠ 1 ∧ ∃ b ∈ KT V, b ≠ 1 ∧ x = a * b} ∧
        (mixedTorusSet Z I KT).Nonempty ∧
        ((mixedTorusSet Z I KT).ncard : ℤ)
          = (Nat.card ↥Z : ℤ) + (I.ncard : ℤ) - 1 - ∑ᶠ V ∈ I, (Nat.card ↥(kappaA KT V) : ℤ)

@[expose]
def FNI_kappa_candidate_mixed_set_ti : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ (M K A Z : Subgroup G) (I : Set (Subgroup G)) (KT : Subgroup G → Subgroup G),
      IsKappaFamilySetup G M K A Z I KT →
      Subgroup.normalizer (mixedTorusSet Z I KT) = Z ∧
        ∀ g : G, g ∉ Z → mixedTorusSet Z I KT ∩ conjSet (mixedTorusSet Z I KT) g = ∅

@[expose]
def FNI_kappa_candidate_mixed_support_cardinality : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ (M K A Z : Subgroup G) (I : Set (Subgroup G)) (KT : Subgroup G → Subgroup G),
      IsKappaFamilySetup G M K A Z I KT →
      ((sat (mixedTorusSet Z I KT)).ncard : ℚ)
          = (Nat.card G : ℚ) * (1 + ((I.ncard : ℚ) - 1) / (Nat.card ↥Z : ℚ)
              - ∑ᶠ V ∈ I, (1 : ℚ) / (Nat.card ↥(KT V) : ℚ)) ∧
        (sat (mixedTorusSet Z I KT)).Nonempty ∧
        (∀ V ∈ I, (sigmaDelta V).Nonempty) ∧
        (∀ V ∈ I, Disjoint (sat (mixedTorusSet Z I KT)) (sigmaDelta V)) ∧
        (∀ V ∈ I, ∀ V' ∈ I, V ≠ V' → Disjoint (sigmaDelta V) (sigmaDelta V')) ∧
        (1 : G) ∉ sat (mixedTorusSet Z I KT) ∧
        (∀ V ∈ I, (1 : G) ∉ sigmaDelta V)

@[expose]
def FNI_kappa_candidate_prime_collapse : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ (M K A Z : Subgroup G) (I : Set (Subgroup G)) (KT : Subgroup G → Subgroup G),
      IsKappaFamilySetup G M K A Z I KT →
      ∃ V ∈ I, ∃ W ∈ I, V ≠ W ∧ I = {V, W} ∧
        ∃ U : Subgroup G, U ≠ ⊥ ∧
          IsSemidirect V (sigmaCore V) (U ⊔ KT V) ∧ IsSemidirect (U ⊔ KT V) U (KT V) ∧
          (Nat.card ↥(KT V)).Prime ∧
          Group.IsNilpotent ↥(sigmaCore V) ∧
          kappaA KT W = KT V ∧ kappaA KT V = KT W

@[expose]
def FNI_kappa_complement_rank_one_prime_regularity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M E K U : Subgroup G, IsSigmaComplementSetup G M E K U →
      (∀ q ∈ tau1Primes M ∪ tau3Primes M, ∀ x ∈ U, orderOf x = q →
        cent1 (sigmaCore M) x = ⊥) ∧
      IsHallPiOf (kappaPrimes M)ᶜ U E ∧ E ≤ Subgroup.normalizer (U : Set G)

@[expose]
def FNI_kappa_derived_complement : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      IsSemidirect M (⁅M, M⁆ : Subgroup G) K ∧
      kappaPrimes M = tau1Primes M ∧
      ∀ U : Subgroup G,
        IsSemidirect M (sigmaCore M) (U ⊔ K) → IsSemidirect (U ⊔ K) U K →
          (⁅M, M⁆ : Subgroup G) = sigmaCore M ⊔ U

@[expose]
def FNI_kappa_first_supported_complement_action : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M E E₁ E₂ E₃ K : Subgroup G,
      IsThreeHallSetup G M E E₁ E₂ E₃ →
      K ≠ ⊥ → IsHallPiOf (kappaPrimes M) K M → K ≤ E₁ →
      K = E₁ ∧
      IsMulCommutative ↥(E₃ ⊔ E₂) ∧
      E ≤ Subgroup.normalizer ((E₃ ⊔ E₂ : Subgroup G) : Set G) ∧
      IsHallPiOf (sigmaPrimes M ∪ kappaPrimes M)ᶜ (E₃ ⊔ E₂) M ∧
      IsSemidirect M (sigmaCore M) ((E₃ ⊔ E₂) ⊔ K) ∧
      IsSemidirect ((E₃ ⊔ E₂) ⊔ K) (E₃ ⊔ E₂) K ∧
      (∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
        K ≤ Subgroup.normalizer (X : Set G)) ∧
      cent (sigmaCore M) (K : Set G) ≠ ⊥ ∧
      (∀ X : Subgroup G, X ≤ K → X ≠ ⊥ →
        cent (sigmaCore M) (X : Set G) = cent (sigmaCore M) (K : Set G)) ∧
      (∀ k ∈ K, k ≠ 1 → cent1 (E₃ ⊔ E₂) k = ⊥)

@[expose]
def FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      A ≠ ⊥ ∧
      (∀ (q : ℕ) (X : Subgroup G), q.Prime → X ≤ A → Nat.card ↥X = q →
        Subgroup.centralizer (X : Set G) ≤ M ∧
        ∀ T : Subgroup G, IsCoatom T → Subgroup.centralizer (X : Set G) ≤ T → T = M) ∧
      (∀ (q : ℕ) (Q : Subgroup G), q.Prime → q ∣ Nat.card ↥A → IsSylowOf q Q M →
        (∀ T : Subgroup G, IsCoatom T → Q ≤ T → T = M) ∧ ¬ Q ≤ A)

@[expose]
def FNI_kappa_global_pair_exhaustion : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z Mstar : Subgroup G, IsKappaSetup G M K A Z →
      IsCoatom Mstar →
      (∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
        Subgroup.normalizer (X : Set G) ≤ Mstar) →
      (∀ T : Subgroup G, IsCoatom T →
        (∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
          Subgroup.normalizer (X : Set G) ≤ T) → T = Mstar) →
      ∀ H : Subgroup G, IsCoatom H → (kappaPrimes H).Nonempty →
        ∃ g : G, conjSub H g = M ∨ conjSub H g = Mstar

@[expose]
def FNI_kappa_local_pair : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      ∃ Mstar : Subgroup G,
        (IsCoatom Mstar ∧ ∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
          Subgroup.normalizer (X : Set G) ≤ Mstar) ∧
        (∀ T : Subgroup G, IsCoatom T →
          (∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
            Subgroup.normalizer (X : Set G) ≤ T) → T = Mstar) ∧
        (¬ ∃ g : G, conjSub M g = Mstar) ∧
        A ≠ ⊥ ∧ IsHallPiOf (kappaPrimes Mstar) A Mstar ∧
        cent (sigmaCore Mstar) (A : Set G) = K ∧
        IsDirect Z K A ∧ IsCyclic ↥Z ∧
        Subgroup.normalizer (K : Set G) ⊓ M = Z ∧
        Subgroup.normalizer (A : Set G) ⊓ Mstar = Z ∧
        (∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
          Subgroup.normalizer (X : Set G) ≤ Mstar ∧
          Subgroup.centralizer (X : Set G) ≤ Mstar ∧
          (∀ T : Subgroup G, IsCoatom T → Subgroup.normalizer (X : Set G) ≤ T → T = Mstar) ∧
          (∀ T : Subgroup G, IsCoatom T → Subgroup.centralizer (X : Set G) ≤ T → T = Mstar)) ∧
        (∀ Y : Subgroup G, Y ≤ A → (Nat.card ↥Y).Prime →
          Subgroup.centralizer (Y : Set G) ≤ M ∧
          ∀ T : Subgroup G, IsCoatom T → Subgroup.centralizer (Y : Set G) ≤ T → T = M) ∧
        (((Z : Set G) \ ((K : Set G) ∪ (A : Set G))).Nonempty ∧
          Subgroup.normalizer ((Z : Set G) \ ((K : Set G) ∪ (A : Set G))) = Z ∧
          ∀ g : G, g ∉ Z →
            ((Z : Set G) \ ((K : Set G) ∪ (A : Set G)))
              ∩ conjSet ((Z : Set G) \ ((K : Set G) ∪ (A : Set G))) g = ∅) ∧
        ((∃ U : Subgroup G, U ≠ ⊥ ∧ IsSemidirect M (sigmaCore M) (U ⊔ K) ∧
            IsSemidirect (U ⊔ K) U K) ∨
          ∃ V : Subgroup G, V ≠ ⊥ ∧ IsSemidirect Mstar (sigmaCore Mstar) (V ⊔ A) ∧
            IsSemidirect (V ⊔ A) V A)

@[expose]
def FNI_kappa_mixed_elements_avoid_packets : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M K : Subgroup G, IsCoatom M → (kappaPrimes M).Nonempty →
      IsHallPiOf (kappaPrimes M) K M →
      ∀ x ∈ cent (sigmaCore M) (K : Set G), x ≠ 1 →
        ∀ y ∈ K, y ≠ 1 →
          ∀ T : Subgroup G, IsCoatom T → x * y ∉ sigmaDelta T

@[expose]
def FNI_kappa_normalizer_centralizer_structure : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      IsDirect (Subgroup.normalizer (K : Set G) ⊓ M) K A ∧
      (∀ X : Subgroup G, X ≤ K → X ≠ ⊥ → K ≤ Subgroup.normalizer (X : Set G) →
        Subgroup.normalizer (X : Set G) ⊓ M = Subgroup.normalizer (K : Set G) ⊓ M) ∧
      (∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
        K ≤ Subgroup.normalizer (X : Set G) ∧
        Subgroup.normalizer (X : Set G) ⊓ M = Subgroup.normalizer (K : Set G) ⊓ M ∧
        ∀ T : Subgroup G, IsCoatom T → Subgroup.normalizer (X : Set G) ≤ T →
          X ≤ sigmaCore T)

@[expose]
def FNI_kappa_normalizer_reflection : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      ∀ X T : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
        IsCoatom T → Subgroup.normalizer (X : Set G) ≤ T →
        (¬ ∃ g : G, conjSub T g = M) ∧ Z ≤ T ∧ (kappaPrimes T).Nonempty ∧
          (∃ L : Subgroup G, IsHallPiOf (kappaPrimes T) L T ∧ A ≤ L) ∧
          ∀ Y : Subgroup G, Y ≤ A → (Nat.card ↥Y).Prime →
            Z ≤ Subgroup.normalizer (Y : Set G) ⊓ T

@[expose]
def FNI_kappa_pair_hall_intersection : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z Mstar : Subgroup G, IsKappaSetup G M K A Z →
      IsCoatom Mstar →
      (∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
        Subgroup.normalizer (X : Set G) ≤ Mstar) →
      (∀ T : Subgroup G, IsCoatom T →
        (∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
          Subgroup.normalizer (X : Set G) ≤ T) → T = Mstar) →
      IsHallPiOf (sigmaPrimes M) A Mstar ∧
      sigmaCore M ⊓ Mstar = A ∧
      M ⊓ Mstar = Z ∧
      ∀ x ∈ K, x ≠ 1 → ∀ y ∈ A, y ≠ 1 →
        cent1 M x = Z ∧ cent1 Mstar y = Z ∧ Subgroup.centralizer {x * y} = Z

@[expose]
def FNI_kappa_pair_mixed_density : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      ((sat ((Z : Set G) \ ((K : Set G) ∪ (A : Set G)))).ncard : ℚ)
          = (Nat.card G : ℚ) * ((Nat.card ↥K : ℚ) - 1) * ((Nat.card ↥A : ℚ) - 1)
              / ((Nat.card ↥K : ℚ) * (Nat.card ↥A : ℚ)) ∧
        (Nat.card G : ℚ) / 2
          < ((sat ((Z : Set G) \ ((K : Set G) ∪ (A : Set G)))).ncard : ℚ)

@[expose]
def FNI_kappa_reflected_common_normalizer : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      ∀ X T L B : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
        IsCoatom T → Subgroup.normalizer (X : Set G) ≤ T →
        IsHallPiOf (kappaPrimes T) L T → A ≤ L →
        B = cent (sigmaCore T) (L : Set G) →
        IsDirect Z L B ∧ Z = Subgroup.normalizer (L : Set G) ⊓ T

@[expose]
def FNI_kappa_semiprime_complement_existence : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ M K : Subgroup G, IsCoatom M → (kappaPrimes M).Nonempty →
      IsHallPiOf (kappaPrimes M) K M →
      K ≠ ⊥ ∧
      ∃ U E₁ : Subgroup G,
        IsMulCommutative ↥U ∧
        IsHallPiOf (sigmaPrimes M ∪ kappaPrimes M)ᶜ U M ∧
        IsSemidirect M (sigmaCore M) (U ⊔ K) ∧
        IsSemidirect (U ⊔ K) U K ∧
        E₁ ≠ ⊥ ∧ IsHallPiOf (tau1Primes M) E₁ (U ⊔ K) ∧ E₁ ≤ K ∧
        (∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
          K ≤ Subgroup.normalizer (X : Set G)) ∧
        (∀ X : Subgroup G, X ≤ K → X ≠ ⊥ →
          cent (sigmaCore M) (X : Set G) = cent (sigmaCore M) (K : Set G)) ∧
        cent (sigmaCore M) (K : Set G) ≠ ⊥ ∧
        ∀ k ∈ K, k ≠ 1 → cent1 U k = ⊥

@[expose]
def FNI_kappa_third_supported_complement_action : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M E E₁ E₂ E₃ K : Subgroup G,
      IsThreeHallSetup G M E E₁ E₂ E₃ →
      IsHallPiOf (kappaPrimes M) K M → K ≤ E →
      (∃ p ∈ kappaPrimes M ∩ tau3Primes M, p ∣ Nat.card ↥K) →
      K = E ∧ E₂ = ⊥ ∧ E₁ ≠ ⊥ ∧
      (∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
        K ≤ Subgroup.normalizer (X : Set G)) ∧
      cent (sigmaCore M) (K : Set G) ≠ ⊥ ∧
      ∀ X : Subgroup G, X ≤ K → X ≠ ⊥ →
        cent (sigmaCore M) (X : Set G) = cent (sigmaCore M) (K : Set G)

@[expose]
def FNI_kappa_trivial_residual_prime_fixed_core : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ M K A Z : Subgroup G, IsKappaSetup G M K A Z →
      IsSemidirect M (sigmaCore M) K →
      IsCyclic ↥K ∧ (⁅M, M⁆ : Subgroup G) = sigmaCore M ∧ (Nat.card ↥A).Prime ∧
        ∀ X : Subgroup G, X ≤ K → X ≠ ⊥ → cent (sigmaCore M) (X : Set G) = A

@[expose]
def FNI_nonabelian_ambient_normal_hall_free_complement : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (M A E K U : Subgroup G),
      IsPlaneSetup G p M A E →
      (∃ P : Subgroup G, IsSylowTop p P ∧ ¬ IsMulCommutative ↥P) →
      IsHallPiOf (kappaPrimes M) K M → K ≤ E → U ≤ E → IsSemidirect E U K →
      ∀ A₀ : Subgroup G, A₀ = cent A (sigmaCore M : Set G) →
        A₀ ≤ U ∧ IsMulCommutative ↥A₀ ∧ U ≤ Subgroup.normalizer (A₀ : Set G) ∧
        ∃ V : Subgroup G, IsSemidirect U A₀ V ∧
          p ∣ Nat.card ↥V ∧
          Monoid.exponent ↥V = Monoid.exponent ↥U ∧
          (∀ v ∈ V, v ≠ 1 → cent1 (sigmaCore M) v = ⊥) ∧
          ∀ h ∈ sigmaCore M, h ≠ 1 → cent1 U h = A₀

@[expose]
def FNI_nonabelian_ambient_plane_centralizer : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (M A E P R : Subgroup G),
      IsPlaneSetup G p M A E →
      (∃ Q : Subgroup G, IsSylowTop p Q ∧ ¬ IsMulCommutative ↥Q) →
      IsSylowOf p P E → A ≤ P → IsSylowTop p R → P ≤ R →
      IsMulCommutative ↥P ∧ ¬ IsMulCommutative ↥R ∧ P < R ∧
        R ⊓ M = P ∧ cent R (A : Set G) = P ∧
        ∀ Z₀ : Subgroup G,
          (Z₀ : Set G) = {z : G | z ∈ cent R (R : Set G) ∧ z ^ p = 1} →
          Z₀ ≤ A ∧ Nat.card ↥Z₀ = p ∧
            ∀ B₁ B₂ : Subgroup G, B₁ ≤ A → B₂ ≤ A →
              Nat.card ↥B₁ = p → Nat.card ↥B₂ = p → B₁ ≠ Z₀ → B₂ ≠ Z₀ →
              ∃ g ∈ Subgroup.normalizer (A : Set G) ⊓ R, conjSub B₁ g = B₂

@[expose]
def FNI_nonabelian_ambient_prime_kernel_complement : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (M A E : Subgroup G),
      IsPlaneSetup G p M A E →
      (∃ Q : Subgroup G, IsSylowTop p Q ∧ ¬ IsMulCommutative ↥Q) →
      ∀ A₀ : Subgroup G, A₀ = cent A (sigmaCore M : Set G) →
        Nat.card ↥A₀ = p ∧
        M ≤ Subgroup.normalizer (A₀ : Set G) ∧
        A₀ ≤ Subgroup.centralizer ((sigmaCore M : Subgroup G) : Set G) ∧
        (∀ P : Subgroup G, IsSylowOf p P E → IsMulCommutative ↥P) ∧
        ∃ E₀ : Subgroup G, IsSemidirect E A₀ E₀ ∧ p ∣ Nat.card ↥E₀ ∧
          ∀ h ∈ sigmaCore M, h ≠ 1 →
            ∀ r ∈ (Nat.card ↥(cent1 E₀ h)).primeFactors, r ∈ tau1Primes M

@[expose]
def FNI_nonabelian_ambient_single_rank_two_prime : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsAmbient G →
    ∀ (p : ℕ) (M A E : Subgroup G),
      IsPlaneSetup G p M A E →
      (∃ Q : Subgroup G, IsSylowTop p Q ∧ ¬ IsMulCommutative ↥Q) →
      tauTwoPrimes M = {p}

end Statements

end

end CFSG.FeitThompson
