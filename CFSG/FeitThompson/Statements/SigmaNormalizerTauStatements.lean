module

public import CFSG.FeitThompson.Definitions.DadeSupportExtension
public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
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

universe u

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure IsOddOrderMinimalSimple (G : Type*) [Group G] [Finite G] : Prop where
  odd_natCard : Odd (Nat.card G)
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  isSolvable_of_ne_top : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H

namespace IsOddOrderMinimalSimple

variable {G : Type*} [Group G] [Finite G]

theorem nontrivial (h : IsOddOrderMinimalSimple G) : Nontrivial G :=
  h.isSimpleGroup.toNontrivial

theorem isSolvable_of_lt (h : IsOddOrderMinimalSimple G) {H : Subgroup G} (hH : H < ⊤) :
    Group.IsSolvable H := h.isSolvable_of_ne_top H hH.ne

end IsOddOrderMinimalSimple

variable {G : Type*} [Group G]

@[expose]
def fittingIn [Finite G] (M : Subgroup G) : Subgroup G := (fittingRaw ↥M).map M.subtype

@[expose]
def piCoreIn [Finite G] (π : Set ℕ) (M : Subgroup G) : Subgroup G := (piCore π ↥M).map M.subtype

@[expose]
def centerIn (M : Subgroup G) : Subgroup G := (Subgroup.center ↥M).map M.subtype

theorem fittingIn_le [Finite G] (M : Subgroup G) : fittingIn M ≤ M := Subgroup.map_subtype_le _

theorem piCoreIn_le [Finite G] (π : Set ℕ) (M : Subgroup G) : piCoreIn π M ≤ M :=
  Subgroup.map_subtype_le _

theorem centerIn_le (M : Subgroup G) : centerIn M ≤ M := Subgroup.map_subtype_le _

theorem pCoreIn_eq_piCoreIn [Finite G] (p : ℕ) (M : Subgroup G) :
    pCoreIn p M = piCoreIn ({p} : Set ℕ) M := by
  rw [pCoreIn, piCoreIn, pCore_eq_piCore]

theorem pComplCoreIn_eq_piCoreIn [Finite G] (p : ℕ) (M : Subgroup G) :
    pComplCoreIn p M = piCoreIn {q : ℕ | q.Prime ∧ q ≠ p} M := by
  rw [pComplCoreIn, piCoreIn, pComplCore_eq_piCore]

@[expose]
def satSet (A : Set G) : Set G := ⋃ g : G, conjSet A g

theorem subset_satSet (A : Set G) : A ⊆ satSet A := fun _ hx =>
  Set.mem_iUnion.2 ⟨1, by rwa [conjSet_one]⟩

theorem mem_satSet_iff {A : Set G} {x : G} : x ∈ satSet A ↔ ∃ g : G, x ∈ conjSet A g :=
  Set.mem_iUnion

@[expose]
noncomputable def cfInnerFin {α : Type*} [Finite α] (f h : α → ℂ) : ℂ :=
  letI : Fintype α := Fintype.ofFinite α
  cfInner f h

theorem cfInnerFin_eq_cfInner {α : Type*} [Fintype α] (f h : α → ℂ) :
    cfInnerFin f h = cfInner f h := by
  unfold cfInnerFin
  congr 1
  exact Subsingleton.elim _ _

@[expose]
noncomputable def sigCoreSignalizer [Finite G] (a : G) : Subgroup G :=
  canonicalSignalizer (maximalSubgroups G) sigmaCore a

theorem sigCoreSignalizer_eq [Finite G] (a : G) :
    sigCoreSignalizer a = canonicalSignalizer (maximalSubgroups G) sigmaCore a := (rfl)

@[expose]
noncomputable def dadeSupportDomain [Finite G] (L : Subgroup G) : Set G :=
  totalDadeSupport ((hallCoreIn L : Set G) \ {1}) sigCoreSignalizer

theorem dadeSupportDomain_eq [Finite G] (L : Subgroup G) :
    dadeSupportDomain L = totalDadeSupport ((hallCoreIn L : Set G) \ {1}) sigCoreSignalizer := (rfl)

@[expose]
noncomputable def extendSub (K : Subgroup G) (θ : ↥K → ℂ) : G → ℂ :=
  Function.extend K.subtype θ 0

theorem extendSub_apply_coe (K : Subgroup G) (θ : ↥K → ℂ) (x : ↥K) :
    extendSub K θ (x : G) = θ x := K.subtype_injective.extend_apply θ 0 x

theorem extendSub_apply_of_notMem (K : Subgroup G) (θ : ↥K → ℂ) {z : G} (hz : z ∉ K) :
    extendSub K θ z = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨a, rfl⟩
  exact hz a.2

@[expose]
noncomputable def tauDade [Finite G] (L : Subgroup G) (f : ↥L → ℂ) : G → ℂ :=
  dadeSupportExtension ((hallCoreIn L : Set G) \ {1}) sigCoreSignalizer (extendSub L f)

theorem tauDade_eq_zero_of_notMem_dadeSupportDomain [Finite G] {L : Subgroup G} {f : ↥L → ℂ} {x : G}
    (hx : x ∉ dadeSupportDomain L) : tauDade L f x = 0 :=
  dadeSupportExtension_eq_zero_of_notMem hx

@[expose]
noncomputable def indBetween [Finite G] (K L : Subgroup G) (θ : ↥K → ℂ) (y : ↥L) : ℂ :=
  letI : Fintype ↥L := Fintype.ofFinite ↥L
  (Nat.card ↥K : ℂ)⁻¹ * ∑ t : ↥L, extendSub K θ ((t : G)⁻¹ * (y : G) * (t : G))

@[expose]
noncomputable def indTop [Finite G] (K : Subgroup G) (θ : ↥K → ℂ) (y : G) : ℂ :=
  letI : Fintype G := Fintype.ofFinite G
  (Nat.card ↥K : ℂ)⁻¹ * ∑ t : G, extendSub K θ (t⁻¹ * y * t)

theorem indBetween_apply (K L : Subgroup G) [Fintype ↥L] [Finite G] (θ : ↥K → ℂ) (y : ↥L) :
    indBetween K L θ y
      = (Nat.card ↥K : ℂ)⁻¹ * ∑ t : ↥L, extendSub K θ ((t : G)⁻¹ * (y : G) * (t : G)) := by
  unfold indBetween
  congr 1
  exact Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun _ _ => rfl

theorem indTop_apply [Fintype G] (K : Subgroup G) (θ : ↥K → ℂ) (y : G) :
    indTop K θ y = (Nat.card ↥K : ℂ)⁻¹ * ∑ t : G, extendSub K θ (t⁻¹ * y * t) := by
  unfold indTop
  congr 1
  exact Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun _ _ => rfl

@[expose]
noncomputable def calLFam [Finite G] (L : Subgroup G) : Set (↥L → ℂ) :=
  indBetween (hallCoreIn L) L '' {θ : ↥(hallCoreIn L) → ℂ | θ ∈ Irr ↥(hallCoreIn L) ∧ θ ≠ 1}

theorem mem_calLFam [Finite G] {L : Subgroup G} {f : ↥L → ℂ} :
    f ∈ calLFam L ↔ ∃ θ : ↥(hallCoreIn L) → ℂ,
      (θ ∈ Irr ↥(hallCoreIn L) ∧ θ ≠ 1) ∧ indBetween (hallCoreIn L) L θ = f := Iff.rfl

@[expose]
noncomputable def hallCoreIndex [Finite G] (L : Subgroup G) : ℕ := (hallCoreIn L).relIndex L

theorem hallCoreIndex_eq [Finite G] (L : Subgroup G) :
    hallCoreIndex L = (hallCoreIn L).relIndex L := (rfl)

@[expose]
def IsCoherentDade [Finite G] (L : Subgroup G) (ν : (↥L → ℂ) → (G → ℂ)) : Prop :=
  (∀ f ∈ Submodule.span ℤ (calLFam L), ∀ g ∈ Submodule.span ℤ (calLFam L),
      ν (f + g) = ν f + ν g) ∧
  (∀ f ∈ Submodule.span ℤ (calLFam L), ν f ∈ virtualChars G) ∧
  (∀ f ∈ Submodule.span ℤ (calLFam L), ∀ g ∈ Submodule.span ℤ (calLFam L),
      cfInnerFin (ν f) (ν g) = cfInnerFin f g) ∧
  (∀ f ∈ Submodule.span ℤ (calLFam L), f 1 = 0 → ν f = tauDade L f)

structure IsOmegaMap [Finite G] (W₁ W₂ : Subgroup G)
    (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)) : Prop where
  isClassFun : ∀ f, IsClassFun (ω f)
  inner_eq : ∀ f h, cfInnerFin (ω f) (ω h) = cfInnerFin f h
  maps_virtualChars : ∀ f, f ∈ virtualChars ↥(W₁ ⊔ W₂) → ω f ∈ virtualChars G
  map_principal : ω 1 = 1
  eq_ind : ∀ f, (∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ → f z = 0) →
    ω f = indTop (W₁ ⊔ W₂) f

structure IsSigmaMap [Finite G] (S W₁ W₂ : Subgroup G)
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) : Prop where
  isClassFun : ∀ f, IsClassFun (σ f)
  inner_eq : ∀ f h, cfInnerFin (σ f) (σ h) = cfInnerFin f h
  maps_virtualChars : ∀ f, f ∈ virtualChars ↥(W₁ ⊔ W₂) → σ f ∈ virtualChars ↥S
  map_principal : σ 1 = 1
  eq_ind : ∀ f, (∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ → f z = 0) →
    σ f = indBetween (W₁ ⊔ W₂) S f

@[expose]
def IsProductCharFamily {I J : Type*} (W₁ W₂ : Subgroup G)
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ))
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ)) : Prop :=
  ∀ (i : I) (j : J) (x : ↥W₁) (y : ↥W₂) (hxy : (x : G) * (y : G) ∈ W₁ ⊔ W₂),
    w i j ⟨(x : G) * (y : G), hxy⟩ = α i x * β j y

@[expose]
def IsIrrIndexing (X : Subgroup G) {I : Type*} (α : I → (↥X → ℂ)) (i₀ : I) : Prop :=
  Function.Injective α ∧ Set.range α = Irr ↥X ∧ α i₀ = 1

structure IsPBridgeData [Fintype G] (S L U W₁ W₂ : Subgroup G)
    {I J : Type u} [Fintype I] [Fintype J]
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J)
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
    (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
    (b : J → (↥S → ℂ)) : Prop where
  isCoatom_S : IsCoatom S
  isPConfig : IsWitnessedPConfiguration S U W₁ W₂
  isCoatom_L : IsCoatom L
  isTypeI_L : IsTypeI L
  isIrrIndexing_W₁ : IsIrrIndexing W₁ α i₀
  isIrrIndexing_W₂ : IsIrrIndexing W₂ β j₀
  isProductCharFamily : IsProductCharFamily W₁ W₂ α β w
  isSigmaMap : IsSigmaMap S W₁ W₂ σ
  isOmegaMap : IsOmegaMap W₁ W₂ ω
  eta_eq : ∀ i j, η i j = ω (w i j)
  delta_sign : ∀ j, δ j = 1 ∨ δ j = -1
  mu_eq : ∀ j, μ j = δ j • σ (w i₀ j)
  mu_irr : ∀ j, μ j ∈ Irr ↥S
  gamma_eq : γ = indBetween (hallCoreIn S ⊔ W₁) S 1
  b_eq : ∀ j, b j = γ - μ j

namespace Statements

@[expose]
def FBG_outside_sigma_kappa_core_fixer_cyclic : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ X : Subgroup G, X ≤ M →
      IsPiSubgroup ((sigmaPrimes M ∪ kappaPrimes M)ᶜ) X →
      sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥ →
      IsCyclic ↥X ∧ IsPiSubgroup (tauTwoPrimes M) X

@[expose]
def FBG_overlap_kappa_exceptional_prime_cube : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ g : G, g ∉ M →
    ∀ X : Subgroup G, X = fittingIn M ⊓ conjSubgroup (fittingIn M) g → X ≠ ⊥ →
    ∀ H : Subgroup G, H = hallCoreIn M → ¬ IsMulCommutative ↥H →
    ∀ K : Subgroup G, K ≠ ⊥ → IsHallPiSubgroupOf (kappaPrimes M) K M →
      H = sigmaCore M → FreeCore.IsInternalSemidirectProduct M H K →
    ∀ p : ℕ, p = Nat.card ↥X →
    ∀ P : Subgroup G, P = pCoreIn p H →
    ∀ Z₀ : Set G, Z₀ = {z | z ∈ P ⊓ centralizer (P : Set G) ∧ z ^ p = 1} →
      ((H ⊓ centralizer (K : Set G) : Subgroup G) : Set G) = Z₀ →
      ¬ (Nat.card ↥K ∣ p - 1) →
      p.Prime ∧ Odd p ∧
        ((P ⊓ centralizer (P : Set G) : Subgroup G) : Set G) = Z₀ ∧
        Nat.card ↥(P ⊓ centralizer (P : Set G) : Subgroup G) = p ∧
        elementaryAbelianPRank p ↥P ≤ 2 ∧
        Nat.card ↥P = p ^ 3 ∧
        (∀ x ∈ P, x ^ p = 1) ∧
        (∀ k ∈ K, (∀ x ∈ P, k⁻¹ * x * k = x) → k = 1) ∧
        (Nat.card ↥K).Coprime p ∧
        (∀ k ∈ K, ∀ z ∈ P ⊓ centralizer (P : Set G), k⁻¹ * z * k = z)

@[expose]
def FBG_overlap_kappa_fixed_line_order_position : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ g : G, g ∉ M →
    ∀ X : Subgroup G, X = fittingIn M ⊓ conjSubgroup (fittingIn M) g → X ≠ ⊥ →
    ∀ H : Subgroup G, H = hallCoreIn M → ¬ IsMulCommutative ↥H →
    ∀ K : Subgroup G, K ≠ ⊥ → IsHallPiSubgroupOf (kappaPrimes M) K M →
      H = sigmaCore M → FreeCore.IsInternalSemidirectProduct M H K →
    ∀ p : ℕ, p = Nat.card ↥X →
    ∀ P : Subgroup G, P = pCoreIn p H →
    ∀ Z₀ : Set G, Z₀ = {z | z ∈ P ⊓ centralizer (P : Set G) ∧ z ^ p = 1} →
    ∀ Kstar : Subgroup G, Kstar = H ⊓ centralizer (K : Set G) →
      p.Prime ∧ IsCyclic ↥K ∧ Nat.card ↥Kstar = p ∧ Kstar ≤ P ∧
        ((∀ q ∈ (Nat.card ↥H).primeFactors, Nat.card ↥K ∣ q - 1) ∨
          ((Kstar : Set G) = Z₀ ∧ ¬ (Nat.card ↥K ∣ p - 1)))

@[expose]
def FBG_paired_field_array_value_cover : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ S T U V W₁ W₂ : Subgroup G, IsCoatom S → IsCoatom T → S ≠ T →
      IsWitnessedPConfiguration S U W₁ W₂ → IsWitnessedPConfiguration T V W₂ W₁ →
    ∀ P Q : Subgroup G, P = hallCoreIn S → Q = hallCoreIn T →
    ∀ p q u v : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
      u = Nat.card ↥U → v = Nat.card ↥V →
      p.Prime → q.Prime → Odd p → Odd q → q < p →
      (∃ d : ℕ, 1 ≤ d ∧ Nonempty (↥P ≃* (Fin d → Multiplicative (ZMod p)))) →
      (∀ N : Subgroup G, N ≤ P → U ≤ normalizer (N : Set G) → N = ⊥ ∨ N = P) →
    ∀ I J : Type u, ∀ (_ : Fintype I) (_ : Fintype J),
    ∀ (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J),
      IsIrrIndexing W₁ α i₀ → IsIrrIndexing W₂ β j₀ →
    ∀ w : I → J → (↥(W₁ ⊔ W₂) → ℂ), IsProductCharFamily W₁ W₂ α β w →
    ∀ ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ), IsOmegaMap W₁ W₂ ω →
    ∀ η : I → J → (G → ℂ), (∀ i j, η i j = ω (w i j)) →
    ∀ E : Set G, E = satSet ((P : Set G) \ {1}) ∪ satSet ((Q : Set G) \ {1}) ∪
        satSet (cyclicTIset W₁ W₂) →
    ∀ D : Set G, ∀ f : G → ℂ, IsClassFun f →
    ∀ ε : I → J → ℂ, (∀ i j, ε i j = 1 ∨ ε i j = -1) →
      (∀ g : G, g ∉ D → f g = ∑ i : I, ∑ j : J, ε i j * η i j g) →
      ∀ g : G, g ∉ D ∪ E → 1 ≤ ‖f g‖ ^ 2

@[expose]
def FBG_paired_local_geometry : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ K U : Subgroup G, IsHallPiSubgroupOf (kappaPrimes M) K M → U ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K) →
      FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K →
      K ≤ normalizer (U : Set G) → K ≠ ⊥ →
    ∀ Kstar : Subgroup G, Kstar = sigmaCore M ⊓ centralizer (K : Set G) →
      ∃ Mstar : Subgroup G, IsCoatom Mstar ∧ (∀ g : G, Mstar ≠ conjSubgroup M g) ∧
        IsHallPiSubgroupOf (kappaPrimes Mstar) Kstar Mstar ∧
        sigmaCore Mstar ⊓ centralizer (Kstar : Set G) = K ∧
        M ⊓ Mstar = K ⊔ Kstar ∧ IsInternalDirectProduct (M ⊓ Mstar) K Kstar ∧
        IsCyclic ↥(M ⊓ Mstar) ∧
        IsTIWithNormalizer (cyclicTIset K Kstar) (M ⊓ Mstar) ∧
        (∀ L : Subgroup G, IsCoatom L → (kappaPrimes L).Nonempty →
          (∃ g : G, L = conjSubgroup M g) ∨ (∃ g : G, L = conjSubgroup Mstar g)) ∧
        (U ≠ ⊥ ∨ ∃ K' U' : Subgroup G, IsHallPiSubgroupOf (kappaPrimes Mstar) K' Mstar ∧
          U' ≤ Mstar ∧
          FreeCore.IsInternalSemidirectProduct Mstar (sigmaCore Mstar) (U' ⊔ K') ∧
          FreeCore.IsInternalSemidirectProduct (U' ⊔ K') U' K' ∧
          K' ≤ normalizer (U' : Set G) ∧ U' ≠ ⊥)

@[expose]
def FBG_paired_maximal_configuration : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    (∃ M : Subgroup G, IsCoatom M ∧ ¬ IsTypeI M) →
      ∃ S T W₁ W₂ : Subgroup G, IsCoatom S ∧ IsCoatom T ∧ S ≠ T ∧
        W₁ ≠ ⊥ ∧ W₂ ≠ ⊥ ∧ IsCyclic ↥W₁ ∧ IsCyclic ↥W₂ ∧
        IsInternalDirectProduct (W₁ ⊔ W₂) W₁ W₂ ∧ IsCyclic ↥(W₁ ⊔ W₂) ∧
        FreeCore.IsInternalSemidirectProduct S (⁅S, S⁆ : Subgroup G) W₁ ∧
        FreeCore.IsInternalSemidirectProduct T (⁅T, T⁆ : Subgroup G) W₂ ∧
        S ⊓ T = W₁ ⊔ W₂ ∧
        IsTIWithNormalizer (cyclicTIset W₁ W₂) (W₁ ⊔ W₂) ∧
        (IsTypeII S ∨ IsTypeIII S ∨ IsTypeIV S ∨ IsTypeV S) ∧
        (IsTypeII T ∨ IsTypeIII T ∨ IsTypeIV T ∨ IsTypeV T) ∧
        (IsTypeII S ∨ IsTypeII T) ∧
        ∀ L : Subgroup G, IsCoatom L → ¬ IsTypeI L →
          (∃ g : G, L = conjSubgroup S g) ∨ (∃ g : G, L = conjSubgroup T g)

@[expose]
def FBG_prime_fixed_exceptional_hall_core : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ K : Subgroup G, K ≠ ⊥ → K ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K →
      ¬ Group.IsNilpotent ↥(sigmaCore M) →
    ∀ q : ℕ, q.Prime →
    ∀ Z : Subgroup G, Z = sigmaCore M ⊓ centralizer (K : Set G) → Nat.card ↥Z = q →
      (∀ k ∈ K, k ≠ 1 → sigmaCore M ⊓ centralizer ({k} : Set G) = Z) →
    ∀ H : Subgroup G, H = hallCoreIn M →
      (Nat.card ↥K).Prime ∧ H ≠ ⊥ ∧ H ≤ sigmaCore M ∧ sigmaCore M = ⁅M, M⁆ ∧
        (∃ _ : (H.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal,
          Group.IsNilpotent (↥(⁅M, M⁆ : Subgroup G) ⧸ H.subgroupOf (⁅M, M⁆ : Subgroup G))) ∧
        ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ fittingIn M ∧
        ((fittingIn M : Set G)
          = (H : Set G) * ((M ⊓ centralizer (H : Set G) : Subgroup G) : Set G)) ∧
        fittingIn M < (⁅M, M⁆ : Subgroup G) ∧
        normalizer (fittingRawSharp M) = M ∧
        (∀ g : G, g ∉ M → fittingRawSharp M ∩ conjSet (fittingRawSharp M) g = ∅)

@[expose]
def FBG_rank_two_complement_prime_normalizer_bound : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → (∀ g : G, L ≠ conjSubgroup M g) →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥E → p ∣ Nat.card ↥L → p ∈ tauTwoPrimes L →
    ∀ q : ℕ, q.Prime → q ∈ sigmaPrimes M →
    ∀ Y : Subgroup G, Y ≤ L → Y ≠ ⊥ → IsPGroup q ↥Y →
      elementaryAbelianPRank p ↥(L ⊓ normalizer (Y : Set G)) ≤ 1

@[expose]
def FBG_regular_tau_one_sylow_beta_fixed_points : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ p q : ℕ, p ≠ q → p.Prime → q.Prime → p ∈ tau1Primes M →
    ∀ P : Subgroup G, P ≤ M → Nat.card ↥P = p →
    ∀ Q : Subgroup G, IsSylowSubgroupOf q Q M → Q ≠ ⊥ →
      P ≤ normalizer (Q : Set G) → Q ⊓ centralizer (P : Set G) = ⊥ →
      {T : Subgroup G | IsCoatom T ∧ normalizer (Q : Set G) ≤ T} ≠ {M} →
      alphaPrimes ↥M = betaPrimes ↥M ∧ alphaCoreIn M = betaCore M ∧ betaCore M ≠ ⊥ ∧
        q ∉ betaPrimes ↥M ∧ betaCore M ⊓ centralizer (P : Set G) ≠ ⊥ ∧
        betaCore M ⊓ centralizer ((P : Set G) * (Q : Set G)) = ⊥

@[expose]
def FBG_residual_complement_nilpotent_core : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ K U : Subgroup G, IsHallPiSubgroupOf (kappaPrimes M) K M → U ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K) →
      FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K →
      (U ≠ ⊥ → Group.IsNilpotent ↥(sigmaCore M) ∧ hallCoreIn M = sigmaCore M ∧
        sigmaCore M ≠ ⊥) ∧
      (hallCoreIn M ≠ sigmaCore M → U = ⊥)

@[expose]
def FBG_sigma_complement_abelian_nilpotent : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
      (∀ Q : Subgroup G, Q ≤ M → Group.IsNilpotent ↥Q →
        IsPiSubgroup ((sigmaPrimes M)ᶜ) Q → IsMulCommutative ↥Q) ∧
      (∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        IsMulCommutative ↥(⁅E, E⁆ : Subgroup G))

@[expose]
def FBG_sigma_complement_plane_action_support : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ p : ℕ, p.Prime → p ∉ sigmaPrimes M →
    ∀ A : Subgroup G, A ≤ M → Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p))) →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E → A ≤ E →
    ∀ E₁ E₂ E₃ : Subgroup G, IsHallPiSubgroupOf (tau1Primes M) E₁ E →
      IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E → IsHallPiSubgroupOf (tau3Primes M) E₃ E →
      FreeCore.IsInternalSemidirectProduct E E₃ (E₂ ⊔ E₁) →
      FreeCore.IsInternalSemidirectProduct (E₂ ⊔ E₁) E₂ E₁ →
      (E₂ ⊔ E₃) ≤ E ⊓ centralizer (A : Set G) ∧
        (((E ⊓ centralizer (A : Set G) : Subgroup G)).subgroupOf E).Normal ∧
        ∀ r ∈ ((E ⊓ centralizer (A : Set G) : Subgroup G).relIndex E).primeFactors,
          r ∈ tau1Primes M

@[expose]
def FBG_sigma_conjugate_intersection_cyclic : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ g : G, g ∉ M →
    ∀ X : Subgroup G, X = sigmaCore M ⊓ conjSubgroup M g →
      IsCyclic ↥X ∧ (∀ r ∈ (Nat.card ↥X).primeFactors, r ∉ betaPrimes ↥M) ∧
        X ⊓ (⁅sigmaCore M, sigmaCore M⁆ : Subgroup G) = ⊥

@[expose]
def FBG_sigma_core_nontrivial : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M → (sigmaPrimes M).Nonempty ∧ sigmaCore M ≠ ⊥

@[expose]
def FBG_sigma_core_normal_hall : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
      IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M ∧
        IsHallPiSubgroup (sigmaPrimes M) (sigmaCore M) ∧
        sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)

@[expose]
def FBG_sigma_hall_centralizer_cyclic_complement : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ π : Set ℕ, ∀ H : Subgroup G, H ≠ ⊥ → IsHallPiSubgroupOf π H (sigmaCore M) →
      ∃ X : Subgroup G, X ≤ M ⊓ centralizer (H : Set G) ∧ IsCyclic ↥X ∧
        IsPiSubgroup (tauTwoPrimes M) X ∧
        FreeCore.IsInternalSemidirectProduct (M ⊓ centralizer (H : Set G))
          (sigmaCore M ⊓ centralizer (H : Set G)) X

@[expose]
def FBG_sigma_hall_centralizer_excludes_kappa : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ π : Set ℕ, ∀ H : Subgroup G, H ≠ ⊥ → IsHallPiSubgroupOf π H (sigmaCore M) →
      ∀ r ∈ (Nat.card ↥(M ⊓ centralizer (H : Set G) : Subgroup G)).primeFactors,
        r ∉ kappaPrimes M

@[expose]
def FBG_sigma_intersection_outside_prime_rank_one : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → M ≠ L →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥E → sigmaCore M ⊓ L ≠ ⊥ →
      elementaryAbelianPRank p ↥(M ⊓ L) ≤ 1

@[expose]
def FBG_sigma_prime_normalizer_common_sigma_prime_factor : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
    ∀ q : ℕ, q.Prime → q ∈ sigmaPrimes M →
    ∀ Y : Subgroup G, Y ≤ M → Y ≠ ⊥ → IsPGroup q ↥Y → normalizer (Y : Set G) ≤ T →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥E → p ∉ betaPrimes G → q ∈ sigmaPrimes T →
    ∀ D : Subgroup G, D = pComplCoreIn p (⁅T, T⁆ : Subgroup G) →
      (D.subgroupOf T).Normal ∧ ¬ (p ∣ Nat.card ↥D) ∧
        ((T : Set G) = (D : Set G) * ((M ⊓ T : Subgroup G) : Set G))

@[expose]
def FBG_sigma_prime_normalizer_embedding_sylows : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
    ∀ q : ℕ, q.Prime → q ∈ sigmaPrimes M →
    ∀ Y : Subgroup G, Y ≤ M → Y ≠ ⊥ → IsPGroup q ↥Y → normalizer (Y : Set G) ≤ T →
      (∀ g : G, T ≠ conjSubgroup M g) ∧
        (∀ S : Subgroup G, IsSylowSubgroupOf q S (M ⊓ T) → Y ≤ S →
          normalizer (S : Set G) ≤ M ∧ IsSylowSubgroupOf q S T) ∧
        (q ∈ sigmaPrimes T ∨ q ∈ tauTwoPrimes T)

@[expose]
def FBG_sigma_prime_normalizer_first_prime_embedding : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
    ∀ q : ℕ, q.Prime → q ∈ sigmaPrimes M →
    ∀ Y : Subgroup G, Y ≤ M → Y ≠ ⊥ → IsPGroup q ↥Y → normalizer (Y : Set G) ≤ T →
    ∀ p : ℕ, p.Prime → p ∈ tau1Primes M → p ∈ sigmaPrimes T →
    ∀ P : Subgroup G, P ≤ M ⊓ T → Nat.card ↥P = p →
      q ∈ sigmaPrimes T ∧ alphaCoreIn M ≠ ⊥ ∧ alphaPrimes ↥M = betaPrimes ↥M ∧
        ((T : Set G) = (betaCore T : Set G) * ((M ⊓ T : Subgroup G) : Set G)) ∧
        tau1Primes T ⊆ tau1Primes M ∪ alphaPrimes ↥M

@[expose]
def FBG_sigma_prime_normalizer_narrow_rank_bound : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → (∀ g : G, L ≠ conjSubgroup M g) →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥E → p ∉ betaPrimes G →
    ∀ q : ℕ, q.Prime → q ∈ sigmaPrimes M →
    ∀ Y : Subgroup G, Y ≤ L → Y ≠ ⊥ → IsPGroup q ↥Y →
      elementaryAbelianPRank p ↥(L ⊓ normalizer (Y : Set G)) ≤ 1

@[expose]
def FBG_sigma_prime_normalizer_outside_complement : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
    ∀ q : ℕ, q.Prime → q ∈ sigmaPrimes M →
    ∀ Y : Subgroup G, Y ≤ M → Y ≠ ⊥ → IsPGroup q ↥Y → normalizer (Y : Set G) ≤ T →
      q ∉ sigmaPrimes T →
      q ∈ tauTwoPrimes T ∧ sigmaCore T ⊓ M = ⊥ ∧
        FreeCore.IsInternalSemidirectProduct T (sigmaCore T) (M ⊓ T)

@[expose]
def FBG_sigma_prime_normalizer_outside_narrow_prime_factor : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
    ∀ q : ℕ, q.Prime → q ∈ sigmaPrimes M →
    ∀ Y : Subgroup G, Y ≤ M → Y ≠ ⊥ → IsPGroup q ↥Y → normalizer (Y : Set G) ≤ T →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥E → p ∉ betaPrimes G → q ∉ sigmaPrimes T →
      p ∉ sigmaPrimes T ∧ ¬ (p ∣ Nat.card ↥(sigmaCore T)) ∧
        FreeCore.IsInternalSemidirectProduct T (sigmaCore T) (M ⊓ T)

@[expose]
def FBG_tau_one_fixed_core_transfer : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → (∀ g : G, L ≠ conjSubgroup M g) →
    ∀ p : ℕ, p.Prime → p ∈ tau1Primes M → p ∈ tau1Primes L →
    ∀ P : Subgroup G, P ≤ M ⊓ L → Nat.card ↥P = p →
    ∀ q : ℕ, q.Prime → q ≠ p →
    ∀ Q : Subgroup G, IsSylowSubgroupOf q Q M → Q ≠ ⊥ →
      P ≤ normalizer (Q : Set G) → Q ⊓ centralizer (P : Set G) = ⊥ →
      normalizer (Q : Set G) ≤ L →
    ∀ r : ℕ, r.Prime → r ∈ betaPrimes ↥L →
      r ∣ Nat.card ↥(M ⊓ centralizer (P : Set G) : Subgroup G) →
      sigmaCore M ⊓ centralizer (P : Set G) ≤ L

@[expose]
def FBG_tau_one_intersection_asymmetry : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → (∀ g : G, L ≠ conjSubgroup M g) →
    ∀ p : ℕ, p.Prime → p ∈ tau1Primes M → p ∈ tau1Primes L →
    ∀ P : Subgroup G, P ≤ M ⊓ L → Nat.card ↥P = p →
    ∀ q u : ℕ, q.Prime → u.Prime →
    ∀ Q U : Subgroup G, IsSylowSubgroupOf q Q (M ⊓ L) → IsSylowSubgroupOf u U (M ⊓ L) →
      P ≤ normalizer (Q : Set G) ⊓ normalizer (U : Set G) →
      Q ⊓ centralizer (P : Set G) = ⊥ → U ⊓ centralizer (P : Set G) = ⊥ →
      normalizer (Q : Set G) ≤ L → normalizer (U : Set G) ≤ M →
      False

@[expose]
def FBG_tau_one_intersection_regular_sylow : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → (∀ g : G, L ≠ conjSubgroup M g) →
    ∀ p : ℕ, p.Prime → p ∈ tau1Primes M →
    ∀ P : Subgroup G, P ≤ M ⊓ L → Nat.card ↥P = p →
    ∀ q : ℕ, q.Prime →
    ∀ Q : Subgroup G, IsSylowSubgroupOf q Q (M ⊓ L) →
      P ≤ normalizer (Q : Set G) → Q ⊓ centralizer (P : Set G) = ⊥ →
      normalizer (Q : Set G) ≤ L →
      Q ≠ ⊥ ∧ IsSylowSubgroupOf q Q M ∧ q ≠ p ∧ q ∉ betaPrimes ↥M ∧
        alphaPrimes ↥M = betaPrimes ↥M ∧
        betaCore M ⊓ centralizer (P : Set G) ≠ ⊥ ∧
        betaCore M ⊓ centralizer ((P : Set G) * (Q : Set G)) = ⊥

@[expose]
def FBG_tau_two_ambient_abelian_propagation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ p : ℕ, p ∈ tauTwoPrimes M → (∀ R : Sylow p G, IsMulCommutative ↥(R : Subgroup G)) →
    ∀ q ∈ tauTwoPrimes M, ∀ R : Sylow q G, IsMulCommutative ↥(R : Subgroup G)

@[expose]
def FBG_tau_two_full_central_hall : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ p : ℕ, p ∈ tauTwoPrimes M → (∀ R : Sylow p G, IsMulCommutative ↥(R : Subgroup G)) →
    ∀ E₂ : Subgroup G, IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E →
      E₂ ≤ centerIn (fittingIn E) ∧ IsMulCommutative ↥E₂ ∧ (E₂.subgroupOf E).Normal ∧
        IsHallPiSubgroup (tauTwoPrimes M) E₂

@[expose]
def FBG_tau_two_hall_abelian : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M : Subgroup G, IsCoatom M →
    ∀ E : Subgroup G, FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
    ∀ E₂ : Subgroup G, IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E → IsMulCommutative ↥E₂

@[expose]
def FBG_two_beta_fixed_cores_hall_position : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → (∀ g : G, L ≠ conjSubgroup M g) →
    ∀ P : Subgroup G, P ≤ M ⊓ L → P ≠ ⊥ →
      betaCore M ⊓ centralizer (P : Set G) ≠ ⊥ →
      betaCore L ⊓ centralizer (P : Set G) ≠ ⊥ →
      ∃ M₀ L₀ : Subgroup G, ((M₀ = M ∧ L₀ = L) ∨ (M₀ = L ∧ L₀ = M)) ∧
        ∃ H : Subgroup G, H ≤ (centralizer (P : Set G) ⊓ M₀ : Subgroup G) ∧
        ∃ s r : ℕ, s ∈ betaPrimes ↥M₀ ∧ r ∈ betaPrimes ↥L₀ ∧
          IsHallPiSubgroupOf (betaPrimes ↥M ∪ betaPrimes ↥L) H
            (centralizer (P : Set G)) ∧
          betaCore M₀ ⊓ centralizer (P : Set G) ≤ H ∧
          r ∣ Nat.card ↥H ∧
          pCoreIn s H ≠ ⊥ ∧ ((pCoreIn s H).subgroupOf H).Normal ∧
          pCoreIn s H ≤ betaCore M₀

@[expose]
def FBG_type_II_supporting_maximal_configuration : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M T U V W₁ W₂ : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
      IsWitnessedPConfiguration M U W₁ W₂ → IsWitnessedPConfiguration T V W₂ W₁ →
      IsTypeII M → IsCyclic ↥(W₁ ⊔ W₂) → M ⊓ T = W₁ ⊔ W₂ →
      (∀ L : Subgroup G, IsCoatom L → ¬ IsTypeI L →
        (∃ g : G, L = conjSubgroup M g) ∨ (∃ g : G, L = conjSubgroup T g)) →
    ∀ L : Subgroup G, IsCoatom L → normalizer (U : Set G) ≤ L →
    ∀ P Q H : Subgroup G, P = hallCoreIn M → Q = hallCoreIn T → H = hallCoreIn L →
    ∀ p q : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
      IsTypeI L ∧
      (∃ E : Subgroup G, E ≠ ⊥ ∧
        FreeCore.IsInternalSemidirectProduct L H E ∧
        ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥) ∧
      U ≤ H ∧
      (FreeCore.IsInternalSemidirectProduct L H W₁ ∨
        ∃ y ∈ Q, FreeCore.IsInternalSemidirectProduct L H (W₁ ⊔ conjSubgroup W₂ y))

@[expose]
def FBG_type_II_supporting_maximum_excludes_pair : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M T U V W₁ W₂ : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
      IsWitnessedPConfiguration M U W₁ W₂ → IsWitnessedPConfiguration T V W₂ W₁ →
      IsTypeII M → IsCyclic ↥(W₁ ⊔ W₂) → M ⊓ T = W₁ ⊔ W₂ →
      (∀ L : Subgroup G, IsCoatom L → ¬ IsTypeI L →
        (∃ g : G, L = conjSubgroup M g) ∨ (∃ g : G, L = conjSubgroup T g)) →
    ∀ L : Subgroup G, IsCoatom L → normalizer (U : Set G) ≤ L →
    ∀ P Q H : Subgroup G, P = hallCoreIn M → Q = hallCoreIn T → H = hallCoreIn L →
    ∀ p q : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
      (∀ g : G, L ≠ conjSubgroup M g) ∧ (∀ g : G, L ≠ conjSubgroup T g) ∧ IsTypeI L

@[expose]
def FBG_type_p_fixed_core_normalizer : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      normalizer (W₂ : Set G) = centralizer (W₂ : Set G) ∧
        (centralizer (W₂ : Set G) : Set G) = ((hallCoreIn M : Set G) * (W₁ : Set G)) ∧
        FreeCore.IsInternalSemidirectProduct (hallCoreIn M ⊔ W₁) (hallCoreIn M) W₁

@[expose]
def FCH_actual_paired_support_saturation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ S L U W₁ W₂ : Subgroup G,
    ∀ I J : Type u, ∀ (_ : Fintype I) (_ : Fintype J),
    ∀ (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J),
    ∀ (w : I → J → (↥(W₁ ⊔ W₂) → ℂ)),
    ∀ (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)),
    ∀ (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
      (bfam : J → (↥S → ℂ)),
      IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam →
    ∀ T V₀ : Subgroup G, IsCoatom T → IsWitnessedPConfiguration T V₀ W₂ W₁ →
    ∀ h e p q u v : ℕ, h = Nat.card ↥(hallCoreIn L) → e = hallCoreIndex L →
      p = Nat.card ↥W₂ → q = Nat.card ↥W₁ → u = Nat.card ↥U → v = Nat.card ↥V₀ →
    ∀ ν : (↥L → ℂ) → (G → ℂ), IsCoherentDade L ν →
    ∀ φ ∈ calLFam L, φ 1 = (e : ℂ) →
    ∀ βL : G → ℂ, βL = tauDade L (indBetween (hallCoreIn L) L 1 - φ) →
      e ≤ p * q →
      ((u : ℚ) - 1) / (q : ℚ) < ((h : ℚ) - 1) / (e : ℚ) →
      ((v : ℚ) - 1) / (p : ℚ) < ((h : ℚ) - 1) / (e : ℚ) →
      e = p * q ∧
        ∃ (ε : I → J → ℂ) (χ : G → ℂ),
          (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
          (χ = ν φ ∨ χ = -(ν (fun x => (starRingEnd ℂ) (φ x)))) ∧
          (χ ∈ Irr G ∨ -χ ∈ Irr G) ∧
          βL = (∑ i : I, ∑ j : J, ε i j • η i j) - χ ∧
          ∀ (i : I) (j : J), cfInnerFin χ (η i j) = 0

@[expose]
def FCH_actual_type_I_crossed_control : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ L₁ L₂ : Subgroup G, IsCoatom L₁ → IsCoatom L₂ →
      (∀ g : G, L₂ ≠ conjSubgroup L₁ g) → IsTypeI L₁ → IsTypeI L₂ →
    ∀ h₁ h₂ e₁ e₂ : ℕ, h₁ = Nat.card ↥(hallCoreIn L₁) → h₂ = Nat.card ↥(hallCoreIn L₂) →
      e₁ = hallCoreIndex L₁ → e₂ = hallCoreIndex L₂ →
    ∀ ν₁ : (↥L₁ → ℂ) → (G → ℂ), IsCoherentDade L₁ ν₁ →
    ∀ ν₂ : (↥L₂ → ℂ) → (G → ℂ), IsCoherentDade L₂ ν₂ →
    ∀ φ₁ ∈ calLFam L₁, φ₁ 1 = (e₁ : ℂ) →
    ∀ φ₂ ∈ calLFam L₂, φ₂ 1 = (e₂ : ℂ) →
    ∀ β₁ β₂ : G → ℂ,
      β₁ = tauDade L₁ (indBetween (hallCoreIn L₁) L₁ 1 - φ₁) →
      β₂ = tauDade L₂ (indBetween (hallCoreIn L₂) L₂ 1 - φ₂) →
    ∀ c₁₂ c₂₁ : ℂ, c₁₂ = cfInnerFin β₁ (ν₂ φ₂) → c₂₁ = cfInnerFin β₂ (ν₁ φ₁) →
      dadeSupportDomain L₁ ∩ dadeSupportDomain L₂ = ∅ ∧
      (∀ ξ ∈ calLFam L₁, ∀ ζ ∈ calLFam L₂, cfInnerFin (ν₁ ξ) (ν₂ ζ) = 0) ∧
      (c₁₂ ≠ 0 ∨ c₂₁ ≠ 0) ∧
      (c₁₂ ≠ 0 → ((h₂ : ℚ) - 1) / (e₂ : ℚ) ≤ (e₁ : ℚ) - 1) ∧
      (c₂₁ ≠ 0 → ((h₁ : ℚ) - 1) / (e₁ : ℚ) ≤ (e₂ : ℚ) - 1)

@[expose]
def FCH_paired_fitting_saturations_disjoint : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
    ∀ H F C : Subgroup G, H = hallCoreIn M → F = fittingIn M →
      C = U ⊓ centralizer (H : Set G) →
    ∀ p q u : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ → u = C.relIndex U →
    ∀ N V₀ : Subgroup G, IsCoatom N → N ≠ M → V₀ ≤ N →
      IsWitnessedPConfiguration N V₀ W₂ W₁ →
    ∀ HN FN DN : Subgroup G, HN = hallCoreIn N → FN = fittingIn N →
      DN = V₀ ⊓ centralizer (HN : Set G) →
    ∀ v : ℕ, v = DN.relIndex V₀ →
      (satSet (F : Set G) \ {1}) ∩ (satSet (FN : Set G) \ {1}) = ∅

@[expose]
def FCH_paired_fitting_witness_excludes_partner : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
    ∀ H F C : Subgroup G, H = hallCoreIn M → F = fittingIn M →
      C = U ⊓ centralizer (H : Set G) →
    ∀ p q u : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ → u = C.relIndex U →
    ∀ N V₀ : Subgroup G, IsCoatom N → N ≠ M → V₀ ≤ N →
      IsWitnessedPConfiguration N V₀ W₂ W₁ →
    ∀ HN FN DN : Subgroup G, HN = hallCoreIn N → FN = fittingIn N →
      DN = V₀ ⊓ centralizer (HN : Set G) →
    ∀ v : ℕ, v = DN.relIndex V₀ →
      (∃ ψ : ↥F → ℂ, ψ ∈ Irr ↥F ∧ ψ 1 = 1 ∧ indBetween F M ψ ∈ Irr ↥M ∧
        ¬ (∀ x : ↥M, (x : G) ∈ H → indBetween F M ψ x = indBetween F M ψ 1)) →
      (¬ ∃ φ : ↥FN → ℂ, φ ∈ Irr ↥FN ∧ φ 1 = 1 ∧ indBetween FN N φ ∈ Irr ↥N ∧
        ¬ (∀ x : ↥N, (x : G) ∈ HN → indBetween FN N φ x = indBetween FN N φ 1)) ∧
      DN = ⊥ ∧ FN = HN ∧ Nat.card ↥V₀ = v ∧ (v * (q - 1) = q ^ p - 1) ∧
      (∀ K : Subgroup G, K ≤ HN → (∀ x ∈ V₀, ∀ h ∈ K, x⁻¹ * h * x ∈ K) →
        K = ⊥ ∨ K = HN) ∧
      ∃ (E : Type u) (_ : Field E) (φ : ↥HN ≃* Multiplicative E),
        Nat.card E = q ^ p ∧
        (∀ x ∈ V₀, ∃ a : E, a ≠ 0 ∧ a ^ (∑ i ∈ Finset.range p, q ^ i) = 1 ∧
          ∀ (h : G) (hh : h ∈ HN) (hc : x⁻¹ * h * x ∈ HN),
            Multiplicative.toAdd (φ ⟨x⁻¹ * h * x, hc⟩)
              = a * Multiplicative.toAdd (φ ⟨h, hh⟩)) ∧
        (∀ a : E, a ≠ 0 → a ^ (∑ i ∈ Finset.range p, q ^ i) = 1 →
          ∃ x ∈ V₀, ∀ (h : G) (hh : h ∈ HN) (hc : x⁻¹ * h * x ∈ HN),
            Multiplicative.toAdd (φ ⟨x⁻¹ * h * x, hc⟩)
              = a * Multiplicative.toAdd (φ ⟨h, hh⟩))

@[expose]
def FCH_type_I_P_bridge_orthogonality : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ S L U W₁ W₂ : Subgroup G,
    ∀ I J : Type u, ∀ (_ : Fintype I) (_ : Fintype J),
    ∀ (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J),
    ∀ (w : I → J → (↥(W₁ ⊔ W₂) → ℂ)),
    ∀ (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)),
    ∀ (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
      (bfam : J → (↥S → ℂ)),
      IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam →
    ∀ ν : (↥L → ℂ) → (G → ℂ), IsCoherentDade L ν →
    ∀ φ ∈ calLFam L, φ 1 = (hallCoreIndex L : ℂ) →
    ∀ βL : G → ℂ, βL = tauDade L (indBetween (hallCoreIn L) L 1 - φ) →
      (∀ ξ ∈ calLFam L, ∀ (i : I) (j : J), cfInnerFin (ν ξ) (η i j) = 0) ∧
      (∀ j : J, j ≠ j₀ → ∀ f : ↥L → ℂ, IsClassFun f →
        (∀ x : ↥L, (x : G) ∉ (hallCoreIn L : Set G) \ {1} → f x = 0) →
        cfInnerFin (indTop S (bfam j)) (tauDade L f) = 0)

@[expose]
def FCH_type_I_P_bridge_parity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsOddOrderMinimalSimple G →
    ∀ S L U W₁ W₂ : Subgroup G,
    ∀ I J : Type u, ∀ (_ : Fintype I) (_ : Fintype J),
    ∀ (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J),
    ∀ (w : I → J → (↥(W₁ ⊔ W₂) → ℂ)),
    ∀ (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)),
    ∀ (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
      (bfam : J → (↥S → ℂ)),
      IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam →
    ∀ h e p q u : ℕ, h = Nat.card ↥(hallCoreIn L) → e = hallCoreIndex L →
      p = Nat.card ↥W₂ → q = Nat.card ↥W₁ → u = Nat.card ↥U →
      (∃ ν : (↥L → ℂ) → (G → ℂ), IsCoherentDade L ν) ∧
      (∃ φ ∈ calLFam L, φ 1 = (e : ℂ)) ∧
      ∀ ν : (↥L → ℂ) → (G → ℂ), IsCoherentDade L ν →
      ∀ φ ∈ calLFam L, φ 1 = (e : ℂ) →
      ∀ βL : G → ℂ, βL = tauDade L (indBetween (hallCoreIn L) L 1 - φ) →
      ∀ j₁ : J, j₁ ≠ j₀ →
      ∀ c b : ℂ, c = cfInnerFin (indTop S (bfam j₁)) (ν φ) →
        b = cfInnerFin βL (η i₀ j₁) →
        (∃ m : ℤ, c = (m : ℂ)) ∧ (∃ n : ℤ, b = (n : ℂ)) ∧
        (∀ ξ ∈ calLFam L, ∀ (i : I) (j : J), cfInnerFin (ν ξ) (η i j) = 0) ∧
        (∀ j : J, j ≠ j₀ → cfInnerFin βL (η i₀ j) = b) ∧
        (∀ m n : ℤ, c = (m : ℂ) → b = (n : ℂ) → (Odd m ↔ ¬ Odd n)) ∧
        ((∃ m : ℤ, c = (m : ℂ) ∧ Odd m) ∧ ((h : ℚ) - 1) / (e : ℚ) ≤ ((u : ℚ) - 1) / (q : ℚ) ∨
          (∃ n : ℤ, b = (n : ℂ) ∧ Odd n) ∧ p ≤ e) ∧
        (((u : ℚ) - 1) / (q : ℚ) < ((h : ℚ) - 1) / (e : ℚ) →
          (∀ j : J, j ≠ j₀ → ∃ n : ℤ, cfInnerFin βL (η i₀ j) = (n : ℂ) ∧ Odd n) ∧ p ≤ e)

end Statements

end

end CFSG.FeitThompson
