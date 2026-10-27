module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
public import CFSG.FeitThompson.Definitions.CanonicalCentralizerSignalizerFrom
public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
public import CFSG.FeitThompson.Representations.ProductCharactersFullBasis
public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
public import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
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

open CFSG.FeitThompson Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

namespace Prep06

structure IsMinimalOddSimple (G : Type u) [Group G] : Prop where
  odd : Odd (Nat.card G)
  simple : IsSimpleGroup G
  nonabelian : ¬ IsMulCommutative G
  solvable : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H

variable {G : Type u} [Group G]

@[expose]
def maximalSubgroups (G : Type u) [Group G] : Set (Subgroup G) := {M | IsCoatom M}

@[expose]
def hallCoreIn (M : Subgroup G) : Subgroup G := Subgroup.map M.subtype (hallCore ↥M)

@[expose]
def fittingIn [Finite G] (M : Subgroup G) : Subgroup G :=
  Subgroup.map M.subtype (fittingRaw ↥M)

@[expose]
noncomputable def alphaCoreIn [Finite G] (M : Subgroup G) : Subgroup G :=
  Subgroup.map M.subtype (alphaCore ↥M)

@[expose]
noncomputable def pComplCoreIn [Finite G] (p : ℕ) (X : Subgroup G) : Subgroup G :=
  Subgroup.map X.subtype (pComplCore p ↥X)

@[expose]
def IsSylowIn (p : ℕ) (P X : Subgroup G) : Prop :=
  P ≤ X ∧ Nat.card P = p ^ (Nat.card X).factorization p

@[expose]
def IsHallPiIn (π : Set ℕ) (N X : Subgroup G) : Prop :=
  N ≤ X ∧ (∀ p ∈ (Nat.card N).primeFactors, p ∈ π) ∧
    ∀ p ∈ (N.relIndex X).primeFactors, p ∉ π

@[expose]
noncomputable def supportMult [Finite G] (x : G) : ℕ :=
  supportMultiplicity (maximalSubgroups G) sigmaCore x

@[expose]
noncomputable def sigSignalizer [Finite G] (x : G) : Subgroup G :=
  canonicalSignalizer (maximalSubgroups G) sigmaCore x

@[expose]
noncomputable def sigDelta [Finite G] (M : Subgroup G) : Set G :=
  ⋃ x ∈ (sigmaCore M : Set G) \ {1}, ⋃ g : G,
    (fun y => g⁻¹ * y * g) '' ((fun r => x * r) '' (sigSignalizer x : Set G))

open scoped Classical in
@[expose]
noncomputable def dadeT [Finite G] (M : Subgroup G) (a : G) : Subgroup G :=
  if a ∈ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1} then sigSignalizer a else ⊥

@[expose]
def mixedConj (M W₁ W₂ : Subgroup G) : Set G :=
  ⋃ m ∈ (M : Set G), (fun x => m⁻¹ * x * m) '' cyclicTIset W₁ W₂

@[expose]
def dadeA0 (M W₁ W₂ : Subgroup G) : Set G :=
  (((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) ∪ mixedConj M W₁ W₂

@[expose]
noncomputable def dadeTau [Finite G] (M W₁ W₂ : Subgroup G) (f : ↥M → ℂ) : G → ℂ :=
  dadeMapFun M (dadeA0 M W₁ W₂) (dadeT M) f

@[expose]
noncomputable def dadeDeltaM [Finite G] (M : Subgroup G) : Set G :=
  totalDadeSupport (((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) (dadeT M)

@[expose]
def derivedOf (M : Subgroup G) : Subgroup ↥M := commutator ↥M

open scoped Classical in
@[expose]
noncomputable def indFamNonprincipal [Fintype G] (M : Subgroup G) (K : Subgroup ↥M) :
    Set (↥M → ℂ) := indFam K (nonprincipalIrr ↥K)

open scoped Classical in
@[expose]
noncomputable def indFamKer [Fintype G] (M : Subgroup G) (K A : Subgroup ↥M) : Set (↥M → ℂ) :=
  indFam K {θ ∈ nonprincipalIrr ↥K | ∀ x : ↥K, (x : ↥M) ∈ A → θ x = θ 1}

open scoped Classical in
@[expose]
noncomputable def indFamDetectKer [Fintype G] (M : Subgroup G) (K C H : Subgroup ↥M) :
    Set (↥M → ℂ) :=
  indFam K {θ ∈ irrChar ℂ ↥K | (∀ x : ↥K, (x : ↥M) ∈ C → θ x = θ 1) ∧
    ∃ x : ↥K, (x : ↥M) ∈ H ∧ θ x ≠ θ 1}

open scoped Classical in
@[expose]
noncomputable def HasCoherentMap [Fintype G] (M W₁ W₂ : Subgroup G) (S : Set (↥M → ℂ)) : Prop :=
  ∃ ν : ↥(Submodule.span ℤ S) →+ ↥(virtualChars G),
    (∀ f g : ↥(Submodule.span ℤ S),
      cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥M → ℂ) (g : ↥M → ℂ)) ∧
    ∀ f : ↥(Submodule.span ℤ S), (f : ↥M → ℂ) 1 = 0 →
      (ν f : G → ℂ) = dadeTau M W₁ W₂ (f : ↥M → ℂ)

open scoped Classical in
structure IsRowData [Fintype G] (M W₁ W₂ : Subgroup G)
    (σ : ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) →ₗ[ℂ] ↥(classFun ↥M))
    (w : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) →
      ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)))
    (l : ↑(Irr ↥(W₁.subgroupOf M)) → ↥M → ℂ) : Prop where
  isometry : IsCyclicTIIsometry (W₁.subgroupOf M ⊔ W₂.subgroupOf M)
    (W₁.subgroupOf M) (W₂.subgroupOf M) σ
  prod : ∀ i j (x : ↥(W₁.subgroupOf M)) (y : ↥(W₂.subgroupOf M))
    (z : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)), (z : ↥M) = (x : ↥M) * (y : ↥M) →
      (w i j : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) → ℂ) z =
        (i : ↥(W₁.subgroupOf M) → ℂ) x * (j : ↥(W₂.subgroupOf M) → ℂ) y
  infl : ∀ i (k : ↥(derivedOf M)) (v : ↥(W₁.subgroupOf M)) (z : ↥M),
    z = (k : ↥M) * (v : ↥M) → l i z = (i : ↥(W₁.subgroupOf M) → ℂ) v

open scoped Classical in
structure IsRowSetup [Fintype G] (M W₁ W₂ : Subgroup G)
    (σ : ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) →ₗ[ℂ] ↥(classFun ↥M))
    (w : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) →
      ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)))
    (l : ↑(Irr ↥(W₁.subgroupOf M)) → ↥M → ℂ)
    (δ : ↑(Irr ↥(W₂.subgroupOf M)) → ℂ)
    (μ : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) → ↥M → ℂ) : Prop
    extends IsRowData M W₁ W₂ σ w l where
  sign : ∀ j, δ j = 1 ∨ δ j = -1
  mu_zero_mem : ∀ j, δ j • (σ (w (principalIrr ↥(W₁.subgroupOf M)) j) : ↥M → ℂ) ∈ Irr ↥M
  mu_eq : ∀ i j, μ i j =
    l i * (δ j • (σ (w (principalIrr ↥(W₁.subgroupOf M)) j) : ↥M → ℂ))

open scoped Classical in
structure IsEtaSetup [Fintype G] (W₁ W₂ : Subgroup G)
    (ω : ↥(classFun ↥(W₁ ⊔ W₂)) →ₗ[ℂ] ↥(classFun G))
    (w : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → ↥(classFun ↥(W₁ ⊔ W₂)))
    (η : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → G → ℂ) : Prop where
  isometry : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω
  prod : ∀ i j (x : ↥W₁) (y : ↥W₂) (z : ↥(W₁ ⊔ W₂)), (z : G) = (x : G) * (y : G) →
    (w i j : ↥(W₁ ⊔ W₂) → ℂ) z = (i : ↥W₁ → ℂ) x * (j : ↥W₂ → ℂ) y
  eta_eq : ∀ i j, η i j = (ω (w i j) : G → ℂ)

@[expose]
def SupportedOn (D : Set G) (f : G → ℂ) : Prop := ∀ g : G, g ∉ D → f g = 0

theorem mem_maximalSubgroups_iff {M : Subgroup G} : M ∈ maximalSubgroups G ↔ IsCoatom M := Iff.rfl

theorem hallCoreIn_eq (M : Subgroup G) :
    hallCoreIn M = Subgroup.map M.subtype (hallCore ↥M) := (rfl)

theorem hallCoreIn_le (M : Subgroup G) : hallCoreIn M ≤ M := Subgroup.map_subtype_le _

theorem fittingIn_eq [Finite G] (M : Subgroup G) :
    fittingIn M = Subgroup.map M.subtype (fittingRaw ↥M) := (rfl)

theorem fittingIn_le [Finite G] (M : Subgroup G) : fittingIn M ≤ M := Subgroup.map_subtype_le _

theorem alphaCoreIn_eq [Finite G] (M : Subgroup G) :
    alphaCoreIn M = Subgroup.map M.subtype (alphaCore ↥M) := (rfl)

theorem alphaCoreIn_le [Finite G] (M : Subgroup G) : alphaCoreIn M ≤ M := Subgroup.map_subtype_le _

theorem pComplCoreIn_eq [Finite G] (p : ℕ) (X : Subgroup G) :
    pComplCoreIn p X = Subgroup.map X.subtype (pComplCore p ↥X) := (rfl)

theorem pComplCoreIn_le [Finite G] (p : ℕ) (X : Subgroup G) : pComplCoreIn p X ≤ X :=
  Subgroup.map_subtype_le _

theorem isSylowIn_iff {p : ℕ} {P X : Subgroup G} :
    IsSylowIn p P X ↔ P ≤ X ∧ Nat.card P = p ^ (Nat.card X).factorization p := Iff.rfl

theorem isHallPiIn_iff {π : Set ℕ} {N X : Subgroup G} :
    IsHallPiIn π N X ↔ N ≤ X ∧ (∀ p ∈ (Nat.card N).primeFactors, p ∈ π) ∧
      ∀ p ∈ (N.relIndex X).primeFactors, p ∉ π := Iff.rfl

theorem supportMult_eq [Finite G] (x : G) :
    supportMult x = supportMultiplicity (maximalSubgroups G) sigmaCore x := (rfl)

theorem sigSignalizer_eq [Finite G] (x : G) :
    sigSignalizer x = canonicalSignalizer (maximalSubgroups G) sigmaCore x := (rfl)

theorem sigSignalizer_le_centralizer [Finite G] (x : G) :
    sigSignalizer x ≤ Subgroup.centralizer ({x} : Set G) :=
  canonicalSignalizer_le_centralizer

theorem sigDelta_eq [Finite G] (M : Subgroup G) :
    sigDelta M = ⋃ x ∈ (sigmaCore M : Set G) \ {1}, ⋃ g : G,
      (fun y => g⁻¹ * y * g) '' ((fun r => x * r) '' (sigSignalizer x : Set G)) := (rfl)

open scoped Classical in
theorem dadeT_of_mem [Finite G] {M : Subgroup G} {a : G}
    (ha : a ∈ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) : dadeT M a = sigSignalizer a :=
  if_pos ha

open scoped Classical in
theorem dadeT_of_notMem [Finite G] {M : Subgroup G} {a : G}
    (ha : a ∉ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) : dadeT M a = ⊥ :=
  if_neg ha

theorem mixedConj_eq (M W₁ W₂ : Subgroup G) :
    mixedConj M W₁ W₂ = ⋃ m ∈ (M : Set G), (fun x => m⁻¹ * x * m) '' cyclicTIset W₁ W₂ := (rfl)

theorem dadeA0_eq (M W₁ W₂ : Subgroup G) :
    dadeA0 M W₁ W₂ = (((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) ∪ mixedConj M W₁ W₂ := (rfl)

theorem sdiff_subset_dadeA0 (M W₁ W₂ : Subgroup G) :
    ((⁅M, M⁆ : Subgroup G) : Set G) \ {1} ⊆ dadeA0 M W₁ W₂ := Set.subset_union_left

theorem dadeTau_eq [Finite G] (M W₁ W₂ : Subgroup G) (f : ↥M → ℂ) :
    dadeTau M W₁ W₂ f = dadeMapFun M (dadeA0 M W₁ W₂) (dadeT M) f := (rfl)

theorem dadeDeltaM_eq [Finite G] (M : Subgroup G) :
    dadeDeltaM M = totalDadeSupport (((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) (dadeT M) := (rfl)

theorem derivedOf_eq (M : Subgroup G) : derivedOf M = commutator ↥M := (rfl)

theorem map_subtype_derivedOf (M : Subgroup G) :
    Subgroup.map M.subtype (derivedOf M) = ⁅M, M⁆ := Subgroup.map_subtype_commutator M

open scoped Classical in
theorem indFamNonprincipal_eq [Fintype G] (M : Subgroup G) (K : Subgroup ↥M) :
    indFamNonprincipal M K = indFam K (nonprincipalIrr ↥K) := (rfl)

open scoped Classical in
theorem indFamKer_eq [Fintype G] (M : Subgroup G) (K A : Subgroup ↥M) :
    indFamKer M K A =
      indFam K {θ ∈ nonprincipalIrr ↥K | ∀ x : ↥K, (x : ↥M) ∈ A → θ x = θ 1} := (rfl)

open scoped Classical in
theorem indFamKer_subset_indFamNonprincipal [Fintype G] (M : Subgroup G) (K A : Subgroup ↥M) :
    indFamKer M K A ⊆ indFamNonprincipal M K := by
  rw [indFamKer_eq, indFamNonprincipal_eq]
  exact indFam_mono (K := K) (fun _ hθ => hθ.1)

open scoped Classical in
theorem indFamDetectKer_eq [Fintype G] (M : Subgroup G) (K C H : Subgroup ↥M) :
    indFamDetectKer M K C H =
      indFam K {θ ∈ irrChar ℂ ↥K | (∀ x : ↥K, (x : ↥M) ∈ C → θ x = θ 1) ∧
        ∃ x : ↥K, (x : ↥M) ∈ H ∧ θ x ≠ θ 1} := (rfl)

open scoped Classical in
theorem hasCoherentMap_iff [Fintype G] {M W₁ W₂ : Subgroup G} {S : Set (↥M → ℂ)} :
    HasCoherentMap M W₁ W₂ S ↔
      ∃ ν : ↥(Submodule.span ℤ S) →+ ↥(virtualChars G),
        (∀ f g : ↥(Submodule.span ℤ S),
          cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥M → ℂ) (g : ↥M → ℂ)) ∧
        ∀ f : ↥(Submodule.span ℤ S), (f : ↥M → ℂ) 1 = 0 →
          (ν f : G → ℂ) = dadeTau M W₁ W₂ (f : ↥M → ℂ) := Iff.rfl

theorem supportedOn_iff {D : Set G} {f : G → ℂ} :
    SupportedOn D f ↔ ∀ g : G, g ∉ D → f g = 0 := Iff.rfl

theorem supportedOn_zero (D : Set G) : SupportedOn D (0 : G → ℂ) := fun _ _ => rfl

theorem SupportedOn.mono {D E : Set G} {f : G → ℂ} (h : SupportedOn D f) (hDE : D ⊆ E) :
    SupportedOn E f := fun g hg => h g fun hgD => hg (hDE hgD)

end Prep06

namespace Statements

open Prep06

@[expose]
def FPF_type_iii_iv_core_centralizer_derived : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G) = ⁅U, U⁆

@[expose]
def FPF_type_iii_iv_core_elementary_chief_kernel_trivial : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      Nonempty (↥(hallCoreIn M) ≃*
          (Fin (Nat.card W₁) → Multiplicative (ZMod (Nat.card W₂)))) ∧
        Nat.card (hallCoreIn M) = Nat.card W₂ ^ Nat.card W₁ ∧
        ⁅hallCoreIn M, hallCoreIn M⁆ = ⊥ ∧
        hallCoreIn M ⊓ centralizer (U : Set G) = ⊥ ∧
        (∀ H₀ : Subgroup G, H₀ ≤ hallCoreIn M → M ≤ normalizer (H₀ : Set G) →
          hallCoreIn M ⊓ centralizer (U : Set G) ≤ H₀ → H₀ < hallCoreIn M →
          (∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) →
            ¬ (H₀ < H₁ ∧ H₁ < hallCoreIn M)) → H₀ = ⊥) ∧
        U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G) = ⁅U, U⁆ ∧
        ∃ hN : ((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf U).Normal,
          letI := hN
          Nontrivial (↥U ⧸ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf U) ∧
            IsMulCommutative
              (↥U ⧸ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf U)

@[expose]
def FPF_type_iii_iv_core_is_prime_group : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∃ a : ℕ, 1 ≤ a ∧ Nat.card (hallCoreIn M) = Nat.card W₂ ^ a

@[expose]
def FPF_type_iii_iv_inner_complement_cyclic : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      IsCyclic ↥U ∧ Nat.card W₂ < Nat.card W₁ ∧ IsTypeIII M

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_iv_principal_row_projection : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ σ w l δ μ, IsRowSetup M W₁ W₂ σ w l δ μ →
      ∀ ω wG η, IsEtaSetup W₁ W₂ ω wG η →
      (∀ ζ ∈ indFamKer M (derivedOf M)
          (((hallCoreIn M ⊔ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G))
            : Subgroup G)).subgroupOf M),
        ∀ (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)),
          cfInner (dadeTau M W₁ W₂
              ((∑ᶠ i' : ↑(Irr ↥(W₁.subgroupOf M)), μ i' (principalIrr ↥(W₂.subgroupOf M))) - ζ)
            - ∑ᶠ j' : ↑(Irr ↥W₂), η (principalIrr ↥W₁) j') (η i j) = 0) ∧
        Nat.card W₂ < Nat.card W₁

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_iv_proper_coherent_index_bound : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ H₀ : Subgroup G, M ≤ normalizer (H₀ : Set G) →
        hallCoreIn M ⊓ centralizer (U : Set G) ≤ H₀ → H₀ < hallCoreIn M →
        (∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) →
          ¬ (H₀ < H₁ ∧ H₁ < hallCoreIn M)) →
      ∀ N : Subgroup G, M ≤ normalizer (N : Set G) → N < ⁅M, M⁆ →
        HasCoherentMap M W₁ W₂ (indFamKer M (derivedOf M) (N.subgroupOf M)) →
        N.relIndex (⁅M, M⁆ : Subgroup G) ≤
          2 * Nat.card W₁ *
            (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U + 1

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_iv_row_degree_and_kernel : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ σ w l δ μ, IsRowSetup M W₁ W₂ σ w l δ μ →
      ∀ d n : ℕ, ∀ dsign : ℂ,
        (∀ i j, j ≠ principalIrr ↥(W₂.subgroupOf M) → μ i j 1 = (d : ℂ)) →
        (∀ j, j ≠ principalIrr ↥(W₂.subgroupOf M) → δ j = dsign) →
        (d : ℂ) - dsign = (n : ℂ) * (Nat.card W₁ : ℂ) →
      (∀ j : ↑(Irr ↥(W₂.subgroupOf M)), j ≠ principalIrr ↥(W₂.subgroupOf M) →
        resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j) ∈ Irr ↥(derivedOf M) ∧
        (∀ x : ↥(derivedOf M),
          (x : ↥M) ∈ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf M →
          resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j) x =
            resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j) 1) ∧
        (∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCoreIn M).subgroupOf M ∧
          resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j) x ≠
            resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j) 1) ∧
        resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j) 1 =
          (((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U : ℕ) : ℂ) ∧
        (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), μ i j) =
          indClassFun (derivedOf M)
            (resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j)) ∧
        (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), μ i j) 1 =
          ((Nat.card W₁ : ℂ)) *
            (((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U : ℕ) : ℂ) ∧
        cfInner (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), μ i j)
          (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), μ i j) = (Nat.card W₁ : ℂ)) ∧
      1 < (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U ∧
      Nat.card W₁ ∣ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U - 1 ∧
      d = (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U ∧
      dsign = 1 ∧
      n * Nat.card W₁ =
        (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U - 1

@[expose]
def FPF_type_iii_iv_scalar_coordinate_index_collapse : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ E : Fin (Nat.card W₁) → Subgroup G, ∀ a : ℕ, ∀ b : G,
        (∀ i, E i ≤ hallCoreIn M) →
        (∀ i, Nat.card (E i) = Nat.card W₂) →
        (⨆ i, E i) = hallCoreIn M →
        (∀ i, E i ⊓ (⨆ j ∈ ({i}ᶜ : Set (Fin (Nat.card W₁))), E j) = ⊥) →
        (∀ i, U ≤ normalizer ((E i : Subgroup G) : Set G)) →
        (b ∈ W₁ ∧ zpowers b = W₁) →
        (∀ i : Fin (Nat.card W₁),
          Subgroup.map (MulAut.conj b⁻¹ : G ≃* G) (E i) = E (i + 1)) →
        (∀ (i : Fin (Nat.card W₁)) (x : G), x ∈ U → ∃ m : ℕ,
          ∀ y ∈ E i, x⁻¹ * y * x = y ^ m) →
        1 < a →
        (∀ i, (U ⊓ centralizer ((E i : Subgroup G) : Set G)).relIndex U = a) →
        (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U = a

@[expose]
def FPF_type_iii_iv_second_derived_fitting : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ = fittingIn M ∧
        hallCoreIn M ⊔ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)) = fittingIn M ∧
        hallCoreIn M ⊓ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)) = ⊥ ∧
        ⁅hallCoreIn M, U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)⁆ = ⊥

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_iv_two_coherent_layers : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ C : Subgroup G, C = U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G) →
      ∀ S₁ S₂ : Set (↥M → ℂ),
        S₁ = indFamKer M (derivedOf M) ((hallCoreIn M ⊔ C : Subgroup G).subgroupOf M) →
        S₂ = indFamDetectKer M (derivedOf M) (C.subgroupOf M) ((hallCoreIn M).subgroupOf M) →
      (hallCoreIn M ⊔ C = ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ∧
        C = ⁅U, U⁆ ∧ M ≤ normalizer (C : Set G) ∧
        Disjoint S₁ S₂ ∧ (∀ f ∈ S₁, star f ∈ S₁) ∧ (∀ f ∈ S₂, star f ∈ S₂) ∧
        S₁ ∪ S₂ = indFamKer M (derivedOf M) (C.subgroupOf M) ∧
        HasCoherentMap M W₁ W₂ S₁ ∧ HasCoherentMap M W₁ W₂ S₂ ∧
        ¬ HasCoherentMap M W₁ W₂ (S₁ ∪ S₂) ∧
        S₁ ⊆ Irr ↥M ∧ (∀ f ∈ S₁, f 1 = (Nat.card W₁ : ℂ)) ∧
        ∃ n : ℕ, Nat.card S₁ = n ∧ Even n ∧ 2 ≤ n ∧
          n * Nat.card W₁ = (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U - 1)

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_iv_weighted_normal_family : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ S : Set (↥M → ℂ), S = indFamNonprincipal M (derivedOf M) →
      ((∀ f ∈ S, f ≠ 0 ∧ IsCharacter ↥M f) ∧
        (∀ f ∈ S, star f ∈ S) ∧ (∀ f ∈ S, star f ≠ f) ∧
        (∀ f ∈ S, ∀ g ∈ S, f ≠ g → cfInner f g = 0) ∧
        (∀ f ∈ Submodule.span ℤ S, ∀ g ∈ Submodule.span ℤ S, f 1 = 0 → g 1 = 0 →
          dadeTau M W₁ W₂ (f + g) = dadeTau M W₁ W₂ f + dadeTau M W₁ W₂ g ∧
            cfInner (dadeTau M W₁ W₂ f) (dadeTau M W₁ W₂ g) = cfInner f g ∧
            dadeTau M W₁ W₂ f 1 = 0 ∧
            dadeTau M W₁ W₂ f ∈ virtualChars G) ∧
        (∃ R : (↥M → ℂ) → Set (G → ℂ),
          (∀ f ∈ S, (R f).Finite ∧ R f ⊆ (virtualChars G : Set (G → ℂ)) ∧
            (∀ r ∈ R f, ∀ s ∈ R f, cfInner r s = if r = s then 1 else 0) ∧
            dadeTau M W₁ W₂ (f - star f) = ∑ᶠ r ∈ R f, r) ∧
          ∀ f ∈ S, ∀ g ∈ S, g ≠ f → g ≠ star f →
            ∀ r ∈ R f, ∀ s ∈ R g, cfInner r s = 0) ∧
        ¬ HasCoherentMap M W₁ W₂ S)

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_v_coherence_forces_frobenius_partner : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M)) →
      ∀ N E : Subgroup G, IsCoatom N → IsTypeII N →
        IsWitnessedPConfiguration N E W₂ W₁ →
        ∀ e ∈ E, e ≠ 1 → hallCoreIn N ⊓ centralizer ({e} : Set G) = ⊥

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_v_coherent_crossed_row_data : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M)) →
      ∀ ω wG η, IsEtaSetup W₁ W₂ ω wG η →
      ∃ d : ℕ, ∃ δ : ℂ, ∃ ρ : G → ℂ,
        1 < d ∧ (δ = 1 ∨ δ = -1) ∧ ρ ∈ signedIrr G ∧ star ρ ≠ ρ ∧
          (∀ i j, cfInner ρ (η i j) = 0) ∧
          SupportedOn (dadeDeltaM M) (ρ - star ρ) ∧
          ∀ j : ↑(Irr ↥W₂), j ≠ principalIrr ↥W₂ →
            SupportedOn (dadeDeltaM M)
              (δ • (∑ᶠ i : ↑(Irr ↥W₁), η i j) - (d : ℂ) • ρ)

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_v_extended_dade_support : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      (dadeA0 M W₁ W₂ ⊆ (M : Set G) \ {1}) ∧
        (∀ a ∈ dadeA0 M W₁ W₂, ∀ m ∈ M, m⁻¹ * a * m ∈ dadeA0 M W₁ W₂) ∧
        (∀ a ∈ dadeA0 M W₁ W₂, ∀ b ∈ dadeA0 M W₁ W₂, IsConj a b →
          ∃ m ∈ M, m⁻¹ * a * m = b) ∧
        IsDadeData M (dadeA0 M W₁ W₂) (dadeT M) ∧
        (∀ f g : ↥M → ℂ, f ∈ classFun ↥M → g ∈ classFun ↥M →
          (∀ x : ↥M, (x : G) ∉ dadeA0 M W₁ W₂ → f x = 0) →
          (∀ x : ↥M, (x : G) ∉ dadeA0 M W₁ W₂ → g x = 0) →
          dadeTau M W₁ W₂ (f + g) = dadeTau M W₁ W₂ f + dadeTau M W₁ W₂ g ∧
            (∀ c : ℂ, dadeTau M W₁ W₂ (c • f) = c • dadeTau M W₁ W₂ f) ∧
            cfInner (dadeTau M W₁ W₂ f) (dadeTau M W₁ W₂ g) = cfInner f g ∧
            (f ∈ virtualChars ↥M → dadeTau M W₁ W₂ f ∈ virtualChars G) ∧
            dadeTau M W₁ W₂ f ∈ classFun G)

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_v_frobenius_partner_contradiction : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ N E : Subgroup G, IsCoatom N → IsTypeII N →
        IsWitnessedPConfiguration N E W₂ W₁ →
        (∀ e ∈ E, e ≠ 1 → hallCoreIn N ⊓ centralizer ({e} : Set G) = ⊥) →
        ¬ HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M))

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_v_induced_family_noncoherence : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ¬ HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M))

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_v_local_character_constants : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      (∃ σ : ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) →ₗ[ℂ] ↥(classFun ↥M),
          IsCyclicTIIsometry (W₁.subgroupOf M ⊔ W₂.subgroupOf M)
            (W₁.subgroupOf M) (W₂.subgroupOf M) σ) ∧
        (∀ σ w l, IsRowData M W₁ W₂ σ w l →
          ∀ j : ↑(Irr ↥(W₂.subgroupOf M)),
            ∃! s : ℂ, (s = 1 ∨ s = -1) ∧
              s • (σ (w (principalIrr ↥(W₁.subgroupOf M)) j) : ↥M → ℂ) ∈ Irr ↥M) ∧
        ∀ σ w l δ μ, IsRowSetup M W₁ W₂ σ w l δ μ →
          ∃ d n : ℕ, ∃ dsign : ℂ, Odd d ∧ 1 < d ∧ (dsign = 1 ∨ dsign = -1) ∧
            Even n ∧ 2 ≤ n ∧
            (∀ i j, j ≠ principalIrr ↥(W₂.subgroupOf M) → μ i j 1 = (d : ℂ)) ∧
            (∀ j, j ≠ principalIrr ↥(W₂.subgroupOf M) → δ j = dsign) ∧
            (d : ℂ) - dsign = (n : ℂ) * (Nat.card W₁ : ℂ)

@[expose]
def FPF_type_iii_v_second_factor_prime : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) →
      IsWitnessedPConfiguration M U W₁ W₂ → (Nat.card W₂).Prime

open scoped Classical in
@[expose]
noncomputable def FPF_type_iii_v_type_ii_support_disjoint : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N →
      (IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) → IsTypeII N →
      ∀ B_N D_N : Set G,
        B_N = {a | a ∈ ((⁅N, N⁆ : Subgroup G) : Set G) \ {1} ∧
          hallCoreIn N ⊓ centralizer ({a} : Set G) ≠ ⊥} →
        D_N = ⋃ g : G, (fun x => g⁻¹ * x * g) '' B_N →
        dadeDeltaM M ∩ D_N = ∅ ∧
          ∀ f h : G → ℂ, SupportedOn (dadeDeltaM M) f → SupportedOn D_N h → cfInner f h = 0

@[expose]
def FPF_type_v_exclusion : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M : Subgroup G, IsCoatom M → ¬ IsTypeV M

@[expose]
def FPL_global_maximal_plane_geometry : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ p : ℕ, p.Prime → Odd p →
    ∀ A P : Subgroup G,
      Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p))) →
      (∀ A' : Subgroup G, A < A' → ∀ d : ℕ,
        ¬ Nonempty (↥A' ≃* (Fin d → Multiplicative (ZMod p)))) →
      (∃ n : ℕ, Nat.card P = p ^ n) → A ≤ P → ¬ IsMulCommutative ↥P →
      ∀ Z₀ : Set G, Z₀ = {z | z ∈ P ⊓ centralizer (P : Set G) ∧ z ^ p = 1} →
        ∃ Z₀' : Subgroup G, (Z₀' : Set G) = Z₀ ∧ Z₀' ≤ A ∧ Nat.card Z₀' = p ∧
          (∃ Y : Subgroup G, Y ≤ P ⊓ centralizer (A : Set G) ∧ IsCyclic ↥Y ∧ Z₀' ≤ Y ∧
            ∀ A₀ : Subgroup G, A₀ ≤ A → Nat.card A₀ = p → A₀ ≠ Z₀' →
              A₀ ⊔ Y = P ⊓ centralizer (A : Set G) ∧ A₀ ⊓ Y = ⊥ ∧ ⁅A₀, Y⁆ = ⊥) ∧
          ∀ A₀ A₁ : Subgroup G, A₀ ≤ A → A₁ ≤ A → Nat.card A₀ = p → Nat.card A₁ = p →
            A₀ ≠ Z₀' → A₁ ≠ Z₀' →
            ∃ g ∈ P ⊓ normalizer (A : Set G), Subgroup.map (MulAut.conj g⁻¹ : G ≃* G) A₀ = A₁

@[expose]
def FPL_global_sylow_complement_generation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≠ ⊥ → IsSylowIn p P ⊤ →
      ∀ L : Subgroup G, L = normalizer (P : Set G) →
        (∃ V : Subgroup G, V ≤ L ∧ ¬ p ∣ Nat.card V ∧ ∃ k : ℕ, V.relIndex L = p ^ k) ∧
          ∀ V : Subgroup G, V ≤ L → ¬ p ∣ Nat.card V → (∃ k : ℕ, V.relIndex L = p ^ k) →
            P ⊔ V = L ∧ P ⊓ V = ⊥ ∧ ⁅P, V⁆ = P ∧
              Odd (Nat.card (V ⧸ (V ⊓ centralizer (P : Set G)).subgroupOf V)) ∧
              ¬ p ∣ Nat.card (V ⧸ (V ⊓ centralizer (P : Set G)).subgroupOf V)

@[expose]
def FPL_global_sylow_normalizer_derived : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≠ ⊥ → IsSylowIn p P ⊤ →
      P ≤ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆

@[expose]
def FPL_low_rank_sylow_central_product : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ p : ℕ, p.Prime → Odd p → ∀ R : Subgroup G, IsSylowIn p R ⊤ →
      elementaryAbelianPRank p ↥R ≤ 2 → ¬ IsMulCommutative ↥R →
      ∃ B C : Subgroup G, B ≤ R ∧ C ≤ R ∧ B ⊔ C = R ∧
        Nat.card B = p ^ 3 ∧ ¬ IsMulCommutative ↥B ∧ (∀ b ∈ B, b ^ p = 1) ∧
        C ≠ ⊥ ∧ IsCyclic ↥C ∧ C ≤ R ⊓ centralizer (R : Set G) ∧
        B ⊓ C = B ⊓ centralizer (B : Set G) ∧
        ((B ⊓ C : Subgroup G) : Set G) = {c | c ∈ C ∧ c ^ p = 1} ∧
        Nat.card (B ⊓ C : Subgroup G) = p

@[expose]
def FT_no_minimal_odd_simple : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], ¬ IsMinimalOddSimple G

@[expose]
def FT_odd_order_solvable : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → Group.IsSolvable G

@[expose]
def FTS_abelian_rank_two_hall_centralizer_uniqueness : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M E E₂ : Subgroup G, M ∈ maximalSubgroups G →
      E ≤ M → sigmaCore M ⊔ E = M → sigmaCore M ⊓ E = ⊥ →
      E₂ ≤ E → IsMulCommutative ↥E₂ → IsHallPiIn (tauTwoPrimes M) E₂ E →
      ∀ X : Subgroup G, X ≤ E₂ → X ≠ ⊥ → sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥ →
        centralizer (X : Set G) ≤ M ∧
          IsUniqueMaximalOvergroup (centralizer (X : Set G)) M

@[expose]
def FTS_admissible_tau_one_displacement_contradiction : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M E : Subgroup G, M ∈ maximalSubgroups G →
      E ≤ M → sigmaCore M ⊔ E = M → sigmaCore M ⊓ E = ⊥ →
      ∀ p r q a : ℕ, p.Prime → r.Prime → q.Prime → p ∈ tau1Primes M →
      ∀ P R V T : Subgroup G,
        P ≤ E → Nat.card P = p →
        R ≤ E ⊓ centralizer (P : Set G) → Nat.card R = r →
        V ≤ sigmaCore M ⊓ centralizer (P : Set G) → Nat.card V = q ^ a →
        R ≤ normalizer (V : Set G) →
        ⁅V, R⁆ ≠ ⊥ →
        T ∈ maximalSubgroups G → normalizer (P : Set G) ≤ T →
        (r ∈ tau1Primes M →
          alphaCoreIn M ⊓ centralizer (P : Set G) ≤ alphaCoreIn M ⊓ centralizer (R : Set G) →
          alphaCoreIn M ⊓ centralizer (P : Set G) = alphaCoreIn M ⊓ centralizer (R : Set G)) →
        (q ∈ alphaPrimes ↥M ∨
          alphaCoreIn M ⊓ centralizer (P : Set G) ≤
            alphaCoreIn M ⊓ centralizer (R : Set G)) →
        False

@[expose]
def FTS_admissible_tau_one_prime_centralizer_inclusion : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M E : Subgroup G, M ∈ maximalSubgroups G →
      E ≤ M → sigmaCore M ⊔ E = M → sigmaCore M ⊓ E = ⊥ →
      ∀ p r : ℕ, p.Prime → r.Prime → p ∈ tau1Primes M →
      ∀ P R : Subgroup G,
        P ≤ E → Nat.card P = p →
        R ≤ E ⊓ centralizer (P : Set G) → Nat.card R = r →
        (r ∈ tau1Primes M →
          alphaCoreIn M ⊓ centralizer (P : Set G) ≤ alphaCoreIn M ⊓ centralizer (R : Set G) →
          alphaCoreIn M ⊓ centralizer (P : Set G) = alphaCoreIn M ⊓ centralizer (R : Set G)) →
        sigmaCore M ⊓ centralizer (P : Set G) ≤ sigmaCore M ⊓ centralizer (R : Set G)

@[expose]
noncomputable def FTS_all_type_I_core_centralizer_control : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    (∀ M ∈ maximalSubgroups G, IsTypeI M) →
    ∀ M ∈ maximalSubgroups G,
      (∀ h ∈ (hallCoreIn M : Set G) \ {1},
        centralizer ({h} : Set G) ≤ M ∧ sigSignalizer h = ⊥) ∧
      sigDelta M = ⋃ g : G, (fun x => g⁻¹ * x * g) '' ((hallCoreIn M : Set G) \ {1})

@[expose]
noncomputable def FTS_all_type_I_packet_cover : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    (∀ M ∈ maximalSubgroups G, IsTypeI M) →
    ∀ 𝓣 : Set (Subgroup G), 𝓣 ⊆ maximalSubgroups G →
      (∀ M ∈ maximalSubgroups G, ∃! T, T ∈ 𝓣 ∧
        ∃ g : G, Subgroup.map (MulAut.conj g : G ≃* G) M = T) →
      (∀ M ∈ 𝓣, (sigDelta M).Nonempty) ∧
        (∀ M ∈ 𝓣, ∀ T ∈ 𝓣, M ≠ T → sigDelta M ∩ sigDelta T = ∅) ∧
        (⋃ M ∈ 𝓣, sigDelta M) = (Set.univ : Set G) \ {1} ∧
        (∀ M ∈ 𝓣, ∀ T ∈ 𝓣, M ≠ T →
          Nat.Coprime (Nat.card (sigmaCore M)) (Nat.card (sigmaCore T))) ∧
        (∀ M ∈ 𝓣, Nat.card (sigDelta M) = (Nat.card (sigmaCore M) - 1) * M.index) ∧
        ∀ p ∈ (Nat.card G).primeFactors, ∃ M ∈ 𝓣, p ∣ Nat.card (sigmaCore M)

@[expose]
noncomputable def FTS_alpha_centralizer_uniqueness : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M X : Subgroup G, IsCoatom M → X ≤ M →
      (∀ p ∈ (Nat.card X).primeFactors, p ∉ alphaPrimes ↥M) →
      (∃ p : ℕ, p.Prime ∧
        2 ≤ elementaryAbelianPRank p ↥(alphaCoreIn M ⊓ centralizer (X : Set G))) →
      IsUniqueMaximalOvergroup (M ⊓ centralizer (X : Set G)) M

@[expose]
noncomputable def FTS_alpha_core_prime_centralizer_choice : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M Q : Subgroup G, M ∈ maximalSubgroups G →
      ∀ q : ℕ, q.Prime → q ∉ sigmaPrimes M → Q ≠ ⊥ → IsSylowIn q Q M →
      ∃ x ∈ Q, orderOf x = q ∧
        ∀ r : ℕ, r.Prime → ∀ P : Subgroup G,
          IsSylowIn r P (alphaCoreIn M ⊓ centralizer ({x} : Set G)) → IsCyclic ↥P

@[expose]
def FTS_auxiliary_opposite_tau_two_rank_one : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M T : Subgroup G, M ∈ maximalSubgroups G → T ∈ maximalSubgroups G →
      tauTwoPrimes T ⊆ sigmaPrimes M →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card M → p ∈ sigmaPrimes T → p ∈ betaPrimes ↥T) →
      ∀ p ∈ tauTwoPrimes M, elementaryAbelianPRank p ↥T ≤ 1

@[expose]
def FTS_beta_core_hall_quotient : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M ∈ maximalSubgroups G,
      ((betaCore M).subgroupOf M).Characteristic ∧
        M ≤ normalizer ((betaCore M : Subgroup G) : Set G) ∧
        IsHallPiIn (betaPrimes ↥M) (betaCore M) M ∧
        betaCore M ≤ ⁅M, M⁆ ∧
        IsHallPiIn (betaPrimes ↥M) (betaCore M) ⊤ ∧
        ∃ hN : ((betaCore M).subgroupOf ⁅M, M⁆).Normal,
          letI := hN
          Group.IsNilpotent (↥(⁅M, M⁆ : Subgroup G) ⧸ (betaCore M).subgroupOf ⁅M, M⁆)

@[expose]
def FTS_beta_or_derived_line_centralizer_unique : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M X : Subgroup G, M ∈ maximalSubgroups G → ∀ p : ℕ, p.Prime →
      X ≤ M → Nat.card X = p →
      (p ∈ betaPrimes ↥M ∨ X ≤ ⁅sigmaCore M, sigmaCore M⁆) →
      IsUniqueMaximalOvergroup (centralizer (X : Set G)) M ∧
        ∀ P : Subgroup G, IsSylowIn p P (sigmaCore M) → IsUniqueMaximalOvergroup P M

@[expose]
def FTS_beta_prime_centralizing_sylow : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M ∈ maximalSubgroups G, ∀ p q : ℕ, p.Prime → q.Prime → Odd p → Odd q → p ≠ q →
      p ∉ betaPrimes ↥M → q ∉ betaPrimes ↥M →
      ∀ X : Subgroup G, ∀ a : ℕ, X ≤ M → Nat.card X = q ^ a →
        (X ≤ ⁅M, M⁆ ∨ p < q) →
        ∃ P : Subgroup G, IsSylowIn p P (sigmaCore M) ∧ ⁅X, P⁆ = ⊥

@[expose]
noncomputable def FTS_beta_prime_derived_complement : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M ∈ maximalSubgroups G, ∀ p : ℕ, p.Prime → Odd p → p ∉ betaPrimes ↥M →
      ((pComplCoreIn p (⁅M, M⁆ : Subgroup G)).subgroupOf ⁅M, M⁆).Normal ∧
        ¬ p ∣ Nat.card (pComplCoreIn p (⁅M, M⁆ : Subgroup G)) ∧
        (∃ k : ℕ, (pComplCoreIn p (⁅M, M⁆ : Subgroup G)).relIndex ⁅M, M⁆ = p ^ k) ∧
        ((pComplCoreIn p (sigmaCore M)).subgroupOf (sigmaCore M)).Normal ∧
        ¬ p ∣ Nat.card (pComplCoreIn p (sigmaCore M)) ∧
        ∃ k : ℕ, (pComplCoreIn p (sigmaCore M)).relIndex (sigmaCore M) = p ^ k

@[expose]
def FTS_beta_prime_derived_nilpotent : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M ∈ maximalSubgroups G, ∀ Y : Subgroup G, Y ≤ ⁅M, M⁆ →
      (∀ p ∈ (Nat.card Y).primeFactors, p ∉ betaPrimes ↥M) → Group.IsNilpotent ↥Y

@[expose]
def FTS_beta_prime_quotient_largest_prime : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
    ∀ M ∈ maximalSubgroups G, ∀ p : ℕ, p.Prime → Odd p → p ∉ betaPrimes ↥M →
      ∃ hN : (pComplCore p ↥M).Normal,
        letI := hN
        ∀ q ∈ (Nat.card (↥M ⧸ pComplCore p ↥M)).primeFactors, q ≤ p

end Statements

end

end CFSG.FeitThompson
