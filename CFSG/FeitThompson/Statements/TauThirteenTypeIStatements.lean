module

public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.AlphaCore
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
public import CFSG.FeitThompson.Definitions.CanonicalCentralizerSignalizerFrom
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.DadeAveragingMap
public import CFSG.FeitThompson.Definitions.DadeSupportExtension
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup ComplexOrder

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace Prep05

variable {G : Type*} [Group G]

structure IsMinimalSimpleOdd (G : Type*) [Group G] [Finite G] : Prop where
  odd_natCard : Odd (Nat.card G)
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  isSolvable_of_ne_top : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H

@[expose]
def hallCoreOf (M : Subgroup G) : Subgroup G := (hallCore ↥M).map M.subtype

theorem hallCoreOf_eq (M : Subgroup G) : hallCoreOf M = (hallCore ↥M).map M.subtype := (rfl)

theorem hallCoreOf_le (M : Subgroup G) : hallCoreOf M ≤ M := Subgroup.map_subtype_le _

theorem coe_hallCoreOf_sdiff (M : Subgroup G) :
    (hallCoreOf M : Set G) \ {1} = hallCoreSharp M := by
  rw [hallCoreSharp_eq, hallCoreOf_eq]

@[expose]
def fittingOf [Finite G] (M : Subgroup G) : Subgroup G := (fittingRaw ↥M).map M.subtype

theorem fittingOf_eq [Finite G] (M : Subgroup G) :
    fittingOf M = (fittingRaw ↥M).map M.subtype := (rfl)

theorem fittingOf_le [Finite G] (M : Subgroup G) : fittingOf M ≤ M := Subgroup.map_subtype_le _

@[expose]
def alphaCoreOf [Finite G] (M : Subgroup G) : Subgroup G := (alphaCore ↥M).map M.subtype

theorem alphaCoreOf_eq [Finite G] (M : Subgroup G) :
    alphaCoreOf M = (alphaCore ↥M).map M.subtype := (rfl)

@[expose]
def betaCoreOf [Finite G] (M : Subgroup G) : Subgroup G :=
  (piCore (betaPrimes ↥M) ↥M).map M.subtype

theorem betaCoreOf_eq [Finite G] (M : Subgroup G) :
    betaCoreOf M = (piCore (betaPrimes ↥M) ↥M).map M.subtype := (rfl)

@[expose]
def centralizerIn (X Y : Subgroup G) : Subgroup G := X ⊓ centralizer (Y : Set G)

theorem centralizerIn_eq (X Y : Subgroup G) :
    centralizerIn X Y = X ⊓ centralizer (Y : Set G) := (rfl)

theorem centralizerIn_le (X Y : Subgroup G) : centralizerIn X Y ≤ X := inf_le_left

@[expose]
def IsSylowSubgroupIn (p : ℕ) (P X : Subgroup G) : Prop :=
  P ≤ X ∧ Nat.card ↥P = p ^ (Nat.card ↥X).factorization p

theorem IsSylowSubgroupIn.le {p : ℕ} {P X : Subgroup G} (h : IsSylowSubgroupIn p P X) : P ≤ X :=
  h.1

@[expose]
def IsFixedPointFreeOn (A B : Subgroup G) : Prop :=
  ∀ b ∈ B, b ≠ 1 → centralizerIn A (zpowers b) = ⊥

@[expose]
def IsPPlane (p : ℕ) (A : Subgroup G) : Prop :=
  IsElementaryAbelianSubgroup p A ∧ Nat.card ↥A = p ^ 2

@[expose]
def conjSet (S : Set G) (g : G) : Set G := (fun x => g⁻¹ * x * g) '' S

theorem mem_conjSet {S : Set G} {g x : G} : x ∈ conjSet S g ↔ ∃ y ∈ S, g⁻¹ * y * g = x := by
  simp [conjSet, eq_comm]

@[expose]
def conjClosure (S : Set G) : Set G := ⋃ g : G, conjSet S g

theorem subset_conjClosure (S : Set G) : S ⊆ conjClosure S := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨1, ⟨x, hx, by simp⟩⟩

@[expose]
def IsConjugateSubgroup (X Y : Subgroup G) : Prop :=
  ∃ g : G, Y = X.map (MulAut.conj g).toMonoidHom

theorem isConjugateSubgroup_refl (X : Subgroup G) : IsConjugateSubgroup X X :=
  ⟨1, by ext x; simp⟩

@[expose]
def fixedSet (Y X : Subgroup G) : Set G :=
  {a | a ∈ Y ∧ a ≠ 1 ∧ centralizerIn X (zpowers a) ≠ ⊥}

theorem mem_fixedSet {Y X : Subgroup G} {a : G} :
    a ∈ fixedSet Y X ↔ a ∈ Y ∧ a ≠ 1 ∧ centralizerIn X (zpowers a) ≠ ⊥ := Iff.rfl

theorem fixedSet_subset_coe (Y X : Subgroup G) : fixedSet Y X ⊆ (Y : Set G) := fun _ h => h.1

@[expose]
def leftCosetSet (x : G) (R : Subgroup G) : Set G := (fun r => x * r) '' (R : Set G)

theorem mem_leftCosetSet {x y : G} {R : Subgroup G} :
    y ∈ leftCosetSet x R ↔ ∃ r ∈ R, x * r = y := by
  simp only [leftCosetSet, Set.mem_image, SetLike.mem_coe]

structure IsSigmaComplement [Finite G] (M E : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  semidirect : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E

structure IsTauFactorization [Finite G] (M E E₁ E₂ E₃ : Subgroup G) : Prop where
  isSigmaComplement : IsSigmaComplement M E
  le_E₁ : E₁ ≤ E
  le_E₂ : E₂ ≤ E
  le_E₃ : E₃ ≤ E
  hall_E₁ : IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E)
  hall_E₂ : IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf E)
  hall_E₃ : IsHallPiSubgroup (tau3Primes M) (E₃.subgroupOf E)
  semidirect_E : FreeCore.IsInternalSemidirectProduct E E₃ (E₂ ⊔ E₁)
  semidirect_E₂₁ : FreeCore.IsInternalSemidirectProduct (E₂ ⊔ E₁) E₂ E₁
  isCyclic_E₁ : IsCyclic ↥E₁
  isCyclic_E₃ : IsCyclic ↥E₃
  le_commutator_E₃ : E₃ ≤ ⁅E, E⁆
  normalizes_E₂E₃ : E ≤ normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G)
  centralizer_E₃ : centralizerIn E₃ E = ⊥

@[expose]
noncomputable def signalizer [Finite G] (x : G) : Subgroup G :=
  canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x

theorem signalizer_eq [Finite G] (x : G) :
    signalizer x = canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x := (rfl)

open Classical in
@[expose]
noncomputable def signalizerOn [Finite G] (A : Set G) (x : G) : Subgroup G :=
  if x ∈ A then signalizer x else ⊥

theorem signalizerOn_of_mem [Finite G] {A : Set G} {x : G} (hx : x ∈ A) :
    signalizerOn A x = signalizer x := by classical rw [signalizerOn, if_pos hx]

theorem signalizerOn_of_notMem [Finite G] {A : Set G} {x : G} (hx : x ∉ A) :
    signalizerOn A x = ⊥ := by classical rw [signalizerOn, if_neg hx]

@[expose]
noncomputable def sigSignalizer [Finite G] (X : Subgroup G) : G → Subgroup G :=
  signalizerOn ((sigmaCore X : Set G) \ {1})

@[expose]
noncomputable def derSignalizer [Finite G] (M : Subgroup G) : G → Subgroup G :=
  signalizerOn (((⁅M, M⁆ : Subgroup G) : Set G) \ {1})

@[expose]
noncomputable def extendZero {X : Subgroup G} (f : ↥X → ℂ) : G → ℂ :=
  Function.extend X.subtype f 0

@[expose]
noncomputable def cfIP {X : Type*} [Finite X] (f g : X → ℂ) : ℂ :=
  letI := Fintype.ofFinite X
  cfInner f g

@[expose]
noncomputable def indToTop [Finite G] (X : Subgroup G) (f : ↥X → ℂ) : G → ℂ :=
  letI := Fintype.ofFinite G
  indClassFun X f

@[expose]
noncomputable def indBetween [Finite G] (X Y : Subgroup G) (f : ↥X → ℂ) : ↥Y → ℂ :=
  letI := Fintype.ofFinite ↥Y
  indClassFun (X.subgroupOf Y) fun z => extendZero f ((z : ↥Y) : G)

@[expose]
def cconj {X : Type*} (f : X → ℂ) : X → ℂ := fun x => star (f x)

theorem cconj_apply {X : Type*} (f : X → ℂ) (x : X) : cconj f x = star (f x) := (rfl)

@[expose]
def IsSignedIrr {X : Type*} [Group X] (f : X → ℂ) : Prop := f ∈ Irr X ∨ -f ∈ Irr X

theorem IsSignedIrr.of_mem_Irr {X : Type*} [Group X] {f : X → ℂ} (h : f ∈ Irr X) :
    IsSignedIrr f := Or.inl h

@[expose]
def kerContains (A X : Subgroup G) (θ : ↥X → ℂ) : Prop :=
  ∀ x : ↥X, (x : G) ∈ A → θ x = θ 1

@[expose]
noncomputable def hallIndFam [Finite G] (X : Subgroup G) : Set (↥X → ℂ) :=
  indBetween (hallCoreOf X) X '' {θ ∈ Irr ↥(hallCoreOf X) | θ ≠ 1}

@[expose]
noncomputable def derivedIndFam [Finite G] (M : Subgroup G) : Set (↥M → ℂ) :=
  indBetween (⁅M, M⁆ : Subgroup G) M '' {θ ∈ Irr ↥(⁅M, M⁆ : Subgroup G) | θ ≠ 1}

@[expose]
noncomputable def derivedIndFamKer [Finite G] (M A : Subgroup G) : Set (↥M → ℂ) :=
  indBetween (⁅M, M⁆ : Subgroup G) M ''
    {θ ∈ Irr ↥(⁅M, M⁆ : Subgroup G) | θ ≠ 1 ∧ kerContains A (⁅M, M⁆ : Subgroup G) θ}

@[expose]
noncomputable def tauHall [Finite G] (X : Subgroup G) (f : ↥X → ℂ) : G → ℂ :=
  dadeSupportExtension (fixedSet X (hallCoreOf X)) (sigSignalizer X) (extendZero f)

@[expose]
noncomputable def tauDerived [Finite G] (M W₁ W₂ : Subgroup G) (f : ↥M → ℂ) : G → ℂ :=
  dadeSupportExtension
    ((((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) ∪ ⋃ m ∈ (M : Set G), conjSet (cyclicTIset W₁ W₂) m)
    (derSignalizer M) (extendZero f)

@[expose]
noncomputable def rhoHall [Finite G] (X : Subgroup G) (χ : G → ℂ) : G → ℂ :=
  letI := Fintype.ofFinite G
  dadeAverage (fixedSet X (hallCoreOf X)) (sigSignalizer X) χ

@[expose]
noncomputable def rhoHallCore [Finite G] (X : Subgroup G) (χ : G → ℂ) : G → ℂ :=
  letI := Fintype.ofFinite G
  dadeAverage ((hallCoreOf X : Set G) \ {1}) (sigSignalizer X) χ

structure IsCoherentAt [Finite G] (X : Subgroup G) (S : Set (↥X → ℂ))
    (τ : (↥X → ℂ) → (G → ℂ)) (ν : Submodule.span ℤ S →+ (G → ℂ)) : Prop where
  mem_virtualChars : ∀ f, (ν f : G → ℂ) ∈ virtualChars G
  isometry : ∀ f g, cfIP (ν f : G → ℂ) (ν g : G → ℂ) = cfIP (f : ↥X → ℂ) (g : ↥X → ℂ)
  eq_tau : ∀ f : Submodule.span ℤ S, (f : ↥X → ℂ) 1 = 0 → (ν f : G → ℂ) = τ (f : ↥X → ℂ)

@[expose]
def IsInvariantSubmodule {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
    (D : Subgroup (V ≃ₗ[k] V)) (W : Submodule k V) : Prop :=
  ∀ g ∈ D, ∀ v ∈ W, (g : V ≃ₗ[k] V) v ∈ W

@[expose]
def IsIrreducibleLinear {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
    (D : Subgroup (V ≃ₗ[k] V)) : Prop :=
  ∀ W : Submodule k V, IsInvariantSubmodule D W → W = ⊥ ∨ W = ⊤

@[expose]
def fixedSubmodule {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
    (D : Subgroup (V ≃ₗ[k] V)) : Submodule k V where
  carrier := {v | ∀ g ∈ D, (g : V ≃ₗ[k] V) v = v}
  zero_mem' g _ := map_zero _
  add_mem' hx hy g hg := by rw [map_add, hx g hg, hy g hg]
  smul_mem' c x hx g hg := by rw [map_smul, hx g hg]

theorem mem_fixedSubmodule {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
    {D : Subgroup (V ≃ₗ[k] V)} {v : V} :
    v ∈ fixedSubmodule D ↔ ∀ g ∈ D, (g : V ≃ₗ[k] V) v = v := Iff.rfl

structure IsConjModule (p : ℕ) {G : Type*} [Group G] (H X : Subgroup G) (V : Type*)
    [AddCommGroup V] [Module (ZMod p) V] (e : ↥H ≃* Multiplicative V)
    (ρ : ↥X →* (V ≃ₗ[ZMod p] V)) : Prop where
  conj_eq : ∀ (x : ↥X) (h : ↥H) (hc : (x : G) * (h : G) * (x : G)⁻¹ ∈ H),
    e ⟨(x : G) * (h : G) * (x : G)⁻¹, hc⟩ =
      Multiplicative.ofAdd (ρ x (Multiplicative.toAdd (e h)))

namespace IsConjModule

variable {p : ℕ} {H X : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {e : ↥H ≃* Multiplicative V} {ρ : ↥X →* (V ≃ₗ[ZMod p] V)}

theorem conj_inv_eq (hρ : IsConjModule p H X V e ρ) (x : ↥X) (h : ↥H)
    (hc : (x : G)⁻¹ * (h : G) * (x : G) ∈ H) :
    e ⟨(x : G)⁻¹ * (h : G) * (x : G), hc⟩ =
      Multiplicative.ofAdd (ρ x⁻¹ (Multiplicative.toAdd (e h))) := by
  have h1 := hρ.conj_eq x⁻¹ h (by simpa using hc)
  simpa using h1

theorem conj_mul_eq (hρ : IsConjModule p H X V e ρ) (x y : ↥X) (h : ↥H)
    (hy : (y : G) * (h : G) * (y : G)⁻¹ ∈ H)
    (hxy : ((x : G) * (y : G)) * (h : G) * ((x : G) * (y : G))⁻¹ ∈ H) :
    e ⟨((x : G) * (y : G)) * (h : G) * ((x : G) * (y : G))⁻¹, hxy⟩ =
      Multiplicative.ofAdd (ρ x (ρ y (Multiplicative.toAdd (e h)))) := by
  have hmem : (x : G) * ((y : G) * (h : G) * (y : G)⁻¹) * (x : G)⁻¹ ∈ H := by
    have hg : (x : G) * ((y : G) * (h : G) * (y : G)⁻¹) * (x : G)⁻¹
        = ((x : G) * (y : G)) * (h : G) * ((x : G) * (y : G))⁻¹ := by group
    rw [hg]; exact hxy
  have h1 := hρ.conj_eq x ⟨(y : G) * (h : G) * (y : G)⁻¹, hy⟩ hmem
  have h2 := hρ.conj_eq y h hy
  have e_eq : e ⟨((x : G) * (y : G)) * (h : G) * ((x : G) * (y : G))⁻¹, hxy⟩
      = e ⟨(x : G) * ((y : G) * (h : G) * (y : G)⁻¹) * (x : G)⁻¹, hmem⟩ := by
    congr 1
    exact Subtype.ext (by group)
  rw [e_eq, h1, h2]
  simp

theorem apply_mul (x y : ↥X) (v : V) : ρ (x * y) v = ρ x (ρ y v) := by
  rw [map_mul]; rfl

theorem conj_one_eq (hρ : IsConjModule p H X V e ρ) (h : ↥H) :
    ρ (1 : ↥X) (Multiplicative.toAdd (e h)) = Multiplicative.toAdd (e h) := by
  simp

end IsConjModule

@[expose]
def IsElemAbelianLayer (p q : ℕ) (H₀ H : Subgroup G) : Prop :=
  H₀ ≤ H ∧ ⁅H, H⁆ ≤ H₀ ∧ (∀ h ∈ H, h ^ p ∈ H₀) ∧ H₀.relIndex H = p ^ q

@[expose]
def IsChiefLayer (M H₀ H : Subgroup G) : Prop :=
  M ≤ normalizer (H₀ : Set G) ∧ H₀ < H ∧
    ∀ N : Subgroup G, M ≤ normalizer (N : Set G) → H₀ ≤ N → N ≤ H → N = H₀ ∨ N = H

end Prep05

namespace Statements

open Prep05

@[expose]
def FNI_tau13_noncentral_prime_configuration : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsTauFactorization M E E₁ E₂ E₃ →
      ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≤ E₁ → Nat.card ↥P = p →
        ¬ P ≤ centralizer (E₃ : Set G) →
          ∃ q ∈ tau3Primes M, ∃ Q : Subgroup G, Q ≤ E₃ ∧ Q ≠ ⊥ ∧ IsCyclic ↥Q ∧
            IsSylowSubgroupIn q Q E₃ ∧ IsSylowSubgroupIn q Q M ∧
            E ≤ normalizer (Q : Set G) ∧ centralizerIn Q P = ⊥ ∧
            ¬ normalizer (Q : Set G) ≤ M ∧
            alphaPrimes ↥M = betaPrimes ↥M ∧ alphaCoreOf M = betaCoreOf M ∧
            alphaCoreOf M ≠ ⊥ ∧ centralizerIn (alphaCoreOf M) P ≠ ⊥ ∧
            centralizerIn (alphaCoreOf M) (P ⊔ Q) = ⊥

@[expose]
def FNI_tau13_noncentral_third_factor_free : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsTauFactorization M E E₁ E₂ E₃ →
      ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≤ E₁ → Nat.card ↥P = p →
        ¬ P ≤ centralizer (E₃ : Set G) →
          ∀ x ∈ E₃, x ≠ 1 → centralizerIn (sigmaCore M) (zpowers x) = ⊥

@[expose]
def FNI_tau13_nonfree_product_fixed_centralizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsTauFactorization M E E₁ E₂ E₃ →
      (∃ b ∈ E₁, b ≠ 1 ∧ centralizerIn E₃ (zpowers b) ≠ ⊥) →
        ∀ X : Subgroup G, X ≤ E₃ ⊔ E₁ → X ≠ ⊥ →
          centralizerIn (sigmaCore M) X = centralizerIn (sigmaCore M) (E₃ ⊔ E₁)

@[expose]
def FNI_tau13_nonfree_third_factor_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsTauFactorization M E E₁ E₂ E₃ →
      (∃ x ∈ E₃, x ≠ 1 ∧ centralizerIn (sigmaCore M) (zpowers x) ≠ ⊥) →
        E₂ = ⊥ ∧ E₁ ≠ ⊥ ∧ FreeCore.IsInternalSemidirectProduct E E₃ E₁ ∧
          (∀ X : Subgroup G, X ≤ E → (Nat.card ↥X).Prime → E ≤ normalizer (X : Set G)) ∧
          ∀ Y : Subgroup G, Y ≤ E → Y ≠ ⊥ →
            centralizerIn (sigmaCore M) Y = centralizerIn (sigmaCore M) E

@[expose]
def FNI_tau13_nonregular_core_line_unique : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E : Subgroup G, IsSigmaComplement M E →
      ∀ p ∈ tau1Primes M ∪ tau3Primes M, ∀ P : Subgroup G, P ≤ E → Nat.card ↥P = p →
        centralizerIn (sigmaCore M) P ≠ ⊥ →
          ∀ q : ℕ, q.Prime → ∀ Q : Subgroup G, Q ≤ centralizerIn (sigmaCore M) P →
            Nat.card ↥Q = q → IsUniqueMaximalOvergroup (centralizer (Q : Set G)) M

@[expose]
def FNI_tau13_nonregular_line_normalizer_sigma : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E : Subgroup G, IsSigmaComplement M E →
      ∀ p ∈ tau1Primes M ∪ tau3Primes M, ∀ P : Subgroup G, P ≤ E → Nat.card ↥P = p →
        centralizerIn (sigmaCore M) P ≠ ⊥ →
          ∀ L : Subgroup G, IsCoatom L → normalizer (P : Set G) ≤ L → p ∈ sigmaPrimes L

@[expose]
def FNI_tau13_nonsigma_normalizer_reflected_plane : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E : Subgroup G, IsSigmaComplement M E →
      ∀ p ∈ tau1Primes M ∪ tau3Primes M, ∀ P : Subgroup G, P ≤ E → Nat.card ↥P = p →
        centralizerIn (sigmaCore M) P ≠ ⊥ →
          ∀ L : Subgroup G, IsCoatom L → normalizer (P : Set G) ≤ L → p ∉ sigmaPrimes L →
            (∃ F : Subgroup G, IsSigmaComplement L F ∧ ∃ q ∈ tau1Primes L,
              ∃ Q : Subgroup G, Q ≤ F ∧ Nat.card ↥Q = q ∧
                ∃ A : Subgroup G, A ≤ F ∧ IsPPlane p A ∧ P ≤ A ∧
                  centralizerIn A Q = P ∧ ⁅A, Q⁆ ≠ ⊥ ∧
                  centralizerIn (sigmaCore L) Q = ⊥) ∧
            p ∈ tauTwoPrimes L

@[expose]
def FNI_tau13_strict_fixed_reflection : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsTauFactorization M E E₁ E₂ E₃ →
      ∀ p ∈ tau1Primes M, ∀ P : Subgroup G, P ≤ E₁ → Nat.card ↥P = p →
        ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, R ≤ centralizerIn E₃ P → Nat.card ↥R = r →
          centralizerIn (sigmaCore M) P < centralizerIn (sigmaCore M) R →
            E₂ = ⊥ ∧ ∃ T : Subgroup G, IsCoatom T ∧ normalizer (R : Set G) ≤ T ∧ E ≤ T ∧
              r ∈ sigmaPrimes T ∧ ∀ s ∈ (Nat.card ↥E₁).primeFactors, s ∈ tau1Primes T

@[expose]
def FNI_type_p_core_linear_alternative : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ p q u N : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
        u = (centralizerIn U (hallCoreOf M)).relIndex U → N = (p ^ q - 1) / (p - 1) →
      ∀ (V : Type v) [AddCommGroup V] [Module (ZMod p) V]
        (e : ↥(hallCoreOf M) ≃* Multiplicative V) (ρ : ↥M →* (V ≃ₗ[ZMod p] V)),
        IsConjModule p (hallCoreOf M) M V e ρ →
      ∀ D B : Subgroup (V ≃ₗ[ZMod p] V),
        D = (U.subgroupOf M).map ρ → B = (W₁.subgroupOf M).map ρ →
          D ≠ ⊥ ∧ IsMulCommutative ↥D ∧ Nat.card ↥D = u ∧ Odd u ∧ Nat.Coprime u q ∧
            Nat.card ↥B = q ∧ D ⊓ centralizer (B : Set (V ≃ₗ[ZMod p] V)) = ⊥ ∧
            Module.finrank (ZMod p) ↥(fixedSubmodule B) = 1 ∧
            IsIrreducibleLinear (D ⊔ B) ∧
            Xor
              (¬ IsIrreducibleLinear D ∧
                ∃ L : Fin q → Submodule (ZMod p) V,
                  (∀ i, IsInvariantSubmodule D (L i)) ∧
                  (∀ i, Module.finrank (ZMod p) ↥(L i) = 1) ∧
                  iSupIndep L ∧ (⨆ i, L i) = ⊤ ∧
                  (∃ b ∈ B, ∀ i : Fin q,
                    (L i).map (b : V ≃ₗ[ZMod p] V).toLinearMap = L (finRotate q i)) ∧
                  (∃ a : ℕ, 1 < a ∧ a ∣ p - 1 ∧
                    ∃ φ : ↥D →* (Fin (q - 1) → Multiplicative (ZMod a)), Function.Injective φ) ∧
                  ∀ g ∈ D, ∃ c : Fin q → ZMod p,
                    (∀ i, ∀ v ∈ L i, (g : V ≃ₗ[ZMod p] V) v = c i • v) ∧ ∏ i, c i = 1)
              (IsIrreducibleLinear D ∧
                ∃ (E : Type v) (_ : Field E) (_ : Algebra (ZMod p) E), Nat.card E = p ^ q ∧
                  ∃ φ : V ≃ₗ[ZMod p] E,
                    (∃ v ∈ fixedSubmodule B, v ≠ 0 ∧ φ v = 1) ∧
                    (∃ S : Subgroup Eˣ, IsCyclic ↥S ∧
                      ∀ g : V ≃ₗ[ZMod p] V, g ∈ D ↔ ∃ s ∈ S, ∀ v : V, φ (g v) = (s : E) * φ v) ∧
                    (∀ b : V ≃ₗ[ZMod p] V, b ∈ B ↔
                      ∃ σ : E ≃ₐ[ZMod p] E, ∀ v : V, φ (b v) = σ (φ v)) ∧
                    (fun v => φ v) '' (fixedSubmodule B : Set V) =
                      Set.range (algebraMap (ZMod p) E) ∧
                    Nat.Coprime u (p - 1) ∧ u ∣ N) ∧
            u ≤ N

@[expose]
def FNI_type_p_elementary_core_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ p q : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
        (IsTypeII M ∨ IsTypeIII M) ∧
        p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧
        U ≠ ⊥ ∧ IsMulCommutative ↥U ∧
        FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (U ⊔ W₁) ∧
        FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁ ∧
        Nat.Coprime (Nat.card ↥(hallCoreOf M)) (Nat.card ↥U * Nat.card ↥W₁) ∧
        IsFixedPointFreeOn U W₁ ∧
        (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ZMod p) V),
          Module.finrank (ZMod p) V = q ∧ Nonempty (↥(hallCoreOf M) ≃* Multiplicative V)) ∧
        Nat.card ↥(hallCoreOf M) = p ^ q ∧
        centralizerIn (hallCoreOf M) U = ⊥ ∧
        centralizerIn (hallCoreOf M) W₁ = W₂ ∧
        hallCoreOf M ≠ ⊥ ∧
        (∀ N : Subgroup G, N ≤ hallCoreOf M → M ≤ normalizer (N : Set G) →
          N = ⊥ ∨ N = hallCoreOf M) ∧
        centralizerIn U (hallCoreOf M) < U ∧
        M ≤ normalizer ((centralizerIn U (hallCoreOf M) : Subgroup G) : Set G) ∧
        IsInternalDirectProduct (fittingOf M) (hallCoreOf M) (centralizerIn U (hallCoreOf M)) ∧
        IsMulCommutative ↥(fittingOf M) ∧
        IsTIWithNormalizer ((hallCoreOf M : Set G) \ {1}) M ∧
        IsTIWithNormalizer ((fittingOf M : Set G) \ {1}) M

@[expose]
def FNI_type_p_field_inner_complement_order : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ p q N : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ → N = (p ^ q - 1) / (p - 1) →
      ∀ (V : Type v) [AddCommGroup V] [Module (ZMod p) V]
        (e : ↥(hallCoreOf M) ≃* Multiplicative V) (ρ : ↥M →* (V ≃ₗ[ZMod p] V)),
        IsConjModule p (hallCoreOf M) M V e ρ →
        IsIrreducibleLinear ((U.subgroupOf M).map ρ) →
          IsCyclic ↥U ∧ (q ∣ p - 1 → q ∣ N ∧ Nat.card ↥U = N / q) ∧
            (¬ q ∣ p - 1 → Nat.card ↥U = N)

@[expose]
def FNI_type_p_fitting_induced_witness : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ q u : ℕ, q = Nat.card ↥W₁ → u = (centralizerIn U (hallCoreOf M)).relIndex U →
        centralizerIn U (hallCoreOf M) ≠ ⊥ →
          ∃ ψ ∈ Irr ↥(fittingOf M), ψ 1 = 1 ∧
            ∃ β ∈ Irr ↥(⁅M, M⁆ : Subgroup G),
              β = indBetween (fittingOf M) (⁅M, M⁆ : Subgroup G) ψ ∧
              ∃ lam : ↥M → ℂ, lam = indBetween (⁅M, M⁆ : Subgroup G) M β ∧
                lam = indBetween (fittingOf M) M ψ ∧ lam ∈ Irr ↥M ∧
                lam 1 = (q * u : ℕ) ∧
                ¬ kerContains (hallCoreOf M) (⁅M, M⁆ : Subgroup G) β ∧
                ¬ kerContains (hallCoreOf M) M lam

@[expose]
def FNI_type_p_inner_action_faithful : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      centralizerIn U (hallCoreOf M) = ⊥ ∧ fittingOf M = hallCoreOf M

@[expose]
def FNI_type_p_prime_factors : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ p q : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
        p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧
        ∃ T : Subgroup G, IsCoatom T ∧ T ≠ M ∧ ∃ V : Subgroup G, V ≤ T ∧
          IsWitnessedPConfiguration T V W₂ W₁ ∧ M ⊓ T = W₁ ⊔ W₂ ∧
          (IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) ∧
          (IsTypeII T ∨ IsTypeIII T ∨ IsTypeIV T ∨ IsTypeV T) ∧
          (IsTypeII M ∨ IsTypeII T) ∧
          ∀ L : Subgroup G, IsCoatom L → ¬ IsTypeI L →
            IsConjugateSubgroup M L ∨ IsConjugateSubgroup T L

@[expose]
def FNI_type_p_reducible_inner_action_order : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ p q : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
      ∀ (V : Type v) [AddCommGroup V] [Module (ZMod p) V]
        (e : ↥(hallCoreOf M) ≃* Multiplicative V) (ρ : ↥M →* (V ≃ₗ[ZMod p] V)),
        IsConjModule p (hallCoreOf M) M V e ρ →
        (∃ W : Submodule (ZMod p) V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
          IsInvariantSubmodule ((U.subgroupOf M).map ρ) W) →
          q = 3 ∧ ∀ A : ℕ, A = (p - 1) / 2 →
            Nat.card ↥U = A ^ 2 ∧
            Nonempty (↥U ≃* (Multiplicative (ZMod A) × Multiplicative (ZMod A))) ∧
            0 < A ∧ Odd A ∧ 1 < A

@[expose]
def FPF_all_type_I_kernel_partition : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    (∀ M : Subgroup G, IsCoatom M → IsTypeI M) →
      ∃ k : ℕ, 2 ≤ k ∧ ∃ L : Fin k → Subgroup G, (∀ i, IsCoatom (L i)) ∧
        (∀ M : Subgroup G, IsCoatom M → ∃! i : Fin k, IsConjugateSubgroup (L i) M) ∧
        (∀ i, hallCoreOf (L i) ≠ ⊥) ∧
        (∀ i, ∃ E : Subgroup G, E ≤ L i ∧ E ≠ ⊥ ∧
          FreeCore.IsInternalSemidirectProduct (L i) (hallCoreOf (L i)) E ∧
          IsFixedPointFreeOn (hallCoreOf (L i)) E) ∧
        (∀ i, IsTIWithNormalizer ((hallCoreOf (L i) : Set G) \ {1}) (L i)) ∧
        (∀ i j, i ≠ j →
          Nat.Coprime (Nat.card ↥(hallCoreOf (L i))) (Nat.card ↥(hallCoreOf (L j)))) ∧
        (∀ (i : Fin k) (g : G), (conjSet ((hallCoreOf (L i) : Set G) \ {1}) g).Nonempty) ∧
        (∀ (i j : Fin k) (g h : G),
          conjSet ((hallCoreOf (L i) : Set G) \ {1}) g ≠
              conjSet ((hallCoreOf (L j) : Set G) \ {1}) h →
            Disjoint (conjSet ((hallCoreOf (L i) : Set G) \ {1}) g)
              (conjSet ((hallCoreOf (L j) : Set G) \ {1}) h)) ∧
        (⋃ i : Fin k, conjClosure ((hallCoreOf (L i) : Set G) \ {1})) = Set.univ \ {1}

@[expose]
def FPF_complement_plane_centralizer_witness : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M : Subgroup G, IsCoatom M → sigmaCore M ≠ ⊥ →
      ∀ p : ℕ, p.Prime → ¬ p ∣ Nat.card ↥(sigmaCore M) →
        ∀ P : Subgroup G, P ≤ M → IsPGroup p ↥P →
          (∃ A : Subgroup G, A ≤ P ∧ IsPPlane p A) →
            (∀ a ∈ P, orderOf a = p → centralizerIn (sigmaCore M) (zpowers a) ≠ ⊥ →
              IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) M) →
              ∃ L : Subgroup G, IsCoatom L ∧ ∃ x ∈ P, orderOf x = p ∧ P ≤ sigmaCore L ∧
                ¬ centralizerIn (sigmaCore M) (zpowers x) ≤
                  ⁅sigmaCore M, sigmaCore M⁆ ∧
                normalizer ((zpowers x : Subgroup G) : Set G) ≤ M ∧
                ¬ centralizer ({x} : Set G) ≤ L

@[expose]
def FPF_core_packet_derived_support_centralizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → ¬ IsConjugateSubgroup M N →
      (kappaPrimes M).Nonempty → (kappaPrimes N).Nonempty →
        ∀ x ∈ sigmaCore M, x ≠ 1 → ∀ r ∈ signalizer x,
          x * r ∈ fixedSet (⁅N, N⁆ : Subgroup G) (sigmaCore N) →
            (∃ n : ℤ, (x * r) ^ n = x) ∧ x ∈ (⁅N, N⁆ : Subgroup G) ∧
              centralizerIn (sigmaCore N) (zpowers x) ≠ ⊥ ∧
              IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) N ∧
              ¬ centralizer ({x} : Set G) ≤ M

@[expose]
def FPF_frobenius_coherent_image_other_type_i_blocks : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → IsTypeI M → IsTypeI N →
      ∀ E : Subgroup G, E ≤ N → E ≠ ⊥ →
        FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E →
        IsFixedPointFreeOn (hallCoreOf N) E →
        (¬ ∃ D : Subgroup G, D ≤ M ∧
          FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D ∧
          IsFixedPointFreeOn (hallCoreOf M) D) →
      ∀ ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ),
        IsCoherentAt N (hallIndFam N) (tauHall N) ν →
      ∀ ζ : ↥N → ℂ, ζ ∈ hallIndFam N → ζ ∈ Irr ↥N →
      ∀ hζ : ζ ∈ Submodule.span ℤ (hallIndFam N),
      ∀ Ψ : G → ℂ, Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ) →
        (∀ χ ∈ Irr ↥M, ¬ kerContains (hallCoreOf M) M χ →
          ∃! η : G → ℂ, η ∈ Irr G ∧ η ≠ cconj η ∧
            tauHall M (χ - cconj χ) = η - cconj η) ∧
        IsSignedIrr Ψ ∧
        ∀ η : (↥M → ℂ) → (G → ℂ),
          (∀ χ ∈ Irr ↥M, ¬ kerContains (hallCoreOf M) M χ →
            η χ ∈ Irr G ∧ η χ ≠ cconj (η χ) ∧
            tauHall M (χ - cconj χ) = η χ - cconj (η χ)) →
          ∀ θ ∈ hallIndFam M, ∀ χ ∈ Irr ↥M, ¬ kerContains (hallCoreOf M) M χ →
            0 < cfIP θ χ → cfIP Ψ (η χ) = 0 ∧ cfIP Ψ (-(cconj (η χ))) = 0

@[expose]
def FPF_kappa_positive_core_derived_support_disjoint : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → ¬ IsConjugateSubgroup M N →
      (kappaPrimes M).Nonempty → (kappaPrimes N).Nonempty →
        Disjoint
          (⋃ x ∈ (sigmaCore M : Set G) \ {1}, conjClosure (leftCosetSet x (signalizer x)))
          (conjClosure (fixedSet (⁅N, N⁆ : Subgroup G) (sigmaCore N)))

@[expose]
def FPF_non_type_i_sigma_core_identities : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M : Subgroup G, IsCoatom M →
      (IsTypeII M → sigmaCore M = hallCoreOf M) ∧
      ((IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) → sigmaCore M = ⁅M, M⁆)

@[expose]
def FPF_non_type_i_supporting_maximum_exclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ N : Subgroup G, IsCoatom N →
      (IsTypeII N ∨ IsTypeIII N ∨ IsTypeIV N ∨ IsTypeV N) →
        ∀ p a : ℕ, p.Prime → ∀ P : Subgroup G, P ≤ sigmaCore N → Nat.card ↥P = p ^ a →
          ¬ IsCyclic ↥P → ∀ x ∈ P, x ≠ 1 → ¬ centralizer ({x} : Set G) ≤ N → False

@[expose]
def FPF_not_all_type_I : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∃ M : Subgroup G, IsCoatom M ∧ ¬ IsTypeI M

@[expose]
def FPF_ordered_pair_exclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ S T W₁ W₂ : Subgroup G, IsCoatom S → IsCoatom T → S ≠ T →
      W₁ ≠ ⊥ → W₂ ≠ ⊥ → IsCyclic ↥W₁ → IsCyclic ↥W₂ →
      IsInternalDirectProduct (W₁ ⊔ W₂) W₁ W₂ → IsCyclic ↥(W₁ ⊔ W₂) →
      FreeCore.IsInternalSemidirectProduct S (⁅S, S⁆ : Subgroup G) W₁ →
      FreeCore.IsInternalSemidirectProduct T (⁅T, T⁆ : Subgroup G) W₂ →
      S ⊓ T = W₁ ⊔ W₂ →
      IsTIWithNormalizer (cyclicTIset W₁ W₂) (W₁ ⊔ W₂) →
      (IsTypeII S ∨ IsTypeIII S ∨ IsTypeIV S ∨ IsTypeV S) →
      (IsTypeII T ∨ IsTypeIII T ∨ IsTypeIV T ∨ IsTypeV T) →
      (IsTypeII S ∨ IsTypeII T) →
      (∀ L : Subgroup G, IsCoatom L → ¬ IsTypeI L →
        IsConjugateSubgroup S L ∨ IsConjugateSubgroup T L) →
      Nat.card ↥W₁ < Nat.card ↥W₂ → False

@[expose]
def FPF_ordered_reciprocal_maxima_type_two : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ S T U V W₁ W₂ : Subgroup G, IsCoatom S → IsCoatom T →
      IsWitnessedPConfiguration S U W₁ W₂ → IsWitnessedPConfiguration T V W₂ W₁ →
      Nat.card ↥W₁ < Nat.card ↥W₂ → IsTypeII S ∧ IsTypeII T

@[expose]
def FPF_p_subgroup_sigma_core_placement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup p ↥P →
      ∃ L : Subgroup G, IsCoatom L ∧ P ≤ sigmaCore L

@[expose]
def FPF_reciprocal_type_three_low_family_bound : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ S T U V W₁ W₂ : Subgroup G, IsCoatom S → IsCoatom T →
      IsWitnessedPConfiguration S U W₁ W₂ → IsWitnessedPConfiguration T V W₂ W₁ →
      ∀ p q u v : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
        u = Nat.card ↥U → v = Nat.card ↥V → q < p → IsTypeIII T →
          ((v : ℚ) - 1) / (p : ℚ) ≤ ((u : ℚ) - 1) / (q : ℚ)

@[expose]
def FPF_type_I_frobenius : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ L : Subgroup G, IsCoatom L → IsTypeI L →
      ∃ E : Subgroup G, E ≤ L ∧ E ≠ ⊥ ∧
        FreeCore.IsInternalSemidirectProduct L (hallCoreOf L) E ∧
        IsFixedPointFreeOn (hallCoreOf L) E

@[expose]
def FPF_type_i_nonfrobenius_witness : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M : Subgroup G, IsCoatom M → IsTypeI M →
      ∀ p : ℕ, p.Prime → 2 ≤ elementaryAbelianPRank p ↥M →
        ¬ p ∣ Nat.card ↥(hallCoreOf M) →
        ∀ P : Subgroup G, IsSylowSubgroupIn p P M →
          IsMulCommutative ↥P ∧ elementaryAbelianPRank p ↥P = 2 ∧
          ∃ L : Subgroup G, IsCoatom L ∧ ∃ x ∈ P, orderOf x = p ∧ P ≤ sigmaCore L ∧
            ¬ centralizerIn (hallCoreOf M) (zpowers x) ≤ ⁅hallCoreOf M, hallCoreOf M⁆ ∧
            normalizer ((zpowers x : Subgroup G) : Set G) ≤ M ∧
            ¬ centralizer ({x} : Set G) ≤ L

@[expose]
def FPF_type_i_second_witness_comparison : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → IsTypeI M → IsTypeI N →
      ∀ E : Subgroup G, E ≤ N → E ≠ ⊥ →
        FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E →
        IsFixedPointFreeOn (hallCoreOf N) E →
        (¬ ∃ D : Subgroup G, D ≤ M ∧
          FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D ∧
          IsFixedPointFreeOn (hallCoreOf M) D) →
      ∀ ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ),
        IsCoherentAt N (hallIndFam N) (tauHall N) ν →
      ∀ ζ : ↥N → ℂ, ζ ∈ hallIndFam N → ζ ∈ Irr ↥N →
      ∀ hζ : ζ ∈ Submodule.span ℤ (hallIndFam N),
      ∀ Ψ : G → ℂ, Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ) →
        (∀ k ∈ hallCoreOf M, k ≠ 1 → rhoHall M Ψ k = Ψ k) ∧
        ((hallCoreOf M : Set G) \
          ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G)).Nonempty ∧
        ∃ c : ℤ, ∀ k ∈ (hallCoreOf M : Set G) \
            ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G),
          Ψ k = (c : ℂ)

@[expose]
def FPF_type_i_supporting_case_contradiction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ p : ℕ, p.Prime →
      (∀ q : ℕ, q.Prime → q < p → ∀ Y : Subgroup G, IsCoatom Y → IsTypeI Y →
        2 ≤ elementaryAbelianPRank q ↥Y → q ∣ Nat.card ↥(hallCoreOf Y)) →
      ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → IsTypeI M → IsTypeI N →
        ¬ p ∣ Nat.card ↥(hallCoreOf M) →
        ∀ P : Subgroup G, IsMulCommutative ↥P → IsSylowSubgroupIn p P M →
          elementaryAbelianPRank p ↥P = 2 → P ≤ sigmaCore N →
          ∀ x ∈ P, orderOf x = p →
            ¬ centralizerIn (hallCoreOf M) (zpowers x) ≤ ⁅hallCoreOf M, hallCoreOf M⁆ →
            normalizer ((zpowers x : Subgroup G) : Set G) ≤ M →
            ¬ centralizer ({x} : Set G) ≤ N → False

@[expose]
def FPF_type_i_supporting_character_configuration : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → IsTypeI M → IsTypeI N →
      ∀ E : Subgroup G, E ≤ N → E ≠ ⊥ →
        FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E →
        IsFixedPointFreeOn (hallCoreOf N) E →
        (¬ ∃ B : Subgroup G, B ≤ M ∧
          FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) B ∧
          IsFixedPointFreeOn (hallCoreOf M) B) →
      ∀ p : ℕ, p.Prime → ∀ x : G, x ∈ hallCoreOf N → x ≠ 1 → x ∈ M →
        x ∉ hallCoreOf M → orderOf x = p →
        normalizer ((zpowers x : Subgroup G) : Set G) ≤ M →
        ¬ centralizer ({x} : Set G) ≤ N →
      ∀ h e : ℕ, h = Nat.card ↥(hallCoreOf N) → e = Nat.card ↥E →
        p ^ 2 ≤ h → 2 * e ≤ p + 1 →
        ∃ ζ : ↥N → ℂ, ζ ∈ hallIndFam N ∧ ζ ∈ Irr ↥N ∧ ζ 1 = (e : ℂ) ∧
          ∃ hζ : ζ ∈ Submodule.span ℤ (hallIndFam N),
          ∃ ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ),
            IsCoherentAt N (hallIndFam N) (tauHall N) ν ∧
            ∀ Ψ : G → ℂ, Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ) →
              IsSignedIrr Ψ ∧
              (∀ a : ℕ, 1 ≤ a → a ≤ p - 1 → ∀ k ∈ hallCoreOf M,
                ∀ hxa : x ^ a ∈ N, Ψ (x ^ a * k) = ζ ⟨x ^ a, hxa⟩) ∧
              IsClassFun (fun m : ↥M => rhoHallCore M Ψ (m : G)) ∧
              IsClassFun (fun n : ↥N => rhoHallCore N Ψ (n : G)) ∧
              (∀ k ∈ hallCoreOf M, k ≠ 1 → rhoHallCore M Ψ k = Ψ k) ∧
              ((hallCoreOf M : Set G) \
                ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G)).Nonempty ∧
              (∃ c : ℤ, ∀ k ∈ (hallCoreOf M : Set G) \
                  ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G), Ψ k = (c : ℂ)) ∧
              1 - (e : ℂ) / (h : ℂ) ≤
                cfIP (fun n : ↥N => rhoHallCore N Ψ (n : G))
                  (fun n : ↥N => rhoHallCore N Ψ (n : G))

@[expose]
def FPF_type_i_supporting_group_configuration : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ p : ℕ, p.Prime →
      (∀ q : ℕ, q.Prime → q < p → ∀ Y : Subgroup G, IsCoatom Y → IsTypeI Y →
        2 ≤ elementaryAbelianPRank q ↥Y → q ∣ Nat.card ↥(hallCoreOf Y)) →
      ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → IsTypeI M → IsTypeI N →
        ¬ p ∣ Nat.card ↥(hallCoreOf M) →
        ∀ P : Subgroup G, IsMulCommutative ↥P → IsSylowSubgroupIn p P M →
          elementaryAbelianPRank p ↥P = 2 → P ≤ sigmaCore N →
          ∀ x ∈ P, orderOf x = p →
            ¬ centralizerIn (hallCoreOf M) (zpowers x) ≤ ⁅hallCoreOf M, hallCoreOf M⁆ →
            normalizer ((zpowers x : Subgroup G) : Set G) ≤ M →
            ¬ centralizer ({x} : Set G) ≤ N →
            hallCoreOf M ≠ ⊥ ∧ hallCoreOf N ≠ ⊥ ∧
            Group.IsNilpotent ↥(hallCoreOf M) ∧ Group.IsNilpotent ↥(hallCoreOf N) ∧
            M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) ∧
            N ≤ normalizer ((hallCoreOf N : Subgroup G) : Set G) ∧
            Nat.Coprime (Nat.card ↥(hallCoreOf M)) (hallCoreOf M).index ∧
            Nat.Coprime (Nat.card ↥(hallCoreOf N)) (hallCoreOf N).index ∧
            Group.IsSolvable ↥M ∧ P ≤ hallCoreOf N ∧
            FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (M ⊓ N) ∧
            M ⊓ N ≤ hallCoreOf N ∧
            (∃ D₀ D₁ : Subgroup G, D₀ ≤ M ⊓ N ∧ D₁ ≤ M ⊓ N ∧
              Monoid.exponent ↥D₀ = Monoid.exponent ↥(M ⊓ N) ∧
              IsFixedPointFreeOn (hallCoreOf M) D₀ ∧ IsMulCommutative ↥D₁ ∧
              ∀ k ∈ hallCoreOf M, k ≠ 1 → centralizerIn (M ⊓ N) (zpowers k) ≤ D₁) ∧
            (∃ E : Subgroup G, E ≤ N ∧ E ≠ ⊥ ∧ IsCyclic ↥E ∧
              FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E ∧
              IsFixedPointFreeOn (hallCoreOf N) E ∧
              3 ≤ Nat.card ↥E ∧ (Nat.card ↥E ∣ p - 1 ∨ Nat.card ↥E ∣ p + 1) ∧
              2 * Nat.card ↥E ≤ p + 1) ∧
            3 ≤ p ∧ p ^ 2 ≤ Nat.card ↥(hallCoreOf N) ∧
            ¬ ∃ B : Subgroup G, B ≤ M ∧
              FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) B ∧
              IsFixedPointFreeOn (hallCoreOf M) B

@[expose]
def FPF_type_i_witness_supporting_frobenius : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ p : ℕ, p.Prime →
      (∀ q : ℕ, q.Prime → q < p → ∀ Y : Subgroup G, IsCoatom Y → IsTypeI Y →
        2 ≤ elementaryAbelianPRank q ↥Y → q ∣ Nat.card ↥(hallCoreOf Y)) →
      ∀ M L : Subgroup G, IsCoatom M → IsCoatom L → IsTypeI M → IsTypeI L →
        ∀ P : Subgroup G, P ≤ M → IsMulCommutative ↥P → IsPGroup p ↥P →
          elementaryAbelianPRank p ↥P = 2 → P ≤ sigmaCore L →
          ∀ x ∈ P, orderOf x = p →
            normalizer ((zpowers x : Subgroup G) : Set G) ≤ M →
            ¬ centralizer ({x} : Set G) ≤ L →
            P ≤ hallCoreOf L ∧
            (∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧
              FreeCore.IsInternalSemidirectProduct L (hallCoreOf L) U ∧
              IsFixedPointFreeOn (hallCoreOf L) U) ∧
            FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (M ⊓ L) ∧
            IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) M

@[expose]
def FPF_type_ii_nonfrobenius_crossed_column_data : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ N E W₁ W₂ : Subgroup G, IsCoatom N → IsTypeII N →
      IsWitnessedPConfiguration N E W₂ W₁ →
      ∀ (I J : Type v) [Fintype I] [Fintype J]
        (a : I → (↥W₁ → ℂ)) (b : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J),
        Function.Injective a → Set.range a = Irr ↥W₁ → a i₀ = 1 →
        Function.Injective b → Set.range b = Irr ↥W₂ → b j₀ = 1 →
      ∀ w : I → J → (↥(W₁ ⊔ W₂) → ℂ),
        (∀ (i : I) (j : J) (x y : G) (hx : x ∈ W₁) (hy : y ∈ W₂)
          (hxy : x * y ∈ W₁ ⊔ W₂),
            w i j ⟨x * y, hxy⟩ = a i ⟨x, hx⟩ * b j ⟨y, hy⟩) →
      ∀ ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G,
        (∀ f g, cfIP ((ω f : G → ℂ)) ((ω g : G → ℂ)) =
          cfIP ((f : ↥(W₁ ⊔ W₂) → ℂ)) ((g : ↥(W₁ ⊔ W₂) → ℂ))) →
        (∀ f : classFun ↥(W₁ ⊔ W₂), (f : ↥(W₁ ⊔ W₂) → ℂ) ∈ virtualChars ↥(W₁ ⊔ W₂) →
          (ω f : G → ℂ) ∈ virtualChars G) →
        (∀ f : classFun ↥(W₁ ⊔ W₂), (f : ↥(W₁ ⊔ W₂) → ℂ) = 1 → (ω f : G → ℂ) = 1) →
        (∀ f : classFun ↥(W₁ ⊔ W₂),
          (∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ → (f : ↥(W₁ ⊔ W₂) → ℂ) z = 0) →
          (ω f : G → ℂ) = indToTop (W₁ ⊔ W₂) (f : ↥(W₁ ⊔ W₂) → ℂ)) →
      ∀ η : I → J → (G → ℂ),
        (∀ (i : I) (j : J) (hw : w i j ∈ classFun ↥(W₁ ⊔ W₂)),
          η i j = (ω ⟨w i j, hw⟩ : G → ℂ)) →
        (∃ e ∈ E, e ≠ 1 ∧ centralizerIn (hallCoreOf N) (zpowers e) ≠ ⊥) →
          ∃ i₁ : I, i₁ ≠ i₀ ∧ ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
            ∃ lam : G → ℂ, lam ∈ virtualChars G ∧ IsSignedIrr lam ∧
              lam ≠ cconj lam ∧
              (∀ i j, cfIP lam (η i j) = 0) ∧
              (∀ z : G, z ∉ conjClosure (fixedSet (⁅N, N⁆ : Subgroup G) (hallCoreOf N)) →
                (lam - cconj lam) z = 0) ∧
              ∀ z : G, z ∉ conjClosure (fixedSet (⁅N, N⁆ : Subgroup G) (hallCoreOf N)) →
                (ε • (∑ j : J, η i₁ j) - lam) z = 0

@[expose]
def FPF_type_iii_full_support_ti_induction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsTypeIII M →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ A₀ : Set G,
        A₀ = ((((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) ∪
          ⋃ m ∈ (M : Set G), conjSet (cyclicTIset W₁ W₂) m) →
        A₀.Nonempty ∧ normalizer A₀ = M ∧
        (∀ g : G, g ∉ M → A₀ ∩ conjSet A₀ g = ∅) ∧
        (∀ a ∈ A₀, centralizer ({a} : Set G) = centralizerIn M (zpowers a) ∧
          derSignalizer M a = ⊥) ∧
        ∀ f : ↥M → ℂ, IsClassFun f → (∀ z : ↥M, (z : G) ∉ A₀ → f z = 0) →
          tauDerived M W₁ W₂ f = indToTop M f

@[expose]
def FPF_type_iii_iv_chief_data : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ p q : ℕ, p = Nat.card ↥W₂ → q = Nat.card ↥W₁ →
        p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧ U ≠ ⊥ ∧
        FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (U ⊔ W₁) ∧
        FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁ ∧
        Nat.Coprime (Nat.card ↥(hallCoreOf M)) (Nat.card ↥(U ⊔ W₁)) ∧
        IsFixedPointFreeOn U W₁ ∧
        centralizerIn (hallCoreOf M) W₁ = W₂ ∧
        centralizerIn U (hallCoreOf M) < U ∧
        IsInternalDirectProduct (fittingOf M) (hallCoreOf M) (centralizerIn U (hallCoreOf M)) ∧
        M ≤ normalizer ((centralizerIn U (hallCoreOf M) : Subgroup G) : Set G) ∧
        (∃ H₀ : Subgroup G, centralizerIn (hallCoreOf M) U ≤ H₀ ∧
          IsChiefLayer M H₀ (hallCoreOf M)) ∧
        ∀ H₀ : Subgroup G, centralizerIn (hallCoreOf M) U ≤ H₀ →
          IsChiefLayer M H₀ (hallCoreOf M) →
          IsElemAbelianLayer p q H₀ (hallCoreOf M) ∧
          H₀ ⊓ W₂ = ⊥ ∧
          M ≤ normalizer ((H₀ ⊔ centralizerIn U (hallCoreOf M) : Subgroup G) : Set G) ∧
          IsInternalDirectProduct (H₀ ⊔ centralizerIn U (hallCoreOf M)) H₀
            (centralizerIn U (hallCoreOf M)) ∧
          (H₀.subgroupOf (hallCoreOf M)).Normal ∧
          ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf (fittingOf M)).Normal ∧
          ∀ (_ : (H₀.subgroupOf (hallCoreOf M)).Normal)
            (_ : ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf (fittingOf M)).Normal),
            Nonempty
              ((↥(fittingOf M) ⧸
                  (H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf (fittingOf M)) ≃*
                (↥(hallCoreOf M) ⧸ H₀.subgroupOf (hallCoreOf M)))

@[expose]
def FPF_type_iii_iv_chief_kernel_centralized : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ H₀ : Subgroup G, centralizerIn (hallCoreOf M) U ≤ H₀ →
        IsChiefLayer M H₀ (hallCoreOf M) → ⁅U, H₀⁆ = ⊥

@[expose]
def FPF_type_iii_iv_chief_kernel_is_derived : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ H₀ : Subgroup G, centralizerIn (hallCoreOf M) U ≤ H₀ →
        IsChiefLayer M H₀ (hallCoreOf M) → H₀ = ⁅hallCoreOf M, hallCoreOf M⁆

@[expose]
def FPF_type_iii_iv_chief_layer_noncoherence : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOdd G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
      IsWitnessedPConfiguration M U W₁ W₂ →
      ∀ H₀ : Subgroup G, centralizerIn (hallCoreOf M) U ≤ H₀ →
        IsChiefLayer M H₀ (hallCoreOf M) →
        ¬ ∃ ν : Submodule.span ℤ
            (derivedIndFamKer M (H₀ ⊔ centralizerIn U (hallCoreOf M))) →+ (G → ℂ),
          IsCoherentAt M (derivedIndFamKer M (H₀ ⊔ centralizerIn U (hallCoreOf M)))
            (tauDerived M W₁ W₂) ν

end Statements

end CFSG.FeitThompson
