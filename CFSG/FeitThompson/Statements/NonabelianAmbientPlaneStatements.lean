module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.OddOrder.SharedSylowNormalizedByIntersection
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

structure IsOddSimpleMinimal (G : Type*) [Group G] [Finite G] : Prop where
  odd_natCard : Odd (Nat.card G)
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  isSolvable_of_ne_top : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H

@[expose]
def maximals (G : Type*) [Group G] : Set (Subgroup G) := {M : Subgroup G | IsCoatom M}

theorem mem_maximals {M : Subgroup G} : M ∈ maximals G ↔ IsCoatom M := Iff.rfl

theorem natCard_hallCoreIn (M : Subgroup G) :
    Nat.card (hallCoreIn M) = Nat.card (hallCore M) := by
  rw [hallCoreIn_eq, Subgroup.card_subtype]

theorem coe_hallCoreSharp (M : Subgroup G) :
    hallCoreSharp M = (hallCoreIn M : Set G) \ {1} := by
  rw [hallCoreSharp_eq, hallCoreIn_eq]

theorem fittingIn_eq [Finite G] (M : Subgroup G) :
    fittingIn M = (fittingRaw M).map M.subtype := (rfl)

@[expose]
def betaCoreIn [Finite G] (M : Subgroup G) : Subgroup G :=
  (piCore (betaPrimes M) M).map M.subtype

theorem betaCoreIn_eq [Finite G] (M : Subgroup G) :
    betaCoreIn M = (piCore (betaPrimes M) M).map M.subtype := (rfl)

theorem betaCoreIn_le [Finite G] (M : Subgroup G) : betaCoreIn M ≤ M := by
  rw [betaCoreIn_eq]; exact Subgroup.map_subtype_le _

theorem mem_conjSubgroup' {Y : Subgroup G} {g x : G} :
    x ∈ conjSubgroup Y g ↔ g * x * g⁻¹ ∈ Y := by
  rw [conjSubgroup_eq]
  simp only [Subgroup.mem_map]
  refine ⟨?_, fun h => ⟨g * x * g⁻¹, h, by simp only [MulAut.conj_apply, MonoidHom.coe_coe]; group⟩⟩
  rintro ⟨y, hy, rfl⟩
  simpa only [MulAut.conj_apply, MonoidHom.coe_coe, mul_assoc, inv_mul_cancel, mul_one,
    mul_inv_cancel_left] using hy

theorem coe_conjSubgroup' (Y : Subgroup G) (g : G) :
    (conjSubgroup Y g : Set G) = (fun y => g⁻¹ * y * g) '' (Y : Set G) := by
  rw [conjSubgroup_eq, Subgroup.coe_map]
  simp [MulAut.conj]

theorem natCard_conjSubgroup (Y : Subgroup G) (g : G) :
    Nat.card (conjSubgroup Y g) = Nat.card Y := by
  rw [conjSubgroup_eq]
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

@[expose]
def IsSylowSubgroup (p : ℕ) (R : Subgroup G) : Prop := ∃ S : Sylow p G, (S : Subgroup G) = R

@[expose]
def IsSylowIn (p : ℕ) (K R : Subgroup G) : Prop :=
  ∃ S : Sylow p K, (S : Subgroup K).map K.subtype = R

theorem IsSylowIn.le {p : ℕ} {K R : Subgroup G} (h : IsSylowIn p K R) : R ≤ K := by
  obtain ⟨S, rfl⟩ := h; exact Subgroup.map_subtype_le _

theorem isSylowIn_iff_natCard [Finite G] {p : ℕ} (hp : p.Prime) {K R : Subgroup G}
    (hRK : R ≤ K) :
    IsSylowIn p K R ↔ Nat.card R = p ^ (Nat.card K).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  exact (natCard_eq_pow_factorization_iff_exists_sylow hRK).symm

theorem isSylowSubgroup_iff_natCard [Finite G] {p : ℕ} (hp : p.Prime) {R : Subgroup G} :
    IsSylowSubgroup p R ↔ Nat.card R = p ^ (Nat.card G).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, fun h => ⟨Sylow.ofCard R h, Sylow.coe_ofCard _ _⟩⟩
  rintro ⟨S, rfl⟩
  exact S.card_eq_multiplicity

theorem IsElementaryAbelianPlane.mem_elementaryAbelianRanks {p : ℕ} {A : Subgroup G}
    (h : IsElementaryAbelianPlane p A) : 2 ∈ elementaryAbelianRanks p G :=
  CFSG.FeitThompson.mem_elementaryAbelianRanks.2 ⟨A, h⟩

theorem IsElementaryAbelianPlane.natCard' {p : ℕ} {A : Subgroup G}
    (h : IsElementaryAbelianPlane p A) : Nat.card A = p ^ 2 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]

theorem IsElementaryAbelianPlane.isElementaryAbelianSubgroup {p : ℕ} {A : Subgroup G}
    (h : IsElementaryAbelianPlane p A) : IsElementaryAbelianSubgroup p A := by
  obtain ⟨e⟩ := h
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact congrArg (Subgroup.subtype A)
      (e.injective (a₁ := (⟨x, hx⟩ : A) * ⟨y, hy⟩) (a₂ := (⟨y, hy⟩ : A) * ⟨x, hx⟩)
        (by rw [map_mul, map_mul, _root_.mul_comm]))
  · exact congrArg (Subgroup.subtype A)
      (e.injective (a₁ := (⟨x, hx⟩ : A) ^ p) (a₂ := 1)
        (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one]))

theorem IsElementaryAbelianPlane.two_le_elementaryAbelianPRank [Finite G] {p : ℕ} (hp : p.Prime)
    {A : Subgroup G} (h : IsElementaryAbelianPlane p A) : 2 ≤ elementaryAbelianPRank p G :=
  le_elementaryAbelianPRank hp.one_lt h.mem_elementaryAbelianRanks

@[expose]
def primeDivisorsOf (X : Type*) [Group X] : Set ℕ := {q : ℕ | q.Prime ∧ q ∣ Nat.card X}

theorem mem_primeDivisorsOf {X : Type*} [Group X] {q : ℕ} :
    q ∈ primeDivisorsOf X ↔ q.Prime ∧ q ∣ Nat.card X := Iff.rfl

@[expose]
def piOnePrimes' (X : Type*) [Group X] : Set ℕ :=
  {q ∈ primeDivisorsOf X | (∀ P : Sylow q X, IsCyclic (P : Subgroup X)) ∧
    ¬ q ∣ Nat.card (commutator X)}

@[expose]
def piTwoPrimes' (X : Type*) [Group X] : Set ℕ :=
  {q ∈ primeDivisorsOf X | ∀ P : Sylow q X, ¬ IsCyclic (P : Subgroup X)}

@[expose]
def piThreePrimes' (X : Type*) [Group X] : Set ℕ :=
  {q ∈ primeDivisorsOf X | (∀ P : Sylow q X, IsCyclic (P : Subgroup X)) ∧
    q ∣ Nat.card (commutator X)}

theorem piOnePrimes'_subset (X : Type*) [Group X] : piOnePrimes' X ⊆ primeDivisorsOf X :=
  fun _ h => h.1

theorem piTwoPrimes'_subset (X : Type*) [Group X] : piTwoPrimes' X ⊆ primeDivisorsOf X :=
  fun _ h => h.1

theorem piThreePrimes'_subset (X : Type*) [Group X] : piThreePrimes' X ⊆ primeDivisorsOf X :=
  fun _ h => h.1

@[expose]
noncomputable def signalizer [Finite G] (a : G) : Subgroup G :=
  canonicalSignalizer (maximals G) sigmaCore a

theorem signalizer_eq [Finite G] (a : G) :
    signalizer a = canonicalSignalizer (maximals G) sigmaCore a := (rfl)

theorem signalizer_le_centralizer [Finite G] (a : G) :
    signalizer a ≤ centralizer ({a} : Set G) := canonicalSignalizer_le_centralizer

structure IsSigmaComplement [Finite G] (M E : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  isInternalSemidirectProduct : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E

theorem IsSigmaComplement.le [Finite G] {M E : Subgroup G} (h : IsSigmaComplement M E) : E ≤ M :=
  h.isInternalSemidirectProduct.right_le

structure IsOutsideSigmaPlane [Finite G] (p : ℕ) (M A : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  prime : p.Prime
  notMem_sigmaPrimes : p ∉ sigmaPrimes M
  le : A ≤ M
  isElementaryAbelianPlane : IsElementaryAbelianPlane p A

structure IsTauHallSplitting [Finite G] (M E E₁ E₂ E₃ : Subgroup G) : Prop where
  le_E₁ : E₁ ≤ E
  le_E₂ : E₂ ≤ E
  le_E₃ : E₃ ≤ E
  isHall_E₁ : IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E)
  isHall_E₂ : IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf E)
  isHall_E₃ : IsHallPiSubgroup (tau3Primes M) (E₃.subgroupOf E)
  outer : FreeCore.IsInternalSemidirectProduct E E₃ (E₂ ⊔ E₁)
  inner : FreeCore.IsInternalSemidirectProduct (E₂ ⊔ E₁) E₂ E₁

structure IsNormalizedTauHallSplitting [Finite G] (M E E₁ E₂ E₃ : Subgroup G) : Prop
    extends IsTauHallSplitting M E E₁ E₂ E₃ where
  isCyclic_E₁ : IsCyclic E₁
  isCyclic_E₃ : IsCyclic E₃
  le_commutator_E₃ : E₃ ≤ ⁅E, E⁆
  normal_E₂_sup_E₃ : E ≤ normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G)
  centralizer_E₃ : E₃ ⊓ centralizer (E : Set G) = ⊥

structure IsPairedSupportingSetup [Finite G] (S T L U V W₁ W₂ : Subgroup G) (y : G) : Prop where
  isCoatom_S : IsCoatom S
  isCoatom_T : IsCoatom T
  ne_S_T : S ≠ T
  config_S : IsWitnessedPConfiguration S U W₁ W₂
  config_T : IsWitnessedPConfiguration T V W₂ W₁
  isTypeII_S : IsTypeII S
  natCard_lt : Nat.card W₁ < Nat.card W₂
  isCoatom_L : IsCoatom L
  le_hallCoreIn_L : U ≤ hallCoreIn L
  mem_y : y ∈ hallCoreIn T
  isInternalSemidirectProduct :
    FreeCore.IsInternalSemidirectProduct L (hallCoreIn L) (W₁ ⊔ conjSubgroup W₂ y)
  centralizer_eq_bot : ∀ e ∈ W₁ ⊔ conjSubgroup W₂ y, e ≠ 1 →
    hallCoreIn L ⊓ centralizer ({e} : Set G) = ⊥

open Classical in
@[expose]
noncomputable def indFamNonprincipal [Fintype G] (X : Subgroup G) : Set (X → ℂ) :=
  indFam (hallCore X)
    (Irr (hallCore X) \ {(principalClassFun (hallCore X) : (hallCore X) → ℂ)})

open Classical in
@[expose]
noncomputable def coreTau [Fintype G] (X : Subgroup G) (f : X → ℂ) : G → ℂ :=
  dadeSupportExtension (hallCoreSharp X) signalizer (Function.extend X.subtype f 0)

theorem coreTau_eq [Fintype G] (X : Subgroup G) (f : X → ℂ) :
    coreTau X f =
      dadeSupportExtension (hallCoreSharp X) signalizer (Function.extend X.subtype f 0) := (rfl)

open Classical in
structure IsCoreCharData [Fintype G] (X : Subgroup G) (ν : (X → ℂ) → (G → ℂ)) (φ : X → ℂ)
    (β : G → ℂ) : Prop where
  map_add : ∀ f g : X → ℂ, f ∈ Submodule.span ℤ (indFamNonprincipal X) →
    g ∈ Submodule.span ℤ (indFamNonprincipal X) → ν (f + g) = ν f + ν g
  mem_virtualChars : ∀ f : X → ℂ, f ∈ Submodule.span ℤ (indFamNonprincipal X) →
    ν f ∈ virtualChars G
  inner_eq : ∀ f g : X → ℂ, f ∈ Submodule.span ℤ (indFamNonprincipal X) →
    g ∈ Submodule.span ℤ (indFamNonprincipal X) → cfInner (ν f) (ν g) = cfInner f g
  eq_coreTau : ∀ f : X → ℂ, f ∈ Submodule.span ℤ (indFamNonprincipal X) → f 1 = 0 →
    ν f = coreTau X f
  mem_φ : φ ∈ indFamNonprincipal X
  φ_apply_one : φ 1 = ((hallCore X).index : ℂ)
  β_eq : β = coreTau X
    (indClassFun (hallCore X) (principalClassFun (hallCore X) : (hallCore X) → ℂ) - φ)

namespace Statements

@[expose]
def FNI_nonabelian_ambient_sylow_centralizing_kernel : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      (∃ P : Subgroup G, IsSylowSubgroup p P ∧ ¬ IsMulCommutative P) →
      ∀ P : Subgroup G, IsSylowIn p E P → A ≤ P →
        (∃ Y : Subgroup G, Y ≠ ⊥ ∧ IsCyclic Y ∧
            IsInternalDirectProduct P (A ⊓ centralizer (sigmaCore M : Set G)) Y ∧
            Y ⊓ centralizer (sigmaCore M : Set G) = ⊥) ∧
          P ⊓ centralizer (sigmaCore M : Set G) = A ⊓ centralizer (sigmaCore M : Set G)

@[expose]
def FNI_nonabelian_ambient_unique_nonregular_line : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      (∃ P : Subgroup G, IsSylowSubgroup p P ∧ ¬ IsMulCommutative P) →
      ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A₀ = p ∧
        sigmaCore M ⊓ centralizer (A₀ : Set G) = sigmaCore M ∧
        (∀ X : Subgroup G, X ≤ E → Nat.card X = p → X ≠ A₀ →
          sigmaCore M ⊓ centralizer (X : Set G) = ⊥ ∧ ¬ centralizer (X : Set G) ≤ M) ∧
        A₀ = A ⊓ centralizer (sigmaCore M : Set G) ∧
        A₀ ≤ M ∧ M ≤ normalizer (A₀ : Set G)

@[expose]
def FNI_nonabelian_common_overgroup_sylow : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M T P : Subgroup G), IsCoatom M → IsCoatom T → M ≠ T → p.Prime →
      P ≤ M ⊓ T → IsPGroup p P → ¬ IsMulCommutative P →
      Odd p ∧
        (∃ R : Subgroup G, ¬ IsMulCommutative R ∧ P ≤ R ∧
          IsSylowIn p (M ⊓ T) R ∧ IsSylowIn p M R ∧ IsSylowIn p T R ∧
          IsSylowSubgroup p R ∧ normalizer (R : Set G) ≤ M ⊓ T ∧
          elementaryAbelianPRank p R = 2) ∧
        p ∈ sigmaPrimes M ∧ p ∈ sigmaPrimes T

@[expose]
def FNI_nonabelian_prime_subgroup_unique_maximum : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p a : ℕ) (P : Subgroup G), p.Prime → 1 ≤ a → Nat.card P = p ^ a → ¬ IsMulCommutative P →
      ∃! M : Subgroup G, IsCoatom M ∧ P ≤ M

@[expose]
def FNI_nonconjugate_maxima_hall_cores_coprime : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ L M : Subgroup G, IsCoatom L → IsCoatom M → (∀ g : G, conjSubgroup M g ≠ L) →
      Nat.Coprime (Nat.card (hallCoreIn L)) (Nat.card (hallCoreIn M)) ∧
        (hallCoreIn L ≠ ⊥ → hallCoreIn M ≠ ⊥ →
          Nat.card (hallCoreIn L) ≠ Nat.card (hallCoreIn M))

@[expose]
def FNI_nonregular_plane_line_unique_centralizer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E X : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      X ≤ E → Nat.card X = p → sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥ →
      IsUniqueMaximalOvergroup (centralizer (X : Set G)) M ∧ normalizer (X : Set G) ≤ M

@[expose]
def FNI_ordered_outer_prime_forces_type_II : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M U W₁ W₂ →
      Nat.card W₁ < Nat.card W₂ → IsTypeII M

@[expose]
def FNI_ordered_pair_full_supporting_complement : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ S T U V W₁ W₂ L : Subgroup G, IsCoatom S → IsCoatom T → S ≠ T →
      IsWitnessedPConfiguration S U W₁ W₂ → IsWitnessedPConfiguration T V W₂ W₁ →
      IsCyclic ↥(W₁ ⊔ W₂) → S ⊓ T = W₁ ⊔ W₂ →
      (∀ N : Subgroup G, IsCoatom N → ¬ IsTypeI N →
        (∃ g : G, conjSubgroup S g = N) ∨ (∃ g : G, conjSubgroup T g = N)) →
      Nat.card W₁ < Nat.card W₂ →
      IsCoatom L → normalizer (U : Set G) ≤ L →
      IsTypeII S ∧ IsTypeI L ∧ U ≤ hallCoreIn L ∧
        ∃ y ∈ hallCoreIn T,
          FreeCore.IsInternalSemidirectProduct L (hallCoreIn L) (W₁ ⊔ conjSubgroup W₂ y) ∧
          (∀ e ∈ W₁ ⊔ conjSubgroup W₂ y, e ≠ 1 →
            hallCoreIn L ⊓ centralizer ({e} : Set G) = ⊥) ∧
          (hallCoreIn L).relIndex L = Nat.card W₂ * Nat.card W₁

@[expose]
def FNI_outside_sigma_kappa_sylow_core_nilpotent : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M P : Subgroup G), IsCoatom M → p.Prime → p ∣ Nat.card M →
      p ∉ sigmaPrimes M ∪ kappaPrimes M → IsSylowIn p M P →
      IsMulCommutative P ∧
        (∃ A : Subgroup G, (A : Set G) = {x ∈ (P : Set G) | x ^ p = 1} ∧
          IsElementaryAbelianSubgroup p A ∧ (Nat.card A = p ∨ Nat.card A = p ^ 2) ∧
          sigmaCore M ⊓ centralizer (A : Set G) = ⊥) ∧
        Group.IsNilpotent (sigmaCore M)

@[expose]
def FNI_outside_sigma_plane_complement_normalizer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      E ≤ normalizer (A : Set G) ∧
        (∀ X : Subgroup G, X ≤ E → Nat.card X = p → X ≤ A) ∧
        centralizer (A : Set G) ≤ E ∧
        normalizer (A : Set G) ⊓ M = E ∧
        ¬ normalizer (A : Set G) ≤ M

@[expose]
def FNI_outside_sigma_plane_core_disjoint : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A L : Subgroup G), IsOutsideSigmaPlane p M A →
      IsCoatom L → L ≠ M → A ≤ L → sigmaCore M ⊓ L = ⊥

@[expose]
def FNI_outside_sigma_plane_sylow : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A : Subgroup G), IsOutsideSigmaPlane p M A →
      elementaryAbelianPRank p M = 2 ∧
        Maximal (IsElementaryAbelianSubgroup p) A ∧
        (∀ P : Subgroup G, IsSylowIn p M P → IsMulCommutative P ∧
          (A ≤ P → (A : Set G) = {x ∈ (P : Set G) | x ^ p = 1} ∧
            ¬ normalizer (P : Set G) ≤ M)) ∧
        ∃ A₁ : Subgroup G, A₁ ≤ A ∧ Nat.card A₁ = p ∧
          sigmaCore M ⊓ centralizer (A₁ : Set G) = ⊥

@[expose]
def FNI_p_configuration_kappa_factors : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ M E W₁ W₂ : Subgroup G, IsCoatom M → IsWitnessedPConfiguration M E W₁ W₂ →
      (kappaPrimes M).Nonempty ∧
        IsHallPiSubgroup (kappaPrimes M) (W₁.subgroupOf M) ∧
        sigmaCore M ⊓ centralizer (W₁ : Set G) = W₂

@[expose]
def FNI_paired_full_support_forces_field_action : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (S T L U V W₁ W₂ : Subgroup G) (y : G), IsPairedSupportingSetup S T L U V W₁ W₂ y →
      ∀ K : Subgroup G, K ≤ hallCoreIn S → (∀ u ∈ U, conjSubgroup K u ≤ K) →
        K = ⊥ ∨ K = hallCoreIn S

@[expose]
def FNI_paired_full_support_inner_not_characteristic : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (S T L U V W₁ W₂ : Subgroup G) (y : G), IsPairedSupportingSetup S T L U V W₁ W₂ y →
      ¬ (U.subgroupOf (hallCoreIn L)).Characteristic

@[expose]
def FNI_paired_p_configurations_prime_factors : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ S T U V W₁ W₂ : Subgroup G, IsCoatom S → IsCoatom T → S ≠ T →
      IsWitnessedPConfiguration S U W₁ W₂ → IsWitnessedPConfiguration T V W₂ W₁ →
      (Nat.card W₂).Prime ∧ (Nat.card W₁).Prime ∧ Odd (Nat.card W₂) ∧ Odd (Nat.card W₁) ∧
        Nat.card W₂ ≠ Nat.card W₁

@[expose]
def FNI_paired_supporting_crossed_alternatives : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G], IsOddSimpleMinimal G →
    ∀ (S T L U V W₁ W₂ : Subgroup G) (y : G), IsPairedSupportingSetup S T L U V W₁ W₂ y →
      IsTypeI L → (hallCoreIn L).relIndex L = Nat.card W₂ * Nat.card W₁ →
      ∀ M : Subgroup G, IsCoatom M → IsTypeI M → hallCoreIn M = V →
        (hallCoreIn M).relIndex M = Nat.card W₂ * Nat.card W₁ →
      ∀ (νL : (L → ℂ) → (G → ℂ)) (φL : L → ℂ) (βL : G → ℂ), IsCoreCharData L νL φL βL →
      ∀ (νM : (M → ℂ) → (G → ℂ)) (φM : M → ℂ) (βM : G → ℂ), IsCoreCharData M νM φM βM →
        (cfInner βM (νL φL) ≠ 0 ∧
            ((Nat.card (hallCoreIn L) : ℚ) - 1) / ((Nat.card W₂ : ℚ) * (Nat.card W₁ : ℚ)) ≤
              (Nat.card W₂ : ℚ) * (Nat.card W₁ : ℚ) - 1) ∨
          (cfInner βL (νM φM) ≠ 0 ∧ Nat.card W₁ = 3 ∧ Nat.card W₂ = 5)

@[expose]
def FNI_paired_supporting_inner_full_norm_order : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G], IsOddSimpleMinimal G →
    ∀ (S T L U V W₁ W₂ : Subgroup G) (y : G), IsPairedSupportingSetup S T L U V W₁ W₂ y →
      IsTypeI L → (hallCoreIn L).relIndex L = Nat.card W₂ * Nat.card W₁ →
      ∀ M : Subgroup G, IsCoatom M → IsTypeI M → hallCoreIn M = V →
        (hallCoreIn M).relIndex M = Nat.card W₂ * Nat.card W₁ →
      ∀ (νL : (L → ℂ) → (G → ℂ)) (φL : L → ℂ) (βL : G → ℂ), IsCoreCharData L νL φL βL →
      ∀ (νM : (M → ℂ) → (G → ℂ)) (φM : M → ℂ) (βM : G → ℂ), IsCoreCharData M νM φM βM →
        (Nat.card U : ℚ) =
          ((Nat.card W₂ : ℚ) ^ Nat.card W₁ - 1) / ((Nat.card W₂ : ℚ) - 1)

@[expose]
def FNI_paired_supporting_kernel_collapse : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G], IsOddSimpleMinimal G →
    ∀ (S T L U V W₁ W₂ : Subgroup G) (y : G), IsPairedSupportingSetup S T L U V W₁ W₂ y →
      IsTypeI L → (hallCoreIn L).relIndex L = Nat.card W₂ * Nat.card W₁ →
      ∀ M : Subgroup G, IsCoatom M → IsTypeI M → hallCoreIn M = V →
        (hallCoreIn M).relIndex M = Nat.card W₂ * Nat.card W₁ →
      ∀ (νL : (L → ℂ) → (G → ℂ)) (φL : L → ℂ) (βL : G → ℂ), IsCoreCharData L νL φL βL →
      ∀ (νM : (M → ℂ) → (G → ℂ)) (φM : M → ℂ) (βM : G → ℂ), IsCoreCharData M νM φM βM →
        hallCoreIn L = U

@[expose]
def FNI_paired_supporting_maxima_nonconjugate : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (S T L U V W₁ W₂ : Subgroup G) (y : G), IsPairedSupportingSetup S T L U V W₁ W₂ y →
      ∀ M : Subgroup G, IsCoatom M → hallCoreIn M = V → ∀ g : G, L ≠ conjSubgroup M g

@[expose]
def FNI_plane_normalizer_action_prime_transfer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E T : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      IsCoatom T → normalizer (A : Set G) ≤ T →
      ∀ q : ℕ, q.Prime → q ∣ (E ⊓ centralizer (A : Set G)).relIndex E →
        q ∈ tau1Primes T ∨ q ∈ tauTwoPrimes T

@[expose]
def FNI_plane_normalizer_overlap_ambient_sylows : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E T : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      IsCoatom T → normalizer (A : Set G) ≤ T →
      ∀ q : ℕ, q.Prime → q ∣ (E ⊓ centralizer (A : Set G)).relIndex E →
        q ∣ Nat.card (E ⊓ centralizer (A : Set G) : Subgroup G) →
        (∃ P : Subgroup G, IsSylowSubgroup p P ∧ P ≤ T ∧ T ≤ normalizer (P : Set G)) ∧
          (∃ R : Subgroup G, IsSylowSubgroup q R ∧ IsMulCommutative R ∧ R ≤ T)

@[expose]
def FNI_plane_normalizer_overlap_frattini : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E T : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      IsCoatom T → normalizer (A : Set G) ≤ T →
      ∀ q : ℕ, q.Prime → q ∣ (E ⊓ centralizer (A : Set G)).relIndex E →
        q ∣ Nat.card (E ⊓ centralizer (A : Set G) : Subgroup G) →
      ∀ Q₀ Q : Subgroup G, Q₀ ≤ E ⊓ centralizer (A : Set G) → Nat.card Q₀ = q →
        IsSylowIn q E Q → Q₀ ≤ Q →
        q ∈ tau1Primes M ∧ IsCyclic Q ∧
          centralizer (A : Set G) = E ⊓ centralizer (A : Set G) ∧
          E ≤ normalizer (centralizer (A : Set G) : Set G) ∧
          normalizer (A : Set G) ≤ normalizer (centralizer (A : Set G) : Set G) ∧
          IsSylowIn q (centralizer (A : Set G)) (Q ⊓ centralizer (A : Set G)) ∧
          (normalizer (A : Set G) : Set G) = (centralizer (A : Set G) : Set G) *
            ((normalizer (A : Set G) ⊓ normalizer (Q₀ : Set G) : Subgroup G) : Set G)

@[expose]
def FNI_plane_normalizer_overlap_prime_maximum : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E T : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      IsCoatom T → normalizer (A : Set G) ≤ T →
      ∀ q : ℕ, q.Prime → q ∣ (E ⊓ centralizer (A : Set G)).relIndex E →
        q ∣ Nat.card (E ⊓ centralizer (A : Set G) : Subgroup G) →
      ∀ Q₀ : Subgroup G, Q₀ ≤ E ⊓ centralizer (A : Set G) → Nat.card Q₀ = q →
        q ∈ tauTwoPrimes T ∧ normalizer (Q₀ : Set G) ≤ T

@[expose]
def FNI_plane_normalizer_rank_two_primes_in_sigma : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E T : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      IsCoatom T → normalizer (A : Set G) ≤ T →
      T ≠ M ∧ tauTwoPrimes M ⊆ sigmaPrimes T

@[expose]
def FNI_prime_cube_centralizer_in_competing_maximum : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M T Q D : Subgroup G), IsCoatom M → IsCoatom T → p.Prime → Odd p →
      Q ≤ M ⊓ T → ¬ IsMulCommutative Q → Nat.card Q = p ^ 3 → (∀ x ∈ Q, x ^ p = 1) →
      D ≤ M → M ≤ normalizer (D : Set G) → Nat.Coprime (Nat.card D) p →
      D ⊓ centralizer ((Q ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) ≤ T

@[expose]
def FNI_rank_one_plane_centralizer_regular : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E : Subgroup G), IsOutsideSigmaPlane p M A → IsSigmaComplement M E → A ≤ E →
      ∀ (q : ℕ) (Q : Subgroup G), q.Prime → q ∉ sigmaPrimes M → elementaryAbelianPRank q M = 1 →
        Q ≤ E ⊓ centralizer (A : Set G) → Nat.card Q = q →
        sigmaCore M ⊓ centralizer (Q : Set G) = ⊥

@[expose]
def FNI_regular_first_plane_fixed_line_escape : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p q : ℕ) (M E A Q : Subgroup G), IsSigmaComplement M E →
      p ∈ tauTwoPrimes M → A ≤ E → IsElementaryAbelianPlane p A →
      q ∈ tau1Primes M → Q ≤ E → Nat.card Q = q →
      sigmaCore M ⊓ centralizer (Q : Set G) = ⊥ → ⁅A, Q⁆ ≠ ⊥ →
      Nat.card (⁅A, Q⁆ : Subgroup G) = p ∧
        Nat.card (A ⊓ centralizer (Q : Set G) : Subgroup G) = p ∧
        IsInternalDirectProduct A (⁅A, Q⁆ : Subgroup G) (A ⊓ centralizer (Q : Set G)) ∧
        (⁅A, Q⁆ : Subgroup G) = A ⊓ centralizer (sigmaCore M : Set G) ∧
        ¬ centralizer ((A ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) ≤ M

@[expose]
def FNI_shared_rank_two_controlled_noncentral_line : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M T R Q A : Subgroup G), IsCoatom M → IsCoatom T → M ≠ T → p.Prime → Odd p →
      R ≤ M ⊓ T → ¬ IsMulCommutative R → IsSylowSubgroup p R →
      elementaryAbelianPRank p R = 2 → normalizer (R : Set G) ≤ M ⊓ T →
      Q ≤ R → ¬ IsMulCommutative Q → Nat.card Q = p ^ 3 → (∀ x ∈ Q, x ^ p = 1) →
      A ≤ Q → IsElementaryAbelianPlane p A →
      ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A₀ = p ∧ A₀ ≠ Q ⊓ centralizer (Q : Set G) ∧
        IsUniqueMaximalOvergroup (normalizer (A₀ : Set G)) M

@[expose]
def FNI_shared_rank_two_derived_factor_and_alpha : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M T R : Subgroup G), IsCoatom M → IsCoatom T → M ≠ T → p.Prime → Odd p →
      R ≤ M ⊓ T → ¬ IsMulCommutative R → IsSylowSubgroup p R →
      elementaryAbelianPRank p R = 2 → normalizer (R : Set G) ≤ M ⊓ T →
      pComplCoreIn p (⁅M, M⁆ : Subgroup G) ≤ M ∧
        M ≤ normalizer ((pComplCoreIn p (⁅M, M⁆ : Subgroup G) : Subgroup G) : Set G) ∧
        ¬ p ∣ Nat.card (pComplCoreIn p (⁅M, M⁆ : Subgroup G)) ∧
        (M : Set G) = (pComplCoreIn p (⁅M, M⁆ : Subgroup G) : Set G) *
          ((M ⊓ T : Subgroup G) : Set G) ∧
        alphaCoreIn M ≠ ⊥

@[expose]
def FNI_shared_rank_two_maxima_contradiction : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M T R : Subgroup G), IsCoatom M → IsCoatom T → M ≠ T → p.Prime → Odd p →
      R ≤ M ⊓ T → ¬ IsMulCommutative R → IsSylowSubgroup p R →
      elementaryAbelianPRank p R = 2 → normalizer (R : Set G) ≤ M ⊓ T →
      M = T

@[expose]
def FNI_sigma_complement_prime_data : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ M E : Subgroup G, IsSigmaComplement M E →
      primeDivisorsOf E = primeDivisorsOf M \ sigmaPrimes M ∧
        (∀ q ∈ primeDivisorsOf E, elementaryAbelianPRank q E = elementaryAbelianPRank q M ∧
          elementaryAbelianPRank q M ≤ 2) ∧
        ((⁅M, M⁆ : Subgroup G) : Set G) =
          (sigmaCore M : Set G) * ((⁅E, E⁆ : Subgroup G) : Set G) ∧
        (⁅M, M⁆ : Subgroup G) ⊓ E = ⁅E, E⁆ ∧
        Group.IsNilpotent (⁅E, E⁆ : Subgroup G) ∧
        piOnePrimes' E = tau1Primes M ∧ piTwoPrimes' E = tauTwoPrimes M ∧
        piThreePrimes' E = tau3Primes M

@[expose]
def FNI_sigma_complement_regular_factors : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p : ℕ) (M A E E₁ E₂ E₃ : Subgroup G), IsOutsideSigmaPlane p M A →
      IsSigmaComplement M E → A ≤ E → IsTauHallSplitting M E E₁ E₂ E₃ →
      A ≤ E₂ ∧
        ∀ x : G, x ≠ 1 → (x ∈ E₃ ∨ x ∈ E₁ ⊓ centralizer (A : Set G)) →
          sigmaCore M ⊓ centralizer ({x} : Set G) = ⊥

@[expose]
def FNI_sigma_complement_three_factors : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ M E : Subgroup G, IsSigmaComplement M E →
      ∃ E₁ E₂ E₃ : Subgroup G, IsNormalizedTauHallSplitting M E E₁ E₂ E₃ ∧
        (E ≠ ⊥ → E₂ = ⊥ → E₁ ≠ ⊥)

@[expose]
def FNI_sigma_third_primes_derived_containment : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (q : ℕ) (M : Subgroup G), IsCoatom M → q.Prime →
      (q ∈ sigmaPrimes M ∨ q ∈ tau3Primes M) →
      ∀ Q : Subgroup G, Q ≤ M → (∃ n : ℕ, Nat.card Q = q ^ n) → Q ≤ ⁅M, M⁆

@[expose]
def FNI_tau_three_hall_fixed_centralizer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsSigmaComplement M E →
      IsNormalizedTauHallSplitting M E E₁ E₂ E₃ →
      ∀ X : Subgroup G, X ≤ E₃ → X ≠ ⊥ →
        sigmaCore M ⊓ centralizer (X : Set G) = sigmaCore M ⊓ centralizer (E₃ : Set G)

@[expose]
def FNI_tau12_double_fixed_reflection : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p q : ℕ) (M E P A : Subgroup G), IsSigmaComplement M E →
      p ∈ tau1Primes M → P ≤ E → Nat.card P = p →
      q ∈ tauTwoPrimes M → A ≤ E → IsElementaryAbelianPlane q A →
      A ⊓ centralizer (P : Set G) ≠ ⊥ → sigmaCore M ⊓ centralizer (P : Set G) ≠ ⊥ →
      Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) = q ∧
        IsUniqueMaximalOvergroup
          (centralizer ((A ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) M ∧
        ∀ T : Subgroup G, IsCoatom T → normalizer (A : Set G) ≤ T →
          T ≠ M ∧ E ≤ T ∧ A ≤ sigmaCore T ∧ (p ∈ tau1Primes T ∨ p ∈ tauTwoPrimes T)

@[expose]
def FNI_tau12_fixed_plane_line_core_free : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ (p q : ℕ) (M E P A : Subgroup G), IsSigmaComplement M E →
      p ∈ tau1Primes M → P ≤ E → Nat.card P = p →
      q ∈ tauTwoPrimes M → A ≤ E → IsElementaryAbelianPlane q A →
      A ⊓ centralizer (P : Set G) ≠ ⊥ → sigmaCore M ⊓ centralizer (P : Set G) = ⊥

@[expose]
def FNI_tau13_commuting_prime_fixed_equality : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsSigmaComplement M E →
      IsNormalizedTauHallSplitting M E E₁ E₂ E₃ →
      ∀ (p r : ℕ) (P R : Subgroup G), p ∈ tau1Primes M → P ≤ E₁ → Nat.card P = p →
        r.Prime → R ≤ E₃ ⊓ centralizer (P : Set G) → Nat.card R = r →
        sigmaCore M ⊓ centralizer (P : Set G) = sigmaCore M ⊓ centralizer (R : Set G)

@[expose]
def FNI_tau13_core_fixed_sylow_regular_normalizer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsOddSimpleMinimal G →
    ∀ M E E₁ E₂ E₃ : Subgroup G, IsSigmaComplement M E →
      IsNormalizedTauHallSplitting M E E₁ E₂ E₃ →
      ∀ (p q : ℕ) (P Q : Subgroup G), p ∈ tau1Primes M → P ≤ E₁ → Nat.card P = p →
        q ∈ tau3Primes M → IsSylowIn q E₃ Q → Q ≠ ⊥ →
        Q ⊓ centralizer (P : Set G) = ⊥ →
        alphaPrimes M = betaPrimes M →
        alphaCoreIn M ⊓ centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥ →
      ∀ L : Subgroup G, IsCoatom L → (∀ g : G, conjSubgroup M g ≠ L) → E ≤ L →
        normalizer (Q : Set G) ≤ L →
      ∀ (u : ℕ) (U : Subgroup G), u.Prime →
        u ∣ Nat.card (sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G) →
        IsSylowIn u (sigmaCore M ⊓ centralizer (E₃ : Set G)) U →
        E ≤ normalizer (U : Set G) →
        normalizer (U : Set G) ≤ M ∧ U ⊓ centralizer (P : Set G) = ⊥

end Statements

end

end CFSG.FeitThompson
