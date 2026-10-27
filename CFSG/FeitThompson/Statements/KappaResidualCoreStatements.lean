module

public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.CanonicalCentralizerSignalizerFrom
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Local.PrimeActionChiefFactorsBelowFitting
public import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup FreeCore Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p : ℕ} {A K M P Y : Subgroup G}

structure IsFTAmbient (G : Type*) [Group G] : Prop where
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  odd_natCard : Odd (Nat.card G)
  isSolvable : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H

@[expose]
def maximalSubgroups (G : Type*) [Group G] : Set (Subgroup G) := {M | IsCoatom M}

theorem mem_maximalSubgroups : M ∈ maximalSubgroups G ↔ IsCoatom M := Iff.rfl

@[expose]
def conjBy (Y : Subgroup G) (g : G) : Subgroup G := MulAut.conj g⁻¹ • Y

theorem mem_conjBy {g x : G} : x ∈ conjBy Y g ↔ g * x * g⁻¹ ∈ Y := by
  simp only [conjBy, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]
  simp [mul_assoc]

@[simp] theorem conjBy_one (Y : Subgroup G) : conjBy Y 1 = Y := by ext x; simp [mem_conjBy]

theorem coe_conjBy (Y : Subgroup G) (g : G) :
    (conjBy Y g : Set G) = (fun x : G => g⁻¹ * x * g) '' (Y : Set G) := by
  ext x
  simp only [SetLike.mem_coe, mem_conjBy, Set.mem_image]
  exact ⟨fun h => ⟨g * x * g⁻¹, h, by group⟩, fun ⟨y, hy, hx⟩ => by
    subst hx; simpa [mul_assoc] using hy⟩

theorem natCard_conjBy (Y : Subgroup G) (g : G) : Nat.card ↥(conjBy Y g) = Nat.card ↥Y := by
  rw [conjBy, Subgroup.pointwise_smul_def]
  exact Nat.card_congr (Y.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).symm.toEquiv

theorem conjBy_le_conjBy_iff {X Y : Subgroup G} {g : G} :
    conjBy X g ≤ conjBy Y g ↔ X ≤ Y := by
  simp only [SetLike.le_def, mem_conjBy]
  refine ⟨fun h x hx => ?_, fun h _ hx => h hx⟩
  have hx' : g * (g⁻¹ * x * g) * g⁻¹ ∈ X := by simpa [mul_assoc] using hx
  simpa [mul_assoc] using h hx'

@[expose]
def IsHallSubgroupOf (K M : Subgroup G) : Prop :=
  K ≤ M ∧ Nat.Coprime (Nat.card ↥K) (K.relIndex M)

theorem isHallSubgroupOf_iff :
    IsHallSubgroupOf K M ↔ K ≤ M ∧ Nat.Coprime (Nat.card ↥K) (K.relIndex M) := (Iff.rfl)

theorem IsHallSubgroupOf.le (h : IsHallSubgroupOf K M) : K ≤ M := h.1

@[expose]
def IsHallPiSubgroupOf (π : Set ℕ) (K M : Subgroup G) : Prop :=
  K ≤ M ∧ IsHallPiSubgroup π (K.subgroupOf M)

theorem isHallPiSubgroupOf_iff {π : Set ℕ} :
    IsHallPiSubgroupOf π K M ↔ K ≤ M ∧ IsHallPiSubgroup π (K.subgroupOf M) := (Iff.rfl)

theorem IsHallPiSubgroupOf.le {π : Set ℕ} (h : IsHallPiSubgroupOf π K M) : K ≤ M := h.1

theorem IsHallPiSubgroupOf.isPiSubgroup [Finite G] {π : Set ℕ}
    (h : IsHallPiSubgroupOf π K M) : IsPiSubgroup π K := by
  refine isPiSubgroup_iff.2 fun r hr => isPiSubgroup_iff.1 h.2.isPiSubgroup r ?_
  rwa [← Subgroup.card_subtype M (K.subgroupOf M), Subgroup.map_subgroupOf_eq_of_le h.1]

@[expose]
def IsSylowSubgroupOf (p : ℕ) (P M : Subgroup G) : Prop :=
  P ≤ M ∧ Nat.card ↥P = p ^ (Nat.card ↥M).factorization p

theorem isSylowSubgroupOf_iff :
    IsSylowSubgroupOf p P M ↔ P ≤ M ∧ Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := (Iff.rfl)

theorem IsSylowSubgroupOf.le (h : IsSylowSubgroupOf p P M) : P ≤ M := h.1

@[expose]
def IsElementaryAbelianPlane (p : ℕ) (A : Subgroup G) : Prop :=
  Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p)))

theorem isElementaryAbelianPlane_iff :
    IsElementaryAbelianPlane p A ↔ Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p))) := (Iff.rfl)

theorem IsElementaryAbelianPlane.natCard (hp : p ≠ 0) (h : IsElementaryAbelianPlane p A) :
    Nat.card ↥A = p ^ 2 := by
  obtain ⟨e⟩ := h
  have : NeZero p := ⟨hp⟩
  have h2 : Nat.card (Fin 2 → Multiplicative (ZMod p)) = p ^ 2 := by simp
  rw [Nat.card_congr e.toEquiv, h2]

theorem IsElementaryAbelianPlane.isMulCommutative (h : IsElementaryAbelianPlane p A) :
    IsMulCommutative ↥A := by
  obtain ⟨e⟩ := h
  exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

theorem IsElementaryAbelianPlane.mul_comm (h : IsElementaryAbelianPlane p A) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (h.isMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)

theorem IsElementaryAbelianPlane.two_mem_elementaryAbelianRanks
    (h : IsElementaryAbelianPlane p A) : 2 ∈ elementaryAbelianRanks p G :=
  mem_elementaryAbelianRanks.2 ⟨A, h⟩

@[expose]
def pCoreOf [Finite G] (p : ℕ) (M : Subgroup G) : Subgroup G := (pCore p ↥M).map M.subtype

theorem pCoreOf_le [Finite G] (p : ℕ) (M : Subgroup G) : pCoreOf p M ≤ M := map_subtype_le _

theorem pCoreOf_eq [Finite G] (p : ℕ) (M : Subgroup G) :
    pCoreOf p M = (pCore p ↥M).map M.subtype := (rfl)

@[expose]
def sigmaSupport (G : Type*) [Group G] [Finite G] : Set G :=
  coreFamilySupport (maximalSubgroups G) sigmaCore

theorem sigmaSupport_eq (G : Type*) [Group G] [Finite G] :
    sigmaSupport G = coreFamilySupport (maximalSubgroups G) sigmaCore := (rfl)

theorem mem_sigmaSupport [Finite G] {x : G} :
    x ∈ sigmaSupport G ↔ ∃ M, IsCoatom M ∧ x ∈ sigmaCore M ∧ x ≠ 1 := by
  rw [sigmaSupport, mem_coreFamilySupport_iff]
  simp only [mem_maximalSubgroups]

@[expose]
def sigmaSupportingMaximals [Finite G] (x : G) : Set (Subgroup G) :=
  supportingMaximals (maximalSubgroups G) sigmaCore x

theorem sigmaSupportingMaximals_eq [Finite G] (x : G) :
    sigmaSupportingMaximals x = supportingMaximals (maximalSubgroups G) sigmaCore x := (rfl)

theorem mem_sigmaSupportingMaximals [Finite G] {x : G} :
    M ∈ sigmaSupportingMaximals x ↔ IsCoatom M ∧ x ∈ sigmaCore M := by
  rw [sigmaSupportingMaximals, mem_supportingMaximals, mem_maximalSubgroups]

@[expose]
noncomputable def sigmaMultiplicity [Finite G] (x : G) : ℕ :=
  supportMultiplicity (maximalSubgroups G) sigmaCore x

theorem sigmaMultiplicity_eq_ncard [Finite G] (x : G) :
    sigmaMultiplicity x = (sigmaSupportingMaximals x).ncard := by
  rw [sigmaMultiplicity, sigmaSupportingMaximals, supportMultiplicity_eq_ncard]

@[expose]
noncomputable def sigmaSignalizer [Finite G] (x : G) : Subgroup G :=
  canonicalSignalizer (maximalSubgroups G) sigmaCore x

theorem sigmaSignalizer_eq [Finite G] (x : G) :
    sigmaSignalizer x = canonicalSignalizer (maximalSubgroups G) sigmaCore x := (rfl)

theorem sigmaSignalizer_le_centralizer [Finite G] (x : G) :
    sigmaSignalizer x ≤ centralizer ({x} : Set G) := canonicalSignalizer_le_centralizer

structure IsExceptionalPlaneConfig (p : ℕ) (M A₀ A P : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  prime : p.Prime
  notMem_sigmaPrimes : p ∉ sigmaPrimes M
  le_of_A₀ : A₀ ≤ A
  le_of_A : A ≤ P
  le_of_P : P ≤ M
  natCard_A₀ : Nat.card ↥A₀ = p
  isElementaryAbelianPlane : IsElementaryAbelianPlane p A
  isSylowSubgroupOf : IsSylowSubgroupOf p P M
  normalizer_le : normalizer (A₀ : Set G) ≤ M

structure IsKappaFreeNonfittingConfig [Finite G] (q : ℕ) (M E Q : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  kappaPrimes_eq_empty : kappaPrimes M = ∅
  le_of_E : E ≤ M
  isInternalSemidirectProduct : IsInternalSemidirectProduct M (sigmaCore M) E
  prime : q.Prime
  le_of_Q : Q ≤ E
  natCard_Q : Nat.card ↥Q = q
  not_le_fitting : ¬ Q ≤ fittingOfNormal E

structure IsKappaResidualConfig [Finite G] (M K U : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  kappaPrimes_nonempty : (kappaPrimes M).Nonempty
  isHallKappa : IsHallPiSubgroupOf (kappaPrimes M) K M
  isHallCompl : IsHallPiSubgroupOf {r : ℕ | r.Prime ∧ r ∉ sigmaPrimes M ∧ r ∉ kappaPrimes M} U M
  isInternalSemidirectProduct : IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K)
  isInternalSemidirectProduct_complement : IsInternalSemidirectProduct (U ⊔ K) U K

structure IsKappaResidualPartner [Finite G] (r : ℕ) (M K U A Mstar R H : Subgroup G) : Prop where
  config : IsKappaResidualConfig M K U
  isMulCommutative_U : IsMulCommutative ↥U
  centralizer_eq_bot : ∀ k ∈ K, k ≠ 1 → U ⊓ centralizer ({k} : Set G) = ⊥
  U_ne_bot : U ≠ ⊥
  A_eq : A = sigmaCore M ⊓ centralizer (K : Set G)
  isCoatom_Mstar : IsCoatom Mstar
  exists_prime_order_normalizer_le : ∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
    normalizer (X : Set G) ≤ Mstar
  prime_r : r.Prime
  dvd_natCard_U : r ∣ Nat.card ↥U
  isSylowSubgroupOf_R : IsSylowSubgroupOf r R U
  isCoatom_H : IsCoatom H
  normalizer_R_le : normalizer (R : Set G) ≤ H

namespace Statements

@[expose]
def FTS_canonical_signalizer_full_support_coprimality : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G,
      (∀ a ∈ sigmaCore M, a ≠ 1 → ∀ b ∈ M, b ≠ 1 →
          sigmaCore M ⊓ centralizer ({b} : Set G) ≠ ⊥ →
          Nat.Coprime (Nat.card ↥(sigmaSignalizer a))
            (Nat.card ↥(M ⊓ centralizer ({b} : Set G)))) ∧
        ((kappaPrimes M).Nonempty → ∀ a ∈ sigmaCore M, a ≠ 1 →
          Nat.Coprime (Nat.card ↥(sigmaSignalizer a)) (Nat.card ↥M))

@[expose]
def FTS_canonical_signalizer_structure : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ x ∈ sigmaSupport G,
      ((sigmaSignalizer x).subgroupOf (centralizer ({x} : Set G))).Normal ∧
        IsHallSubgroupOf (sigmaSignalizer x) (centralizer ({x} : Set G)) ∧
        Nat.card ↥(sigmaSignalizer x) = sigmaMultiplicity x ∧
        (∀ M ∈ sigmaSupportingMaximals x, ∀ N ∈ sigmaSupportingMaximals x,
          ∃! r : ↥(sigmaSignalizer x), conjBy M (r : G) = N) ∧
        (∀ M ∈ sigmaSupportingMaximals x,
          IsInternalSemidirectProduct (centralizer ({x} : Set G)) (sigmaSignalizer x)
              (M ⊓ centralizer ({x} : Set G)) ∧
            sigmaSignalizer x ⊓ M = ⊥) ∧
        (sigmaSignalizer x ≠ ⊥ → ∀ M ∈ sigmaSupportingMaximals x,
          ∃ N ∈ maximalSubgroups G, centralizer ({x} : Set G) ≤ N ∧
            sigmaSignalizer x ≤ sigmaCore N ∧ x ∈ M ⊓ N ∧ sigmaPrimes M ∩ sigmaPrimes N = ∅)

@[expose]
def FTS_common_core_excludes_rank_two_complement : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ L ∈ maximalSubgroups G, M ≠ L →
      ∀ E : Subgroup G, E ≤ M → IsInternalSemidirectProduct M (sigmaCore M) E →
        E ≤ L → sigmaCore M ⊓ L ≠ ⊥ →
        tauTwoPrimes M = ∅ ∧
          ∀ E₂ : Subgroup G, IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E → E₂ = ⊥

@[expose]
def FTS_common_core_tau_one_witness : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ L ∈ maximalSubgroups G, M ≠ L →
      ∀ E : Subgroup G, E ≤ M → E ≠ ⊥ → IsInternalSemidirectProduct M (sigmaCore M) E →
        E ≤ L → sigmaCore M ⊓ L ≠ ⊥ →
        ∃ E₁ E₂ E₃ : Subgroup G, IsHallPiSubgroupOf (tau1Primes M) E₁ E ∧
          IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E ∧ IsHallPiSubgroupOf (tau3Primes M) E₃ E ∧
          ∃ p ∈ tau1Primes M, ∃ P : Subgroup G, P ≤ E₁ ∧ Nat.card ↥P = p ∧
            E₂ = ⊥ ∧ E₁ ≠ ⊥ ∧ IsInternalSemidirectProduct E E₃ E₁ ∧ P ≤ M ⊓ L ∧
            ∀ Q : Subgroup G, E ≤ normalizer (Q : Set G) → P ≤ normalizer (Q : Set G)

@[expose]
def FTS_common_prime_fixed_core_fitting_envelope : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ L ∈ maximalSubgroups G, (kappaPrimes L).Nonempty →
      ∀ J : Subgroup G, IsHallPiSubgroupOf (kappaPrimes L) J L →
        ∀ q : ℕ, q.Prime → Nat.card ↥(sigmaCore L ⊓ centralizer (J : Set G)) = q →
          ((pCoreOf q L).subgroupOf L).Normal ∧ IsSylowSubgroupOf q (pCoreOf q L) L ∧
            sigmaCore L ⊓
                centralizer ((sigmaCore L ⊓ centralizer (J : Set G) : Subgroup G) : Set G) ≤
              fittingOfNormal L ∧
            (¬ Group.IsNilpotent ↥(sigmaCore L) → q ∈ betaPrimes ↥L)

@[expose]
def FTS_complement_fixed_core_contained_derived : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ E : Subgroup G, E ≤ M →
      IsInternalSemidirectProduct M (sigmaCore M) E →
      sigmaCore M ⊓ centralizer (E : Set G) ≤ ⁅sigmaCore M, sigmaCore M⁆

@[expose]
def FTS_complement_plane_primes_in_opposite_core : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ T ∈ maximalSubgroups G, M ≠ T →
      IsInternalSemidirectProduct T (sigmaCore T) (M ⊓ T) →
      (∃ x ∈ sigmaCore M ⊓ (M ⊓ T), x ≠ 1) →
      tauTwoPrimes T ⊆ sigmaPrimes M

@[expose]
def FTS_core_centralizing_external_element_dichotomy : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ x ∈ sigmaCore M, x ≠ 1 →
      ∀ y ∈ M ⊓ centralizer ({x} : Set G), y ≠ 1 →
        (∀ r ∈ (orderOf y).primeFactors, r ∉ sigmaPrimes M) →
        ((∀ r ∈ (orderOf y).primeFactors, r ∈ kappaPrimes M) ∧
            centralizer ({x} : Set G) ≤ M) ∨
          ((∀ r ∈ (orderOf y).primeFactors, r ∈ tauTwoPrimes M) ∧
            IsUniqueMaximalOvergroup (centralizer ({y} : Set G)) M)

@[expose]
def FTS_core_nonregular_element_with_tau_two_prime : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ E : Subgroup G, E ≤ M →
      IsInternalSemidirectProduct M (sigmaCore M) E →
      ∀ y ∈ E, y ≠ 1 → sigmaCore M ⊓ centralizer ({y} : Set G) ≠ ⊥ →
        (∃ r ∈ (orderOf y).primeFactors, r ∈ tauTwoPrimes M) →
        ∀ r ∈ (orderOf y).primeFactors, r ∈ tauTwoPrimes M

@[expose]
def FTS_cyclic_sylow_complement_fixed_centralizer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ E : Subgroup G, E ≤ M →
      IsInternalSemidirectProduct M (sigmaCore M) E →
      ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, IsSylowSubgroupOf p P E → P ≠ ⊥ → IsCyclic ↥P →
        ∀ X : Subgroup G, X ≤ P → X ≠ ⊥ →
          sigmaCore M ⊓ centralizer (X : Set G) = sigmaCore M ⊓ centralizer (P : Set G)

@[expose]
def FTS_derived_complement_centralizes_beta_prime_hall : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ E : Subgroup G, E ≤ M →
      IsInternalSemidirectProduct M (sigmaCore M) E →
      ∃ H : Subgroup G, IsHallPiSubgroupOf {r : ℕ | r.Prime ∧ r ∉ betaPrimes ↥M} H (sigmaCore M) ∧
        ⁅⁅E, E⁆, H⁆ = ⊥

@[expose]
def FTS_exceptional_core_conjugate_intersection : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      ∀ g : G, g ∉ M → A ≤ conjBy M g →
        sigmaCore M ⊓ conjBy M g = ⊥ ∧
          sigmaCore M ⊓ centralizer ((conjBy A₀ g : Subgroup G) : Set G) = ⊥

@[expose]
def FTS_exceptional_core_nilpotent : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      Group.IsNilpotent ↥(sigmaCore M)

@[expose]
def FTS_exceptional_core_overgroup_uniqueness : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      ∀ T ∈ maximalSubgroups G, A ≤ T → sigmaCore M ⊓ sigmaCore T ≠ ⊥ → T = M

@[expose]
def FTS_exceptional_invariant_sylow_separation : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      ∀ q ∈ sigmaPrimes M, ∀ g : G, g ∉ M → A ≤ conjBy M g →
        ∀ Q₁ Q₂ : Subgroup G, IsSylowSubgroupOf q Q₁ (sigmaCore M) →
          IsSylowSubgroupOf q Q₂ (conjBy (sigmaCore M) g) →
          A ≤ normalizer (Q₁ : Set G) → A ≤ normalizer (Q₂ : Set G) →
          Q₁ ⊓ Q₂ = ⊥ ∧ ∀ X : Subgroup G, X ≤ A → Nat.card ↥X = p →
            Q₁ ⊓ centralizer (X : Set G) = ⊥ ∨ Q₂ ⊓ centralizer (X : Set G) = ⊥

@[expose]
def FTS_exceptional_noncentral_sylow_fixed_free : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      ∀ q : ℕ, q.Prime → q ≠ p → q ∉ sigmaPrimes M →
        ∀ Q : Subgroup G, IsSylowSubgroupOf q Q M → A ≤ normalizer (Q : Set G) →
          ⁅Q, A⁆ ≠ ⊥ → Q ⊓ centralizer (A : Set G) = ⊥

@[expose]
def FTS_exceptional_normal_plane_product : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      ((sigmaCore M ⊔ A).subgroupOf M).Normal

@[expose]
def FTS_exceptional_plane_centralizes_outside_sylow : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      ∀ q : ℕ, q.Prime → q ≠ p → q ∉ sigmaPrimes M →
        ∀ Q : Subgroup G, IsSylowSubgroupOf q Q M → A ≤ normalizer (Q : Set G) → ⁅Q, A⁆ = ⊥

@[expose]
def FTS_exceptional_plane_fixed_free_lines : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      (A : Set G) = {x : G | x ∈ P ∧ x ^ p = 1} ∧
        sigmaCore M ⊓ centralizer (A : Set G) = ⊥ ∧
        ∃ A₁ A₂ : Subgroup G, A₁ ≤ A ∧ A₂ ≤ A ∧ A₁ ≠ A₂ ∧
          Nat.card ↥A₁ = p ∧ Nat.card ↥A₂ = p ∧
          sigmaCore M ⊓ centralizer (A₁ : Set G) = ⊥ ∧
          sigmaCore M ⊓ centralizer (A₂ : Set G) = ⊥

@[expose]
def FTS_exceptional_sylow_abelian : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (p : ℕ) (M A₀ A P : Subgroup G), IsExceptionalPlaneConfig p M A₀ A P →
      IsMulCommutative ↥P ∧ ∀ Q : Subgroup G, IsSylowSubgroupOf p Q M → IsMulCommutative ↥Q

@[expose]
def FTS_kappa_fixed_core_outside_conjugate_disjoint : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, (kappaPrimes M).Nonempty →
      ∀ K : Subgroup G, IsHallPiSubgroupOf (kappaPrimes M) K M →
        ∀ g : G, g ∉ M →
          (sigmaCore M ⊓ centralizer (K : Set G)) ⊓ conjBy M g = ⊥

@[expose]
def FTS_kappa_fixed_intersection_sigma_containment : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, (kappaPrimes M).Nonempty →
      ∀ K : Subgroup G, IsHallPiSubgroupOf (kappaPrimes M) K M →
        ∀ Y : Subgroup G, IsPiSubgroup (sigmaPrimes M) Y →
          Y ⊓ (sigmaCore M ⊓ centralizer (K : Set G)) ≠ ⊥ → Y ≤ sigmaCore M

@[expose]
def FTS_kappa_free_auxiliary_cross_point_coprimality : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ T ∈ maximalSubgroups G,
      tauTwoPrimes T ⊆ sigmaPrimes M →
      (∀ r : ℕ, r ∣ Nat.card ↥M → r ∈ sigmaPrimes T → r ∈ betaPrimes ↥T) →
      kappaPrimes M = ∅ → sigmaPrimes M ∩ sigmaPrimes T = ∅ →
      (∃ x ∈ sigmaCore M, x ≠ 1 ∧ centralizer ({x} : Set G) ≤ T) →
      ∀ b ∈ M, b ≠ 1 → sigmaCore M ⊓ centralizer ({b} : Set G) ≠ ⊥ →
        Nat.Coprime (Nat.card ↥(sigmaCore T)) (Nat.card ↥(M ⊓ centralizer ({b} : Set G)))

@[expose]
def FTS_kappa_free_auxiliary_overlap_excludes_tau_two : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ T ∈ maximalSubgroups G,
      tauTwoPrimes T ⊆ sigmaPrimes M →
      (∀ r : ℕ, r ∣ Nat.card ↥M → r ∈ sigmaPrimes T → r ∈ betaPrimes ↥T) →
      kappaPrimes M = ∅ → sigmaPrimes M ∩ sigmaPrimes T = ∅ →
      (∃ x ∈ sigmaCore M, x ≠ 1 ∧ centralizer ({x} : Set G) ≤ T) →
      (∃ r : ℕ, r ∣ Nat.card ↥M ∧ r ∈ sigmaPrimes T) → tauTwoPrimes M = ∅

@[expose]
def FTS_kappa_free_nonfitting_displacement_support : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (q : ℕ) (M E Q : Subgroup G), IsKappaFreeNonfittingConfig q M E Q →
      q ∈ tau1Primes M ∧ sigmaCore M ⊓ centralizer (Q : Set G) = ⊥ ∧
        ⁅E, Q⁆ ≠ ⊥ ∧ IsCyclic ↥(⁅E, Q⁆ : Subgroup G) ∧ ((⁅E, Q⁆ : Subgroup G).subgroupOf M).Normal ∧
        ⁅(⁅E, Q⁆ : Subgroup G), Q⁆ = ⁅E, Q⁆ ∧
        (⁅E, Q⁆ : Subgroup G) ⊓ centralizer (Q : Set G) = ⊥ ∧
        ⁅(⁅E, Q⁆ : Subgroup G), sigmaCore M⁆ = ⊥ ∧
        ∀ r ∈ (Nat.card ↥(⁅E, Q⁆ : Subgroup G)).primeFactors, r ∈ tauTwoPrimes M

@[expose]
def FTS_kappa_free_nonfitting_plane_action : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (q : ℕ) (M E Q : Subgroup G), IsKappaFreeNonfittingConfig q M E Q →
      ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ tauTwoPrimes M = {p} ∧
        ∃ A : Subgroup G, A ≤ E ∧ IsElementaryAbelianPlane p A ∧
          (∃ S : Sylow p G, ¬ IsMulCommutative ↥(S : Subgroup G)) ∧
          (⁅E, Q⁆ : Subgroup G) = A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G) ∧
          Nat.card ↥(⁅E, Q⁆ : Subgroup G) = p ∧ ⁅A, Q⁆ = ⁅E, Q⁆ ∧
          Nat.card ↥(A ⊓ centralizer (Q : Set G)) = p ∧ ⁅A, Q⁆ ≠ ⊥

@[expose]
def FTS_kappa_free_nonfitting_plane_transfer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (q : ℕ) (M E Q : Subgroup G), IsKappaFreeNonfittingConfig q M E Q →
      ∀ (p : ℕ) (A : Subgroup G), p.Prime → p ≠ q → tauTwoPrimes M = {p} → A ≤ E →
        IsElementaryAbelianPlane p A →
        (⁅E, Q⁆ : Subgroup G) = A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G) →
        Nat.card ↥(⁅E, Q⁆ : Subgroup G) = p → ⁅A, Q⁆ = ⁅E, Q⁆ →
        Nat.card ↥(A ⊓ centralizer (Q : Set G)) = p →
        (∀ T ∈ maximalSubgroups G, normalizer (A : Set G) ≤ T →
            p ∈ sigmaPrimes T ∧ p ∉ betaPrimes ↥T ∧
              (q ∈ tau1Primes T ∨ q ∈ tauTwoPrimes T) ∧ Q ≤ T ∧
              sigmaCore T ⊓ centralizer (Q : Set G) ≠ ⊥) ∧
          ∃ T ∈ maximalSubgroups G, normalizer (A : Set G) ≤ T

@[expose]
def FTS_kappa_free_nonfitting_prime_alternative : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (q : ℕ) (M E Q : Subgroup G), IsKappaFreeNonfittingConfig q M E Q →
      ∃ T ∈ maximalSubgroups G,
        (q ∈ tauTwoPrimes T ∧ Q ≤ T ∧
            IsUniqueMaximalOvergroup (centralizer (Q : Set G)) T) ∨
          (q ∈ kappaPrimes T ∧ Q ≤ T ∧ ∀ L : Subgroup G,
            IsHallPiSubgroupOf (kappaPrimes T) L T →
            IsInternalSemidirectProduct T (sigmaCore T) L)

@[expose]
def FTS_kappa_free_tau_two_free_frobenius : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, kappaPrimes M = ∅ → tauTwoPrimes M = ∅ →
      sigmaCore M ≠ ⊥ ∧
        (∃ E : Subgroup G, E ≤ M ∧ E ≠ ⊥ ∧
          IsInternalSemidirectProduct M (sigmaCore M) E ∧
          ∀ e ∈ E, e ≠ 1 → sigmaCore M ⊓ centralizer ({e} : Set G) = ⊥) ∧
        (∀ E : Subgroup G, E ≤ M → IsInternalSemidirectProduct M (sigmaCore M) E →
          ∀ e ∈ E, e ≠ 1 → sigmaCore M ⊓ centralizer ({e} : Set G) = ⊥)

@[expose]
def FTS_kappa_hall_local_ti : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, (kappaPrimes M).Nonempty →
      ∀ K : Subgroup G, IsHallPiSubgroupOf (kappaPrimes M) K M →
        (∀ g ∈ M, g ∉ normalizer (K : Set G) → K ⊓ conjBy K g = ⊥) ∧
          ∀ g ∈ M, g ∉ M ⊓ normalizer (K : Set G) →
            Disjoint ((K : Set G) \ {1}) ((fun x : G => g⁻¹ * x * g) '' ((K : Set G) \ {1}))

@[expose]
def FTS_kappa_positive_multiple_core_trivial_residual : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ x ∈ sigmaSupport G, 1 < sigmaMultiplicity x →
      ∀ M ∈ sigmaSupportingMaximals x, ∀ T ∈ maximalSubgroups G,
        IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) T →
        (kappaPrimes M).Nonempty →
        (∃ p ∈ (orderOf x).primeFactors, p ∈ sigmaPrimes M ∧ p ∈ tauTwoPrimes T ∧
            p ∉ betaPrimes G ∧ p ∉ betaPrimes ↥M) ∧
          sigmaPrimes M ≠ betaPrimes ↥M ∧
          ∀ K : Subgroup G, IsHallPiSubgroupOf (kappaPrimes M) K M →
            IsInternalSemidirectProduct M (sigmaCore M) K

@[expose]
def FTS_kappa_positive_support_forces_cyclic_frobenius : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M ∈ maximalSubgroups G, ∀ N ∈ maximalSubgroups G, ∀ x ∈ sigmaCore M, x ≠ 1 →
      ¬ centralizer ({x} : Set G) ≤ M → centralizer ({x} : Set G) ≤ N →
      (kappaPrimes N).Nonempty →
      kappaPrimes M = ∅ ∧ tauTwoPrimes M = ∅ ∧ Group.IsNilpotent ↥(sigmaCore M) ∧
        (∃ E : Subgroup G, E ≤ M ∧ sigmaCore M ≠ ⊥ ∧ E ≠ ⊥ ∧
          IsInternalSemidirectProduct M (sigmaCore M) E ∧ IsCyclic ↥E ∧
          ∀ e ∈ E, e ≠ 1 → sigmaCore M ⊓ centralizer ({e} : Set G) = ⊥) ∧
        (∀ E : Subgroup G, E ≤ M → IsInternalSemidirectProduct M (sigmaCore M) E →
          E ≠ ⊥ ∧ IsCyclic ↥E ∧
            ∀ e ∈ E, e ≠ 1 → sigmaCore M ⊓ centralizer ({e} : Set G) = ⊥)

@[expose]
def FTS_kappa_positive_support_sigma_primes_disjoint : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ x ∈ sigmaSupport G, 1 < sigmaMultiplicity x →
      ∀ M ∈ sigmaSupportingMaximals x, ∀ T ∈ maximalSubgroups G,
        IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) T →
        (kappaPrimes M).Nonempty →
        ∀ r : ℕ, r ∣ Nat.card ↥M → r ∉ sigmaPrimes T

@[expose]
def FTS_kappa_residual_contained_opposite_sigma_core : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (r : ℕ) (M K U A Mstar R H : Subgroup G),
      IsKappaResidualPartner r M K U A Mstar R H → U ≤ sigmaCore H

@[expose]
def FTS_kappa_residual_containing_complement_fitting : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (r : ℕ) (M K U A Mstar R H : Subgroup G),
      IsKappaResidualPartner r M K U A Mstar R H →
      (∃ D : Subgroup G, D ≤ H ∧ IsInternalSemidirectProduct H (sigmaCore H) D ∧ K ≤ D) ∧
        ∀ D : Subgroup G, D ≤ H → IsInternalSemidirectProduct H (sigmaCore H) D → K ≤ D →
          K ≤ fittingOfNormal D ∧ D ≤ Mstar

@[expose]
def FTS_kappa_residual_in_prescribed_complement : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ N ∈ maximalSubgroups G, (kappaPrimes N).Nonempty →
      ∀ E : Subgroup G, E ≤ N → IsInternalSemidirectProduct N (sigmaCore N) E →
        ∃ K U : Subgroup G, K ≤ E ∧ U ≤ E ∧
          IsHallPiSubgroupOf (kappaPrimes N) K N ∧ IsMulCommutative ↥U ∧
          IsHallPiSubgroupOf {r : ℕ | r.Prime ∧ r ∉ sigmaPrimes N ∧ r ∉ kappaPrimes N} U N ∧
          IsInternalSemidirectProduct E U K ∧
          IsInternalSemidirectProduct N (sigmaCore N) (U ⊔ K) ∧
          ∀ k ∈ K, k ≠ 1 → U ⊓ centralizer ({k} : Set G) = ⊥

@[expose]
def FTS_kappa_residual_local_normalizer : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M K U : Subgroup G, IsKappaResidualConfig M K U → U ≠ ⊥ →
      sigmaCore M ⊓ centralizer (U : Set G) = ⊥ ∧
        normalizer (U : Set G) ⊓ M = U ⊔ K

@[expose]
def FTS_kappa_residual_normalizer_escape : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ M K U : Subgroup G, IsKappaResidualConfig M K U → IsMulCommutative ↥U →
      (∀ k ∈ K, k ≠ 1 → U ⊓ centralizer ({k} : Set G) = ⊥) →
      ¬ normalizer (U : Set G) ≤ M

@[expose]
def FTS_kappa_residual_partner_intersection_complement : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (r : ℕ) (M K U A Mstar R H : Subgroup G),
      IsKappaResidualPartner r M K U A Mstar R H →
      IsInternalSemidirectProduct H (sigmaCore H) (H ⊓ Mstar) ∧
        K ≤ fittingOfNormal (H ⊓ Mstar)

@[expose]
def FTS_kappa_residual_prime_overgroup_intersection : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], IsFTAmbient G →
    ∀ (r : ℕ) (M K U A Mstar R H : Subgroup G),
      IsKappaResidualPartner r M K U A Mstar R H →
      Group.IsNilpotent ↥(sigmaCore H) ∧ sigmaCore H ⊓ M = U ∧ H ⊓ M = U ⊔ K ∧
        ¬ normalizer (U : Set G) ⊓ H ≤ M

end Statements

end

end CFSG.FeitThompson
