module

public import Mathlib
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.NormalSylowHallCore
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import CFSG.FeitThompson.Definitions.AlphaCore
public import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.SupportOfAMaximalSubgroupCoreFamily
public import CFSG.FeitThompson.Definitions.SupportingMaximalSubgroupsOfAnElement
public import CFSG.FeitThompson.Definitions.SupportMultiplicity
public import CFSG.FeitThompson.Definitions.CanonicalCentralizerSignalizerFrom
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
public import CFSG.FeitThompson.Definitions.LocalTypeI
public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
public import CFSG.FeitThompson.Definitions.TheLocalFrobeniusTypePredicate
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Definitions.DadeData
public import CFSG.FeitThompson.Definitions.DadeCosetPacket
public import CFSG.FeitThompson.Definitions.DadeSupportExtension
public import CFSG.FeitThompson.Definitions.MaximumElementaryAbelianPrimeRank
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
public import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
public import CFSG.FeitThompson.Representations.PrimeTILocalTransporterTISet
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Foundations.PrimeConstituentsOfElement
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.TensorAndDualCharacters

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

universe u

variable {G : Type*} [Group G]

namespace Prep09

structure IsMinimalSimpleOddOrder (G : Type*) [Group G] [Finite G] : Prop where
  odd_natCard : Odd (Nat.card G)
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  isSolvable_of_ne_top : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H

@[expose]
def hallCoreIn (M : Subgroup G) : Subgroup G := (hallCore M).map M.subtype

@[expose]
def alphaCoreIn [Finite G] (M : Subgroup G) : Subgroup G := (alphaCore M).map M.subtype

@[expose]
def pComplCoreIn [Finite G] (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (pComplCore p X).map X.subtype

@[expose]
def centIn (X : Subgroup G) (S : Set G) : Subgroup G := X ⊓ centralizer S

@[expose]
def conjSub (g : G) (Y : Subgroup G) : Subgroup G := Y.map (MulAut.conj g⁻¹ : G →* G)

@[expose]
def conjSet (g : G) (S : Set G) : Set G := (fun x => g⁻¹ * x * g) '' S

@[expose]
def conjUnion (M : Subgroup G) (S : Set G) : Set G := ⋃ m ∈ (M : Set G), conjSet m S

@[expose]
def IsNilpotentNormalHall (T N : Subgroup G) : Prop :=
  N ≤ T ∧ (N.subgroupOf T).Normal ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (N.relIndex T)

@[expose]
def IsComplementTo (M H U : Subgroup G) : Prop :=
  U ≤ M ∧ (H : Set G) * (U : Set G) = (M : Set G) ∧ H ⊓ U = ⊥

@[expose]
def coreFixedSet (H X : Subgroup G) : Set G :=
  {a : G | a ∈ X ∧ a ≠ 1 ∧ centIn H {a} ≠ ⊥}

@[expose]
def exteriorFixedSet (H X : Subgroup G) : Set G :=
  {y : G | y ∈ X ∧ y ∉ H ∧ centIn H {y} ≠ ⊥}

@[expose]
def IsMaximalElementaryAbelianPlane (p : ℕ) {X : Type*} [Group X] (A : Subgroup X) : Prop :=
  Maximal (IsElementaryAbelianSubgroup p) A ∧ Nat.card A = p ^ 2

@[expose]
def sigmaPrimeSets (G : Type*) [Group G] [Finite G] : Set (Set ℕ) :=
  {π : Set ℕ | π.Nonempty ∧ ∃ M : Subgroup G, IsCoatom M ∧ π = sigmaPrimes M}

@[expose]
noncomputable def sigmaConstituents [Finite G] (x : G) : Set G :=
  {y : G | ∃ π ∈ sigmaPrimeSets G, y = piConstituent π x ∧ y ≠ 1}

open scoped Classical in
@[expose]
noncomputable def sigmaSignalizerOn [Finite G] (M : Subgroup G) (a : G) : Subgroup G :=
  if a ∈ sigmaCore M ∧ a ≠ 1 then sigmaSignalizer a else ⊥

open scoped Classical in
@[expose]
noncomputable def hallSignalizerOn [Finite G] (M : Subgroup G) (a : G) : Subgroup G :=
  if a ∈ hallCoreIn M then sigmaSignalizer a else ⊥

@[expose]
def IsTypeIIWitness [Finite G] (M E W₁ W₂ : Subgroup G) : Prop :=
  IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
    ¬ normalizer (E : Set G) ≤ M ∧
    IsFrobeniusType ↥(⁅M, M⁆ : Subgroup G) (E.subgroupOf (⁅M, M⁆ : Subgroup G)) ∧
    (hallCore ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype = hallCoreIn M

@[expose]
noncomputable def classFunInner (X : Type*) [Group X] (f h : X → ℂ) : ℂ :=
  (Nat.card X : ℂ)⁻¹ * ∑ᶠ x : X, f x * (starRingEnd ℂ) (h x)

@[expose]
noncomputable def inducedClassFun (M : Subgroup G) (f : G → ℂ) (g : G) : ℂ :=
  (Nat.card M : ℂ)⁻¹ * ∑ᶠ x ∈ {x : G | x⁻¹ * g * x ∈ M}, f (x⁻¹ * g * x)

theorem hallCoreIn_def (M : Subgroup G) : hallCoreIn M = (hallCore M).map M.subtype := (rfl)

theorem hallCoreIn_le (M : Subgroup G) : hallCoreIn M ≤ M := Subgroup.map_subtype_le _

theorem alphaCoreIn_def [Finite G] (M : Subgroup G) :
    alphaCoreIn M = (alphaCore M).map M.subtype := (rfl)

theorem alphaCoreIn_le [Finite G] (M : Subgroup G) : alphaCoreIn M ≤ M := Subgroup.map_subtype_le _

theorem pComplCoreIn_def [Finite G] (p : ℕ) (X : Subgroup G) :
    pComplCoreIn p X = (pComplCore p X).map X.subtype := (rfl)

theorem pComplCoreIn_le [Finite G] (p : ℕ) (X : Subgroup G) : pComplCoreIn p X ≤ X :=
  Subgroup.map_subtype_le _

theorem centIn_def (X : Subgroup G) (S : Set G) : centIn X S = X ⊓ centralizer S := (rfl)

theorem mem_centIn {X : Subgroup G} {S : Set G} {x : G} :
    x ∈ centIn X S ↔ x ∈ X ∧ ∀ s ∈ S, s * x = x * s := by
  simp [centIn, Subgroup.mem_centralizer_iff]

theorem centIn_le (X : Subgroup G) (S : Set G) : centIn X S ≤ X := inf_le_left

theorem centIn_le_centralizer (X : Subgroup G) (S : Set G) : centIn X S ≤ centralizer S :=
  inf_le_right

theorem centIn_mono_left {X Y : Subgroup G} (h : X ≤ Y) (S : Set G) : centIn X S ≤ centIn Y S :=
  inf_le_inf_right _ h

theorem conjSub_def (g : G) (Y : Subgroup G) :
    conjSub g Y = Y.map (MulAut.conj g⁻¹ : G →* G) := (rfl)

@[simp]
theorem mem_conjSub {g y : G} {Y : Subgroup G} : y ∈ conjSub g Y ↔ g * y * g⁻¹ ∈ Y := by
  rw [conjSub_def, Subgroup.mem_map]
  refine ⟨?_, fun h => ⟨g * y * g⁻¹, h, by simp [MulAut.conj, mul_assoc]⟩⟩
  rintro ⟨z, hz, rfl⟩
  simpa [MulAut.conj, mul_assoc] using hz

theorem conjSet_def (g : G) (S : Set G) : conjSet g S = (fun x => g⁻¹ * x * g) '' S := (rfl)

@[simp]
theorem mem_conjSet {g y : G} {S : Set G} : y ∈ conjSet g S ↔ g * y * g⁻¹ ∈ S := by
  rw [conjSet_def]
  refine ⟨?_, fun h => ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩⟩
  rintro ⟨z, hz, rfl⟩
  simpa [mul_assoc] using hz

@[simp]
theorem conjSub_one (Y : Subgroup G) : conjSub 1 Y = Y := by ext; simp

@[simp]
theorem conjSet_one (S : Set G) : conjSet 1 S = S := by ext; simp

@[simp]
theorem coe_conjSub (g : G) (Y : Subgroup G) : (conjSub g Y : Set G) = conjSet g (Y : Set G) := by
  ext; simp

theorem mem_conjUnion {y : G} {M : Subgroup G} {S : Set G} :
    y ∈ conjUnion M S ↔ ∃ m ∈ M, y ∈ conjSet m S := by
  simp [conjUnion]

theorem subset_conjUnion (M : Subgroup G) (S : Set G) : S ⊆ conjUnion M S := fun x hx =>
  mem_conjUnion.2 ⟨1, one_mem M, by simpa using hx⟩

theorem mem_coreFixedSet {H X : Subgroup G} {a : G} :
    a ∈ coreFixedSet H X ↔ a ∈ X ∧ a ≠ 1 ∧ centIn H {a} ≠ ⊥ := Iff.rfl

theorem mem_exteriorFixedSet {H X : Subgroup G} {y : G} :
    y ∈ exteriorFixedSet H X ↔ y ∈ X ∧ y ∉ H ∧ centIn H {y} ≠ ⊥ := Iff.rfl

theorem coreFixedSet_subset (H X : Subgroup G) : coreFixedSet H X ⊆ (X : Set G) :=
  fun _ h => h.1

theorem exteriorFixedSet_subset_coreFixedSet (H X : Subgroup G) :
    exteriorFixedSet H X ⊆ coreFixedSet H X := by
  rintro y ⟨hyX, hyH, hc⟩
  exact ⟨hyX, fun h => hyH (h ▸ one_mem H), hc⟩

theorem exteriorFixedSet_eq_sdiff (H X : Subgroup G) :
    exteriorFixedSet H X = coreFixedSet H X \ ((H : Set G) \ {1}) := by
  ext y
  simp only [mem_exteriorFixedSet, mem_coreFixedSet, Set.mem_diff, Set.mem_singleton_iff,
    not_and, not_not]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun h => h2 (h ▸ one_mem H), h3⟩, fun h => absurd h h2⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, fun h => h2 (h4 h), h3⟩

theorem one_notMem_sigmaSupport [Finite G] : (1 : G) ∉ sigmaSupport G := by
  rw [sigmaSupport_eq]
  exact one_notMem_coreFamilySupport

open scoped Classical in
theorem sigmaSignalizerOn_of_mem [Finite G] {M : Subgroup G} {a : G} (ha : a ∈ sigmaCore M)
    (ha1 : a ≠ 1) : sigmaSignalizerOn M a = sigmaSignalizer a := by
  rw [sigmaSignalizerOn, if_pos ⟨ha, ha1⟩]

open scoped Classical in
theorem sigmaSignalizerOn_of_notMem [Finite G] {M : Subgroup G} {a : G}
    (ha : ¬ (a ∈ sigmaCore M ∧ a ≠ 1)) : sigmaSignalizerOn M a = ⊥ := by
  rw [sigmaSignalizerOn, if_neg ha]

open scoped Classical in
theorem hallSignalizerOn_of_mem [Finite G] {M : Subgroup G} {a : G} (ha : a ∈ hallCoreIn M) :
    hallSignalizerOn M a = sigmaSignalizer a := by
  rw [hallSignalizerOn, if_pos ha]

open scoped Classical in
theorem hallSignalizerOn_of_notMem [Finite G] {M : Subgroup G} {a : G} (ha : a ∉ hallCoreIn M) :
    hallSignalizerOn M a = ⊥ := by
  rw [hallSignalizerOn, if_neg ha]

theorem isTypeII_of_isTypeIIWitness [Finite G] {M E W₁ W₂ : Subgroup G}
    (h : IsTypeIIWitness M E W₁ W₂) : IsTypeII M :=
  ⟨E, W₁, W₂, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem classFunInner_def (X : Type*) [Group X] (f h : X → ℂ) :
    classFunInner X f h = (Nat.card X : ℂ)⁻¹ * ∑ᶠ x : X, f x * (starRingEnd ℂ) (h x) := (rfl)

theorem inducedClassFun_def (M : Subgroup G) (f : G → ℂ) (g : G) :
    inducedClassFun M f g =
      (Nat.card M : ℂ)⁻¹ * ∑ᶠ x ∈ {x : G | x⁻¹ * g * x ∈ M}, f (x⁻¹ * g * x) := (rfl)

end Prep09

namespace Statements

open Prep09

@[expose]
def FTS_sigma_normalizer_complement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → M ≠ N →
      ∀ q ∈ sigmaPrimes M, ∀ Q : Subgroup G, Q ≤ M → Nat.card Q = q →
        normalizer (Q : Set G) ≤ N → q ∉ sigmaPrimes N →
          ((sigmaCore N : Set G) * ((M ⊓ N : Subgroup G) : Set G) = (N : Set G)) ∧
            sigmaCore N ⊓ M = ⊥ ∧
            FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (M ⊓ N)

@[expose]
def FTS_sigma_overgroup_conjugacy : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ x : G, x ∈ sigmaCore M → x ≠ 1 →
      sigmaSupportingMaximals x = {N : Subgroup G | ∃ g : G, N = conjSub g M ∧ x ∈ N} ∧
        ∀ N ∈ sigmaSupportingMaximals (G := G) x, ∀ T ∈ sigmaSupportingMaximals (G := G) x,
          ∃ g : G, T = conjSub g N

@[expose]
def FTS_sigma_prime_centralizer_transitivity : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ q : ℕ, q.Prime → ∀ Q : Subgroup G, Nat.card Q = q →
      {M : Subgroup G | IsCoatom M ∧ Q ≤ sigmaCore M}.Nonempty →
        ∀ M ∈ {M : Subgroup G | IsCoatom M ∧ Q ≤ sigmaCore M},
          ∀ T ∈ {M : Subgroup G | IsCoatom M ∧ Q ≤ sigmaCore M},
            ∃ c ∈ centralizer (Q : Set G), conjSub c M = T

@[expose]
def FTS_sigma_prime_separation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T →
      (∀ g : G, T ≠ conjSub g M) → sigmaPrimes M ∩ sigmaPrimes T = ∅

@[expose]
def FTS_sigma_subgroup_conjugate_core : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ Y : Subgroup G, Y ≠ ⊥ →
      IsPiSubgroup (sigmaPrimes M) Y → ∃ g : G, conjSub g Y ≤ sigmaCore M

@[expose]
def FTS_sigma_sylow_alpha_product_normal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ p ∈ sigmaPrimes M, ∀ P : Sylow p (sigmaCore M),
      ((alphaCoreIn M : Set G) *
            (((P : Subgroup (sigmaCore M)).map (sigmaCore M).subtype : Subgroup G) : Set G) =
          ((alphaCoreIn M ⊔ (P : Subgroup (sigmaCore M)).map (sigmaCore M).subtype :
            Subgroup G) : Set G)) ∧
        ((alphaCoreIn M ⊔ (P : Subgroup (sigmaCore M)).map
          (sigmaCore M).subtype).subgroupOf M).Normal

@[expose]
def FTS_signalizer_auxiliary_base : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G, 1 < sigmaMultiplicity x →
      ∀ M ∈ sigmaSupportingMaximals (G := G) x,
        ∃ q : ℕ, q.Prime ∧ q ∣ orderOf x ∧ ∃ Q : Subgroup G, Q ≤ zpowers x ∧ Nat.card Q = q ∧
          ∃ N : Subgroup G, IsCoatom N ∧ N ≠ M ∧ normalizer (Q : Set G) ≤ N ∧
            centralizer ({x} : Set G) ≤ N ∧ x ∈ M ⊓ N ∧
            FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (M ⊓ N) ∧
            sigmaPrimes N ∩ sigmaPrimes M = ∅

@[expose]
def FTS_signalizer_auxiliary_prime_support : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G, 1 < sigmaMultiplicity x →
      ∀ M ∈ sigmaSupportingMaximals (G := G) x,
        ∃ q : ℕ, q.Prime ∧ q ∣ orderOf x ∧ ∃ Q : Subgroup G, Q ≤ zpowers x ∧ Nat.card Q = q ∧
          ∃ T : Subgroup G, IsCoatom T ∧ T ≠ M ∧ normalizer (Q : Set G) ≤ T ∧
            centralizer ({x} : Set G) ≤ T ∧ x ∈ M ⊓ T ∧
            FreeCore.IsInternalSemidirectProduct T (sigmaCore T) (M ⊓ T) ∧
            sigmaPrimes T ∩ sigmaPrimes M = ∅ ∧ q ∈ tauTwoPrimes T ∧
            tauTwoPrimes T ⊆ sigmaPrimes M ∧
            (∀ p ∈ sigmaPrimes T, p ∣ Nat.card M → p ∈ betaPrimes T) ∧
            sigmaSignalizer x = centIn (sigmaCore T) {x} ∧ centIn (sigmaCore T) {x} ≠ ⊥

@[expose]
def FTS_signalizer_cosets_disjoint : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G, ∀ y ∈ sigmaSupport G, x ≠ y →
      x • (sigmaSignalizer x : Set G) ∩ y • (sigmaSignalizer y : Set G) = ∅

@[expose]
def FTS_signalizer_nilpotent_supporting_core : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G, 1 < sigmaMultiplicity x →
      ∀ T : Subgroup G, IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) T →
        Group.IsNilpotent (sigmaCore T) ∧ hallCoreIn T = sigmaCore T ∧ hallCoreIn T ≠ ⊥ ∧
          IsGreatest {N : Subgroup G | IsNilpotentNormalHall T N} (hallCoreIn T) ∧
          sigmaSignalizer x = centIn (hallCoreIn T) {x} ∧ centIn (hallCoreIn T) {x} ≠ ⊥ ∧
          x ∉ hallCoreIn T ∧ x ∈ exteriorFixedSet (hallCoreIn T) T

@[expose]
def FTS_signalizer_product_components : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G,
      (∀ r ∈ sigmaSignalizer x,
          (r = 1 → sigmaConstituents (x * r) = {x}) ∧
            (r ≠ 1 → sigmaConstituents (x * r) = {x, r} ∧ r ∈ sigmaSupport G ∧ x ≠ r)) ∧
        (1 : G) ∉ x • (sigmaSignalizer x : Set G)

@[expose]
def FTS_signalizer_regular_action_from_base : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G, ∀ M ∈ sigmaSupportingMaximals (G := G) x, ∀ N : Subgroup G, IsCoatom N →
      centralizer ({x} : Set G) ≤ N → x ∈ M ⊓ N →
        FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (M ⊓ N) →
          (∃ Q : Subgroup G, Q ≤ zpowers x ∧ (Nat.card Q).Prime ∧
            centralizer (Q : Set G) ≤ N) →
            (centIn (sigmaCore N) {x} ≤ centralizer ({x} : Set G) ∧
              ((centIn (sigmaCore N) {x}).subgroupOf (centralizer ({x} : Set G))).Normal ∧
              (Nat.card (centIn (sigmaCore N) {x})).Coprime
                ((centIn (sigmaCore N) {x}).relIndex (centralizer ({x} : Set G)))) ∧
            (∀ r ∈ centIn (sigmaCore N) {x}, ∀ N₁ ∈ sigmaSupportingMaximals (G := G) x,
              conjSub r N₁ ∈ sigmaSupportingMaximals (G := G) x) ∧
            (∀ N₁ ∈ sigmaSupportingMaximals (G := G) x, ∀ N₂ ∈ sigmaSupportingMaximals (G := G) x,
              ∃! r : G, r ∈ centIn (sigmaCore N) {x} ∧ conjSub r N₁ = N₂) ∧
            Nat.card (centIn (sigmaCore N) {x}) = sigmaMultiplicity x

@[expose]
def FTS_signalizer_supporting_type_exterior : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G, 1 < sigmaMultiplicity x →
      ∀ T : Subgroup G, IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) T →
        (IsTypeI T ∨ IsTypeII T) ∧ hallCoreIn T = sigmaCore T ∧
          sigmaSignalizer x = centIn (hallCoreIn T) {x} ∧ centIn (hallCoreIn T) {x} ≠ ⊥ ∧
          (IsTypeI T →
            x ∈ coreFixedSet (hallCoreIn T) T \ ((hallCoreIn T : Set G) \ {1})) ∧
          (IsTypeII T →
            x ∈ coreFixedSet (hallCoreIn T) (⁅T, T⁆ : Subgroup G) \
              ((hallCoreIn T : Set G) \ {1}))

@[expose]
def FTS_signalizer_unique_supporting_maximum : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ x ∈ sigmaSupport G, 1 < sigmaMultiplicity x →
      (∃! T : Subgroup G, IsCoatom T ∧ centralizer ({x} : Set G) ≤ T) ∧
        ∀ T : Subgroup G, IsCoatom T → centralizer ({x} : Set G) ≤ T →
          sigmaSignalizer x = centIn (sigmaCore T) {x} ∧ centIn (sigmaCore T) {x} ≠ ⊥ ∧
            (∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ tauTwoPrimes T) ∧
            ∀ M ∈ sigmaSupportingMaximals (G := G) x, T ≠ M ∧ x ∈ M ⊓ T ∧
              FreeCore.IsInternalSemidirectProduct T (sigmaCore T) (M ⊓ T) ∧
              sigmaPrimes T ∩ sigmaPrimes M = ∅ ∧ tauTwoPrimes T ⊆ sigmaPrimes M ∧
              (∀ p ∈ sigmaPrimes T, p ∣ Nat.card M → p ∈ betaPrimes T)

@[expose]
def FTS_supported_plane_narrow_centralization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ∀ A : Subgroup G, IsMaximalElementaryAbelianPlane p A →
        ∀ Q : Subgroup G, IsPGroup q Q → A ≤ normalizer (Q : Set G) →
          Q ∈ maximalNormalizedPSubgroups A q →
            q ∣ Nat.card (centralizer (A : Set G)) →
              (IsCyclic Q ∨ ∃ B : Subgroup Q, IsMaximalElementaryAbelianPlane q B) →
                ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
                  ((pComplCoreIn p (centralizer ((P : Subgroup G) : Set G)) : Set G) *
                      ((normalizer ((P : Subgroup G) : Set G) ⊓ normalizer (Q : Set G) :
                        Subgroup G) : Set G) =
                    (normalizer ((P : Subgroup G) : Set G) : Set G)) ∧
                  (P : Subgroup G) ≤ ⁅normalizer (Q : Set G), normalizer (Q : Set G)⁆ ∧
                  ⁅(P : Subgroup G), Q⁆ = ⊥

@[expose]
def FTS_supported_plane_sylow_normalizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ∀ A : Subgroup G, IsMaximalElementaryAbelianPlane p A →
        ∀ Q : Subgroup G, IsPGroup q Q → A ≤ normalizer (Q : Set G) →
          Q ∈ maximalNormalizedPSubgroups A q →
            q ∣ Nat.card (centralizer (A : Set G)) →
              ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
                ((pComplCoreIn p (centralizer ((P : Subgroup G) : Set G)) : Set G) *
                    ((normalizer ((P : Subgroup G) : Set G) ⊓ normalizer (Q : Set G) :
                      Subgroup G) : Set G) =
                  (normalizer ((P : Subgroup G) : Set G) : Set G)) ∧
                (P : Subgroup G) ≤ ⁅normalizer (Q : Set G), normalizer (Q : Set G)⁆

@[expose]
def FTS_supporting_type_two_forces_frobenius : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → IsTypeI M →
      ∀ a ∈ coreFixedSet (hallCoreIn M) M, ¬ centralizer ({a} : Set G) ≤ M →
        ∀ T : Subgroup G, IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) T → IsTypeII T →
          ∃ E : Subgroup G, E ≤ M ∧ hallCoreIn M ≠ ⊥ ∧ E ≠ ⊥ ∧
            FreeCore.IsInternalSemidirectProduct M (hallCoreIn M) E ∧
            ∀ e ∈ E, e ≠ 1 → centIn (hallCoreIn M) {e} = ⊥

@[expose]
def FTS_tau_one_and_derived_complement_fixed_core : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ E₁ : Subgroup G, E₁ ≤ E → E₁ ≠ ⊥ →
          IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E) →
            (centIn (sigmaCore M) (E₁ : Set G) ⊓
                centIn (sigmaCore M) ((⁅E, E⁆ : Subgroup G) : Set G) ≤
              ⁅sigmaCore M, sigmaCore M⁆) ∧
            ((tauTwoPrimes M).Nonempty →
              centIn (sigmaCore M) (E₁ : Set G) ⊓
                centIn (sigmaCore M) ((⁅E, E⁆ : Subgroup G) : Set G) = ⊥)

@[expose]
def FTS_tau_one_displacement_normalizer_reflection : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ p r : ℕ, p.Prime → r.Prime → p ∈ tau1Primes M →
          ∀ P : Subgroup G, P ≤ E → Nat.card P = p →
            ∀ R : Subgroup G, R ≤ centIn E (P : Set G) → Nat.card R = r →
              ∀ q a : ℕ, q.Prime → ∀ V : Subgroup G, V ≤ centIn (sigmaCore M) (P : Set G) →
                Nat.card V = q ^ a → R ≤ normalizer (V : Set G) →
                  ⁅V, R⁆ ≠ ⊥ → ∀ T : Subgroup G, IsCoatom T →
                    normalizer (P : Set G) ≤ T →
                      IsUniqueMaximalOvergroup (normalizer ((⁅V, R⁆ : Subgroup G) : Set G)) T ∧
                        q ∈ sigmaPrimes T ∧ q ∉ alphaPrimes M ∧ r ∈ tau1Primes M ∧
                        alphaCoreIn M ≠ ⊥

@[expose]
def FTS_tau_one_displacement_reflected_configuration : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ p r : ℕ, p.Prime → r.Prime → p ∈ tau1Primes M →
          ∀ P : Subgroup G, P ≤ E → Nat.card P = p →
            ∀ R : Subgroup G, R ≤ centIn E (P : Set G) → Nat.card R = r →
              ∀ q a : ℕ, q.Prime → ∀ V : Subgroup G, V ≤ centIn (sigmaCore M) (P : Set G) →
                Nat.card V = q ^ a → R ≤ normalizer (V : Set G) →
                  ⁅V, R⁆ ≠ ⊥ → ∀ T : Subgroup G, IsCoatom T →
                    normalizer (P : Set G) ≤ T →
                      (∀ g : G, T ≠ conjSub g M) ∧ p ∈ sigmaPrimes T ∧ p ∈ betaPrimes T ∧
                        r ∈ tau1Primes T ∧ q ∈ sigmaPrimes M ∧ q ∉ alphaPrimes T ∧
                        IsMulCommutative V ∧
                        R ≤ normalizer ((⁅V, R⁆ : Subgroup G) : Set G) ∧
                        centIn (⁅V, R⁆ : Subgroup G) (R : Set G) = ⊥ ∧
                        P ≤ centIn (alphaCoreIn T) ((R ⊔ ⁅V, R⁆ : Subgroup G) : Set G) ∧
                        centIn (alphaCoreIn T) ((R ⊔ ⁅V, R⁆ : Subgroup G) : Set G) ≠ ⊥

@[expose]
def FTS_tau_one_fixed_line_beta_or_derived : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ E₁ : Subgroup G, E₁ ≤ E → E₁ ≠ ⊥ →
          IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E) →
            ∀ q : ℕ, q.Prime → ∀ X : Subgroup G, X ≤ centIn (sigmaCore M) (E₁ : Set G) →
              Nat.card X = q → q ∈ betaPrimes M ∨ X ≤ ⁅sigmaCore M, sigmaCore M⁆

@[expose]
def FTS_tau_one_fixed_line_centralizer_unique : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ E₁ : Subgroup G, E₁ ≤ E → IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E) →
          ∀ P : Subgroup G, P ≤ E₁ → P ≠ ⊥ →
            ∀ q : ℕ, q.Prime → ∀ X : Subgroup G, X ≤ centIn (sigmaCore M) (P : Set G) →
              Nat.card X = q →
                IsUniqueMaximalOvergroup (centralizer (X : Set G)) M ∧
                  ∀ S : Sylow q (sigmaCore M),
                    IsUniqueMaximalOvergroup
                      (((S : Subgroup (sigmaCore M)).map (sigmaCore M).subtype : Subgroup G)) M

@[expose]
def FTS_tau_one_hall_fixed_centralizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ E₁ : Subgroup G, E₁ ≤ E → IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E) →
          IsCyclic E₁ ∧ ∀ X : Subgroup G, X ≤ E₁ → X ≠ ⊥ →
            centIn (sigmaCore M) (X : Set G) = centIn (sigmaCore M) (E₁ : Set G)

@[expose]
def FTS_tau_one_narrow_normalizer_derived_exclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ p ∈ tau1Primes M, p ∉ betaPrimes G → ∀ q ∈ sigmaPrimes M,
          ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup q Y →
            ¬ p ∣ Nat.card (⁅normalizer (Y : Set G), normalizer (Y : Set G)⁆ : Subgroup G)

@[expose]
def FTS_tau_one_prime_centralizer_inclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ p r : ℕ, p.Prime → r.Prime → p ∈ tau1Primes M →
          ∀ P : Subgroup G, P ≤ E → Nat.card P = p →
            ∀ R : Subgroup G, R ≤ centIn E (P : Set G) → Nat.card R = r →
              centIn (sigmaCore M) (P : Set G) ≤ centIn (sigmaCore M) (R : Set G)

@[expose]
def FTS_tau_one_three_prime_normalizer_transfer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        ∀ p : ℕ, p ∈ tau1Primes M ∪ tau3Primes M →
          ∀ P : Subgroup G, P ≤ M → Nat.card P = p →
            ∀ L : Subgroup G, IsCoatom L → normalizer (P : Set G) ≤ L →
              (∀ g : G, L ≠ conjSub g M) ∧
                (∀ X : Subgroup G, X ≤ E ⊓ L →
                  (∀ s ∈ (Nat.card X).primeFactors, s ∉ tau1Primes L) →
                    X ≤ centralizer ((sigmaCore M ⊓ L : Subgroup G) : Set G)) ∧
                (⁅sigmaCore M ⊓ L, M ⊓ L⁆ ≠ ⊥ →
                  p ∈ sigmaPrimes L ∧ (p ∈ tau1Primes M → p ∈ betaPrimes L))

@[expose]
def FTS_tau_two_maximum_type_one_or_two : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ T : Subgroup G, IsCoatom T → (tauTwoPrimes T).Nonempty → IsTypeI T ∨ IsTypeII T

@[expose]
def FTS_tau_two_subgroup_centralizer_unique : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ →
      (∀ s ∈ (Nat.card X).primeFactors, s ∈ tauTwoPrimes M) →
        centIn (sigmaCore M) (X : Set G) ≠ ⊥ →
          centralizer (X : Set G) ≤ M ∧
            IsUniqueMaximalOvergroup (centralizer (X : Set G)) M

@[expose]
def FTS_type_I_complement_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → IsTypeI M →
      ∀ U : Subgroup G, IsComplementTo M (hallCoreIn M) U →
        (∀ p : ℕ, p.Prime → ∀ P : Sylow p U,
            IsMulCommutative (P : Subgroup U) ∧
              maxElementaryAbelianPRank (P : Subgroup U) ≤ 2) ∧
          ∀ X : Subgroup G, X ≤ U → X ≠ ⊥ → centIn (hallCoreIn M) (X : Set G) ≠ ⊥ →
            centralizer (X : Set G) ≤ M ∧
              ∀ T : Subgroup G, IsCoatom T → centralizer (X : Set G) ≤ T → T = M

@[expose]
def FTS_type_I_core_kappa_identity : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → IsTypeI M →
      kappaPrimes M = ∅ ∧ hallCoreIn M = sigmaCore M ∧
        ∀ U : Subgroup G, IsComplementTo M (hallCoreIn M) U →
          ∀ s ∈ (Nat.card U).primeFactors, s ∉ sigmaPrimes M

@[expose]
def FTS_type_I_dade_support : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → IsTypeI M →
      sigmaCore M = hallCoreIn M ∧
      (∀ a ∈ coreFixedSet (hallCoreIn M) M, ∀ m ∈ M,
          m⁻¹ * a * m ∈ coreFixedSet (hallCoreIn M) M) ∧
      (∀ a ∈ coreFixedSet (hallCoreIn M) M, ∀ b ∈ coreFixedSet (hallCoreIn M) M,
          (∃ g : G, g⁻¹ * a * g = b) → ∃ m ∈ M, m⁻¹ * a * m = b) ∧
      (∀ a ∈ coreFixedSet (hallCoreIn M) M,
          sigmaSignalizerOn M a ≤ centralizer ({a} : Set G) ∧
            ((sigmaSignalizerOn M a).subgroupOf (centralizer ({a} : Set G))).Normal ∧
            ((sigmaSignalizerOn M a : Set G) *
                ((centIn M {a} : Subgroup G) : Set G) = (centralizer ({a} : Set G) : Set G)) ∧
            sigmaSignalizerOn M a ⊓ centIn M {a} = ⊥) ∧
      (∀ a ∈ coreFixedSet (hallCoreIn M) M, ∀ b ∈ coreFixedSet (hallCoreIn M) M,
          (Nat.card (sigmaSignalizerOn M a)).Coprime (Nat.card (centIn M {b}))) ∧
      IsDadeData M (coreFixedSet (hallCoreIn M) M) (sigmaSignalizerOn M) ∧
      (∀ f : G → ℂ, (∀ z : G, z ∉ coreFixedSet (hallCoreIn M) M → f z = 0) →
          (∀ m ∈ M, ∀ z : G, f (m⁻¹ * z * m) = f z) → ∀ z : G,
            (∀ a ∈ coreFixedSet (hallCoreIn M) M,
                (∃ y ∈ dadeCoset (sigmaSignalizerOn M) a, IsConj y z) →
                  dadeSupportExtension (coreFixedSet (hallCoreIn M) M)
                    (sigmaSignalizerOn M) f z = f a) ∧
              ((∀ a ∈ coreFixedSet (hallCoreIn M) M,
                  ∀ y ∈ dadeCoset (sigmaSignalizerOn M) a, ¬ IsConj y z) →
                dadeSupportExtension (coreFixedSet (hallCoreIn M) M)
                  (sigmaSignalizerOn M) f z = 0)) ∧
      ((exteriorFixedSet (hallCoreIn M) M).Nonempty →
          IsTIWithNormalizer (exteriorFixedSet (hallCoreIn M) M) M) ∧
      (∀ a ∈ coreFixedSet (hallCoreIn M) M, ¬ centralizer ({a} : Set G) ≤ M →
          (a ∈ hallCoreIn M ∧ a ≠ 1) ∧
            ∃ T : Subgroup G, IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) T ∧
              (IsTypeI T ∨ IsTypeII T) ∧ hallCoreIn T = sigmaCore T ∧
              FreeCore.IsInternalSemidirectProduct T (hallCoreIn T) (M ⊓ T) ∧
              (IsTypeI T →
                a ∈ coreFixedSet (hallCoreIn T) T \ ((hallCoreIn T : Set G) \ {1})) ∧
              (IsTypeII T →
                a ∈ coreFixedSet (hallCoreIn T) (⁅T, T⁆ : Subgroup G) \
                  ((hallCoreIn T : Set G) \ {1})) ∧
              sigmaSignalizerOn M a = centIn (hallCoreIn T) {a} ∧
              ∀ b ∈ coreFixedSet (hallCoreIn M) M,
                (Nat.card (hallCoreIn T)).Coprime (Nat.card (centIn M {b})))

@[expose]
def FTS_type_I_exterior_power_centralizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → IsTypeI M →
      ∀ k : ℕ, Nat.card (hallCoreIn M) ∣ k →
        k ≡ 1 [MOD (hallCoreIn M).relIndex M] →
          ∀ y ∈ exteriorFixedSet (hallCoreIn M) M,
            y ^ k ≠ 1 ∧ orderOf (y ^ k) ∣ (hallCoreIn M).relIndex M ∧
              centIn (hallCoreIn M) {y ^ k} ≠ ⊥ ∧
              IsUniqueMaximalOvergroup (centralizer ({y ^ k} : Set G)) M

@[expose]
def FTS_type_I_exterior_ti : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → IsTypeI M →
      (exteriorFixedSet (hallCoreIn M) M).Nonempty →
        normalizer (exteriorFixedSet (hallCoreIn M) M) = M ∧
          (∀ g : G, g ∉ M →
            exteriorFixedSet (hallCoreIn M) M ∩
              conjSet g (exteriorFixedSet (hallCoreIn M) M) = ∅) ∧
          ∀ y ∈ exteriorFixedSet (hallCoreIn M) M,
            ∀ z ∈ exteriorFixedSet (hallCoreIn M) M, ∀ g : G, g⁻¹ * y * g = z → g ∈ M

@[expose]
def FTS_type_II_extended_dade_induction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M E W₁ W₂ : Subgroup G, IsCoatom M → IsTypeII M → IsTypeIIWitness M E W₁ W₂ →
      ∀ A₀ : Set G,
        A₀ = coreFixedSet (hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
          conjUnion M (cyclicTIset W₁ W₂) →
        (∀ a ∈ A₀, hallSignalizerOn M a = ⊥) ∧
        (∀ a ∈ A₀, hallSignalizerOn M a ≤ centralizer ({a} : Set G) ∧
            ((hallSignalizerOn M a).subgroupOf (centralizer ({a} : Set G))).Normal ∧
            FreeCore.IsInternalSemidirectProduct (centralizer ({a} : Set G))
              (hallSignalizerOn M a) (centIn M {a})) ∧
        (∀ a ∈ A₀, ∀ b ∈ A₀,
            (Nat.card (hallSignalizerOn M a)).Coprime (Nat.card (centIn M {b}))) ∧
        (∀ a ∈ A₀, ∀ m ∈ M, m⁻¹ * a * m ∈ A₀) ∧ A₀.Nonempty ∧ (1 : G) ∉ A₀ ∧
        (∀ a ∈ A₀, ∀ b ∈ A₀, (∃ g : G, g⁻¹ * a * g = b) → ∃ m ∈ M, m⁻¹ * a * m = b) ∧
        IsDadeData M A₀ (hallSignalizerOn M) ∧
        (∀ f : G → ℂ, (∀ z : G, z ∉ A₀ → f z = 0) →
            (∀ m ∈ M, ∀ z : G, f (m⁻¹ * z * m) = f z) → ∀ g : G,
              ((∀ a ∈ A₀, IsConj a g →
                  dadeSupportExtension A₀ (hallSignalizerOn M) f g = f a) ∧
                ((∀ a ∈ A₀, ¬ IsConj a g) →
                  dadeSupportExtension A₀ (hallSignalizerOn M) f g = 0)) ∧
              dadeSupportExtension A₀ (hallSignalizerOn M) f g = inducedClassFun M f g) ∧
        (∀ f h : G → ℂ, (∀ z : G, z ∉ A₀ → f z = 0) → (∀ z : G, z ∉ A₀ → h z = 0) →
            (∀ m ∈ M, ∀ z : G, f (m⁻¹ * z * m) = f z) →
            (∀ m ∈ M, ∀ z : G, h (m⁻¹ * z * m) = h z) →
              classFunInner G (dadeSupportExtension A₀ (hallSignalizerOn M) f)
                  (dadeSupportExtension A₀ (hallSignalizerOn M) h) =
                classFunInner M (fun m => f m) (fun m => h m)) ∧
        (∀ f : G → ℂ, (∀ z : G, z ∉ A₀ → f z = 0) →
            (∀ m ∈ M, ∀ z : G, f (m⁻¹ * z * m) = f z) →
              (fun m : M => f m) ∈ virtualChars M →
                dadeSupportExtension A₀ (hallSignalizerOn M) f ∈ virtualChars G ∧
                  dadeSupportExtension A₀ (hallSignalizerOn M) f 1 = 0)

@[expose]
def FTS_type_II_extended_support_ti : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M E W₁ W₂ : Subgroup G, IsCoatom M → IsTypeII M → IsTypeIIWitness M E W₁ W₂ →
      ∀ A₀ : Set G,
        A₀ = coreFixedSet (hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
          conjUnion M (cyclicTIset W₁ W₂) →
        hallCoreIn M = sigmaCore M ∧ A₀.Nonempty ∧ A₀ ⊆ (M : Set G) \ {1} ∧
          normalizer A₀ = M ∧ (∀ g : G, g ∉ M → A₀ ∩ conjSet g A₀ = ∅) ∧
          (∀ a ∈ A₀, ∀ b ∈ A₀, ∀ g : G, g⁻¹ * a * g = b → g ∈ M) ∧
          ∀ a ∈ A₀, centralizer ({a} : Set G) = centIn M {a}

end Statements

end

end CFSG.FeitThompson
