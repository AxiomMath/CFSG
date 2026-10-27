module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
public import CFSG.FeitThompson.Definitions.AlphaCore
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.CanonicalCentralizerSignalizerFrom
public import CFSG.FeitThompson.Definitions.TotalDadeSupport
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
public import CFSG.FeitThompson.Representations.DadeReciprocityAveraging
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.OddOrder.SharedSylowNormalizedByIntersection
import Mathlib.Tactic.Group
public import CFSG.FeitThompson.Representations.DadeAveragingClassFunction
public import CFSG.FeitThompson.Representations.TensorAndDualCharacters
public import Mathlib.Data.Complex.Basic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

universe u

variable {G : Type*} [Group G]

namespace Prep08

structure IsMinimalSimpleOddOrder (G : Type*) [Group G] [Finite G] : Prop where
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  odd_natCard : Odd (Nat.card G)
  isSolvable_of_ne_top : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H

@[expose]
def conjSubgroup (Y : Subgroup G) (g : G) : Subgroup G := MulAut.conj g⁻¹ • Y

@[expose]
def conjSet (Y : Set G) (g : G) : Set G := (fun y => g⁻¹ * y * g) '' Y

@[simp]
theorem mem_conjSubgroup_iff {Y : Subgroup G} {g x : G} :
    x ∈ conjSubgroup Y g ↔ g * x * g⁻¹ ∈ Y := by
  rw [conjSubgroup, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; simp [MulAut.conj]

@[simp]
theorem mem_conjSet_iff {Y : Set G} {g x : G} : x ∈ conjSet Y g ↔ g * x * g⁻¹ ∈ Y := by
  simp only [conjSet, Set.mem_image]
  refine ⟨?_, fun h => ⟨g * x * g⁻¹, h, by group⟩⟩
  rintro ⟨y, hy, rfl⟩
  have h : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [h]; exact hy

theorem coe_conjSubgroup (Y : Subgroup G) (g : G) :
    ((conjSubgroup Y g : Subgroup G) : Set G) = conjSet (Y : Set G) g := by ext x; simp

@[simp]
theorem conjSubgroup_one (Y : Subgroup G) : conjSubgroup Y 1 = Y := by ext x; simp

@[simp]
theorem conjSet_one (Y : Set G) : conjSet Y 1 = Y := by ext x; simp

@[expose]
def IsSylowOf (p : ℕ) (P M : Subgroup G) : Prop :=
  ∃ S : Sylow p ↥M, (S : Subgroup ↥M).map M.subtype = P

theorem IsSylowOf.le {p : ℕ} {P M : Subgroup G} (h : IsSylowOf p P M) : P ≤ M := by
  obtain ⟨S, rfl⟩ := h; exact Subgroup.map_subtype_le _

theorem IsSylowOf.isPGroup {p : ℕ} {P M : Subgroup G} (h : IsSylowOf p P M) : IsPGroup p ↥P := by
  obtain ⟨S, rfl⟩ := h; exact S.isPGroup'.map M.subtype

theorem isSylowOf_iff_natCard [Finite G] {p : ℕ} (hp : p.Prime) {P M : Subgroup G} (hPM : P ≤ M) :
    IsSylowOf p P M ↔ Nat.card ↥P = p ^ (Nat.card ↥M).factorization p :=
  have : Fact p.Prime := ⟨hp⟩
  (natCard_eq_pow_factorization_iff_exists_sylow hPM).symm

theorem isSylowOf_top_iff [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G} :
    IsSylowOf p P (⊤ : Subgroup G) ↔ ∃ S : Sylow p G, (S : Subgroup G) = P := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨S, rfl⟩
    have hc : Nat.card ↥((S : Subgroup ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype)
        = p ^ (Nat.card G).factorization p := by
      rw [Subgroup.card_subtype]; simpa using S.card_eq_multiplicity
    exact ⟨Sylow.ofCard _ hc, Sylow.coe_ofCard _ hc⟩
  · rintro ⟨S, rfl⟩
    have hc : Nat.card ↥((S : Subgroup G).subgroupOf ⊤)
        = p ^ (Nat.card ↥(⊤ : Subgroup G)).factorization p := by
      rw [← Subgroup.card_subtype (⊤ : Subgroup G), Subgroup.subgroupOf_map_subtype]
      simp [S.card_eq_multiplicity]
    exact ⟨Sylow.ofCard _ hc, by rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le le_top]⟩

@[expose]
def IsPlaneAt (p : ℕ) (A : Subgroup G) : Prop :=
  IsElementaryAbelian p A ∧ Nat.card ↥A = p ^ 2

theorem IsPlaneAt.isElementaryAbelian {p : ℕ} {A : Subgroup G} (h : IsPlaneAt p A) :
    IsElementaryAbelian p A := h.1

theorem IsPlaneAt.natCard {p : ℕ} {A : Subgroup G} (h : IsPlaneAt p A) :
    Nat.card ↥A = p ^ 2 := h.2

theorem IsPlaneAt.isMulCommutative {p : ℕ} {A : Subgroup G} (h : IsPlaneAt p A) :
    IsMulCommutative ↥A := (isElementaryAbelian_iff.1 h.1).1

theorem IsPlaneAt.elementaryAbelianPRank_eq [Finite G] {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (h : IsPlaneAt p A) : elementaryAbelianPRank p ↥A = 2 :=
  have hA := isElementaryAbelian_iff.1 h.1
  have : IsMulCommutative ↥A := hA.1
  elementaryAbelianPRank_eq_of_card_eq hp hA.2 h.2

@[expose]
def IsHallOf (π : Set ℕ) (Y M : Subgroup G) : Prop :=
  Y ≤ M ∧ IsHallPiSubgroup π (Y.subgroupOf M)

theorem IsHallOf.le {π : Set ℕ} {Y M : Subgroup G} (h : IsHallOf π Y M) : Y ≤ M := h.1

theorem IsHallOf.isHallPiSubgroup {π : Set ℕ} {Y M : Subgroup G} (h : IsHallOf π Y M) :
    IsHallPiSubgroup π (Y.subgroupOf M) := h.2

theorem IsHallOf.coprime [Finite G] {π : Set ℕ} {Y M : Subgroup G} (h : IsHallOf π Y M) :
    (Nat.card ↥(Y.subgroupOf M)).Coprime (Y.subgroupOf M).index := h.2.coprime_natCard_index

@[expose]
def alphaCoreOf [Finite G] (M : Subgroup G) : Subgroup G := (alphaCore ↥M).map M.subtype

theorem alphaCoreOf_le [Finite G] (M : Subgroup G) : alphaCoreOf M ≤ M := Subgroup.map_subtype_le _

theorem subgroupOf_alphaCoreOf [Finite G] (M : Subgroup G) :
    (alphaCoreOf M).subgroupOf M = alphaCore ↥M := by
  rw [alphaCoreOf, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

@[expose]
def pCoreOfSubgroup [Finite G] (p : ℕ) (M : Subgroup G) : Subgroup G := (pCore p ↥M).map M.subtype

theorem pCoreOfSubgroup_le [Finite G] (p : ℕ) (M : Subgroup G) : pCoreOfSubgroup p M ≤ M :=
  Subgroup.map_subtype_le _

theorem subgroupOf_pCoreOfSubgroup [Finite G] (p : ℕ) (M : Subgroup G) :
    (pCoreOfSubgroup p M).subgroupOf M = pCore p ↥M := by
  rw [pCoreOfSubgroup, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

@[expose]
def fittingOf [Finite G] (M : Subgroup G) : Subgroup G := (fittingRaw ↥M).map M.subtype

theorem fittingOf_le [Finite G] (M : Subgroup G) : fittingOf M ≤ M := Subgroup.map_subtype_le _

theorem subgroupOf_fittingOf [Finite G] (M : Subgroup G) :
    (fittingOf M).subgroupOf M = fittingRaw ↥M := by
  rw [fittingOf, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

@[expose]
noncomputable def sigmaCoreSignalizer (G : Type*) [Group G] [Finite G] (x : G) : Subgroup G :=
  canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x

theorem sigmaCoreSignalizer_le_centralizer [Finite G] (x : G) :
    sigmaCoreSignalizer G x ≤ centralizer ({x} : Set G) := canonicalSignalizer_le_centralizer

@[expose]
noncomputable def sigmaPacket (G : Type*) [Group G] [Finite G] (M : Subgroup G) : Set G :=
  ⋃ x ∈ (sigmaCore M : Set G) \ {1}, x • (sigmaCoreSignalizer G x : Set G)

@[expose]
noncomputable def sigmaPacketSupport (G : Type*) [Group G] [Finite G] (M : Subgroup G) : Set G :=
  ⋃ g : G, conjSet (sigmaPacket G M) g

theorem mem_sigmaPacket_iff [Finite G] {M : Subgroup G} {y : G} :
    y ∈ sigmaPacket G M ↔ ∃ x ∈ (sigmaCore M : Set G) \ {1}, x⁻¹ * y ∈ sigmaCoreSignalizer G x := by
  simp only [sigmaPacket, Set.mem_iUnion, Set.mem_smul_set, smul_eq_mul, exists_prop,
    SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, r, hr, rfl⟩; exact ⟨x, hx, by simpa using hr⟩
  · rintro ⟨x, hx, h⟩; exact ⟨x, hx, x⁻¹ * y, h, by group⟩

theorem sigmaPacket_eq_dadeCosetUnion [Finite G] (M : Subgroup G) :
    sigmaPacket G M = dadeCosetUnion ((sigmaCore M : Set G) \ {1}) (sigmaCoreSignalizer G) := by
  ext y
  rw [mem_sigmaPacket_iff, mem_dadeCosetUnion_iff]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  rw [mem_dadeCoset_iff]
  have key : ∀ z : G, z ∈ sigmaCoreSignalizer G x → z * x = x * z := fun z hz =>
    mul_comm_of_mem_canonicalSignalizer (𝓜 := {M : Subgroup G | IsCoatom M})
      (S := sigmaCore) (x := x) hz
  constructor
  · intro h
    have h2 : x⁻¹ * y * x = y := by have := key _ h; rw [this]; group
    have h3 : y * x⁻¹ = x⁻¹ * y := by
      calc y * x⁻¹ = x⁻¹ * y * x * x⁻¹ := by rw [h2]
        _ = x⁻¹ * y := by group
    rw [h3]; exact h
  · intro h
    have h2 : y * x⁻¹ * x = y := by group
    have h3 : x⁻¹ * y = y * x⁻¹ := by
      have hk := key _ h
      calc x⁻¹ * y = x⁻¹ * (y * x⁻¹ * x) := by rw [h2]
        _ = x⁻¹ * (x * (y * x⁻¹)) := by rw [hk]
        _ = y * x⁻¹ := by group
    rw [h3]; exact h

theorem sigmaPacketSupport_eq_totalDadeSupport [Finite G] (M : Subgroup G) :
    sigmaPacketSupport G M
      = totalDadeSupport ((sigmaCore M : Set G) \ {1}) (sigmaCoreSignalizer G) := by
  ext y
  simp only [sigmaPacketSupport, conjSet, Set.mem_iUnion, Set.mem_image,
    mem_totalDadeSupport_iff_exists_isConj, sigmaPacket_eq_dadeCosetUnion, mem_dadeCosetUnion_iff]
  constructor
  · rintro ⟨g, z, ⟨a, ha, hz⟩, rfl⟩
    exact ⟨a, ha, z, hz, isConj_iff.2 ⟨g⁻¹, by group⟩⟩
  · rintro ⟨a, ha, z, hz, hc⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    exact ⟨c⁻¹, z, ⟨a, ha, hz⟩, by simpa using hc⟩

theorem sigmaPacket_subset_sigmaPacketSupport [Finite G] (M : Subgroup G) :
    sigmaPacket G M ⊆ sigmaPacketSupport G M := by
  intro y hy
  exact Set.mem_iUnion.2 ⟨1, by simpa using hy⟩

structure IsKappaResidualSetup [Finite G] (M K U A Mstar R H : Subgroup G) (r : ℕ) : Prop where
  isCoatom_M : IsCoatom M
  kappa_nonempty : (kappaPrimes M).Nonempty
  isHall_K : IsHallOf (kappaPrimes M) K M
  isHall_U : IsHallOf {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M ∧ p ∉ kappaPrimes M} U M
  semidirect_M : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K)
  semidirect_UK : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K
  isMulCommutative_U : IsMulCommutative ↥U
  centralizer_U : ∀ k ∈ K, k ≠ 1 → U ⊓ centralizer ({k} : Set G) = ⊥
  U_ne_bot : U ≠ ⊥
  A_eq : A = sigmaCore M ⊓ centralizer ((K : Subgroup G) : Set G)
  isCoatom_Mstar : IsCoatom Mstar
  exists_prime_order_le_K : ∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
    normalizer ((X : Subgroup G) : Set G) ≤ Mstar
  prime_r : r.Prime
  r_dvd : r ∣ Nat.card ↥U
  isSylow_R : IsSylowOf r R U
  isCoatom_H : IsCoatom H
  normalizer_R_le : normalizer ((R : Subgroup G) : Set G) ≤ H

structure IsNonuniqueLineSetup [Finite G] (M A : Subgroup G) (p : ℕ) : Prop where
  isCoatom_M : IsCoatom M
  prime : p.Prime
  le : A ≤ M
  isPlane : IsPlaneAt p A
  nonunique : ∀ Y ≤ A, Nat.card ↥Y = p →
    ∃ T : Subgroup G, IsCoatom T ∧ T ≠ M ∧ normalizer ((Y : Subgroup G) : Set G) ≤ T

structure IsOtherLineSetup [Finite G] (M T A A0 : Subgroup G) (p : ℕ) : Prop where
  isCoatom_M : IsCoatom M
  isCoatom_T : IsCoatom T
  ne : M ≠ T
  prime : p.Prime
  le : A ≤ M
  isPlane : IsPlaneAt p A
  le_A : A0 ≤ A
  natCard_A0 : Nat.card ↥A0 = p
  normalizer_le : normalizer ((A0 : Subgroup G) : Set G) ≤ T

structure IsRegularTauOneAlphaSetup [Finite G] (M P Q : Subgroup G) (p q : ℕ) : Prop where
  isCoatom_M : IsCoatom M
  mem_tau1 : p ∈ tau1Primes M
  prime_q : q.Prime
  q_ne : q ≠ p
  q_notMem_alpha : q ∉ alphaPrimes ↥M
  le_P : P ≤ M
  natCard_P : Nat.card ↥P = p
  le_Q : Q ≤ M
  Q_ne_bot : Q ≠ ⊥
  isPGroup_Q : IsPGroup q ↥Q
  normalized : P ≤ normalizer ((Q : Subgroup G) : Set G)
  centralizer_eq : Q ⊓ centralizer ((P : Subgroup G) : Set G) = ⊥
  not_unique : {N : Subgroup G | IsCoatom N ∧ normalizer ((Q : Subgroup G) : Set G) ≤ N} ≠ {M}

end Prep08

namespace Statements

open Prep08

@[expose]
def FTS_kappa_residual_prime_overgroup_position : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K U A Mstar R H : Subgroup G, ∀ r : ℕ,
      IsKappaResidualSetup M K U A Mstar R H r →
      (Nat.card ↥K).Prime ∧ (U ⊔ K : Subgroup G) ≤ H ∧
        (∀ g : G, H ≠ conjSubgroup M g) ∧ (∀ g : G, H ≠ conjSubgroup Mstar g) ∧
        kappaPrimes H = ∅ ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p ∉ sigmaPrimes H

@[expose]
def FTS_kappa_residual_rank_two_exclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K U A Mstar R H : Subgroup G, ∀ r : ℕ,
      IsKappaResidualSetup M K U A Mstar R H r → (tauTwoPrimes H).Nonempty →
      (Nat.card ↥K).Prime ∧ tauTwoPrimes H = {Nat.card ↥K} ∧ tauTwoPrimes M = ∅ ∧
        ¬ centralizer ((U : Subgroup G) : Set G) ≤ M

@[expose]
def FTS_low_rank_ambient_sylow_derived_central : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ p : ℕ, p.Prime → Odd p → ∀ P : Sylow p G,
      elementaryAbelianPRank p ↥(P : Subgroup G) ≤ 2 →
      ⁅(P : Subgroup G), (P : Subgroup G)⁆ ≤
        (P : Subgroup G) ⊓ centralizer (((P : Subgroup G) : Set G))

@[expose]
def FTS_nilpotent_sigma_prime_separation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → (∀ g : G, T ≠ conjSubgroup M g) →
      Group.IsNilpotent ↥(sigmaCore M) →
      sigmaPrimes M ∩ sigmaPrimes T = ∅ ∧ sigmaCore M ⊓ sigmaCore T = ⊥

@[expose]
def FTS_nonconjugate_intersection_tau_one_beta : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M E L : Subgroup G, ∀ p : ℕ, IsCoatom M → E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
      IsCoatom L → (∀ g : G, L ≠ conjSubgroup M g) →
      p ∈ tau1Primes M → p ∈ sigmaPrimes L →
      ⁅sigmaCore M ⊓ L, M ⊓ L⁆ ≠ ⊥ → p ∈ betaPrimes G ∧ p ∈ betaPrimes ↥L

@[expose]
def FTS_nonconjugate_packets_disjoint : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → (∀ g : G, T ≠ conjSubgroup M g) →
      sigmaPacketSupport G M ∩ sigmaPacketSupport G T = ∅

@[expose]
def FTS_noncyclic_sigma_normalizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M X : Subgroup G, ∀ p : ℕ, IsCoatom M → p ∈ sigmaPrimes M → X ≤ M →
      IsPGroup p ↥X → ¬ IsCyclic ↥X → normalizer ((X : Subgroup G) : Set G) ≤ M

@[expose]
def FTS_nontrivial_kappa_support_residual_witness : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N → ∀ x ∈ sigmaCore M, x ≠ 1 →
      ¬ centralizer ({x} : Set G) ≤ M → centralizer ({x} : Set G) ≤ N →
      (kappaPrimes N).Nonempty →
      IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) N ∧
        FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (M ⊓ N) ∧
        (tauTwoPrimes N).Nonempty ∧
        ∃ r : ℕ, ∃ K U R : Subgroup G,
          r ∈ tauTwoPrimes N ∩ sigmaPrimes M ∧ K ≤ M ⊓ N ∧ U ≤ M ⊓ N ∧ R ≤ U ∧
          (Nat.card ↥K).Prime ∧ IsHallOf (kappaPrimes N) K N ∧
          U ≠ ⊥ ∧ IsMulCommutative ↥U ∧
          IsHallOf {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes N ∧ p ∉ kappaPrimes N} U N ∧
          FreeCore.IsInternalSemidirectProduct (M ⊓ N) U K ∧
          (∀ k ∈ K, k ≠ 1 → U ⊓ centralizer ({k} : Set G) = ⊥) ∧
          IsSylowOf r R U ∧ IsSylowOf r R N ∧ ¬ IsCyclic ↥R ∧
          normalizer ((R : Subgroup G) : Set G) ≤ M

@[expose]
def FTS_nonunique_line_centralizer_bounds : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M A : Subgroup G, ∀ p : ℕ, IsNonuniqueLineSetup M A p →
      (∀ Y ≤ A, Nat.card ↥Y = p → ∀ r : ℕ,
        elementaryAbelianPRank r ↥(M ⊓ centralizer ((Y : Subgroup G) : Set G)) ≤ 2) ∧
      (p ∉ sigmaPrimes M → ∀ Y ≤ A, Nat.card ↥Y = p →
        sigmaCore M ⊓ centralizer ((Y : Subgroup G) : Set G) ≤
          M ⊓ centralizer ((A : Subgroup G) : Set G)) ∧
      (p ∉ alphaPrimes ↥M → ∀ Y ≤ A, Nat.card ↥Y = p →
        alphaCoreOf M ⊓ centralizer ((Y : Subgroup G) : Set G) ≤
          M ⊓ centralizer ((A : Subgroup G) : Set G)) ∧
      ∀ r : ℕ, elementaryAbelianPRank r ↥(M ⊓ centralizer ((A : Subgroup G) : Set G)) ≤ 2

@[expose]
def FTS_nonunique_lines_alpha_core_trivial : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M A : Subgroup G, ∀ p : ℕ, IsNonuniqueLineSetup M A p →
      alphaCoreOf M = ⊥ ∧ Group.IsNilpotent ↥(sigmaCore M) ∧
      ∀ P : Subgroup G, IsSylowOf p P M → A ≤ P →
        ∀ Z0 : Subgroup G,
          (Z0 : Set G) = {z | z ∈ P ∧ (∀ y ∈ P, z * y = y * z) ∧ z ^ p = 1} →
          Z0 ≠ ⊥ ∧ Z0 ≤ A ∧ elementaryAbelianPRank p ↥P = 2 ∧ p ∉ alphaPrimes ↥M

@[expose]
def FTS_nonunique_lines_force_sigma : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M A : Subgroup G, ∀ p : ℕ, IsNonuniqueLineSetup M A p → p ∈ sigmaPrimes M

@[expose]
def FTS_normalizer_complement_plane_assembly : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M N Q : Subgroup G, ∀ q : ℕ, IsCoatom M → IsCoatom N → M ≠ N →
      q ∈ sigmaPrimes M → Q ≤ M → Nat.card ↥Q = q →
      normalizer ((Q : Subgroup G) : Set G) ≤ N → q ∉ sigmaPrimes N →
      FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (M ⊓ N)

@[expose]
def FTS_normalizer_intersection_sylow : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M N Q T : Subgroup G, ∀ p : ℕ, IsCoatom M → IsCoatom N → M ≠ N →
      p ∈ sigmaPrimes M → Q ≤ M → Nat.card ↥Q = p →
      normalizer ((Q : Subgroup G) : Set G) ≤ N →
      IsSylowOf p T (M ⊓ N) → Q ≤ T →
      normalizer ((T : Subgroup G) : Set G) ≤ M ∧ IsSylowOf p T N

@[expose]
def FTS_opposite_sigma_normalizer_beta_support : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M T Y : Subgroup G, ∀ q : ℕ, IsCoatom M → IsCoatom T → M ≠ T →
      q.Prime → q ∈ sigmaPrimes M → Y ≤ M → Y ≠ ⊥ → IsPGroup q ↥Y →
      normalizer ((Y : Subgroup G) : Set G) ≤ T → q ∉ sigmaPrimes T →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥M → p ∈ sigmaPrimes T → p ∈ betaPrimes ↥T

@[expose]
def FTS_opposite_sigma_plane_core_intersection : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M N A : Subgroup G, ∀ p : ℕ, IsCoatom M → IsCoatom N →
      p ∈ sigmaPrimes M → p ∉ sigmaPrimes N → A ≤ M ⊓ N → IsPlaneAt p A →
      sigmaCore N ⊓ M = ⊥

@[expose]
def FTS_ordered_two_prime_hall_nilpotent : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M X Y W : Subgroup G, ∀ p q : ℕ, IsCoatom M →
      p.Prime → q.Prime → Odd p → Odd q → p < q →
      p ∉ betaPrimes ↥M → q ∉ betaPrimes ↥M →
      X ≤ M → IsPGroup q ↥X → Y = X ⊔ ⁅M, M⁆ → X ≤ W → W ≤ Y →
      IsHallOf {p, q} W Y → Group.IsNilpotent ↥W

@[expose]
def FTS_other_line_normalizer_alpha_centralization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M T A A0 : Subgroup G, ∀ p : ℕ, IsOtherLineSetup M T A A0 p →
      p ∈ sigmaPrimes M → p ∉ alphaPrimes ↥M → ⁅A, alphaCoreOf M ⊓ T⁆ = ⊥

@[expose]
def FTS_other_line_normalizer_plane_product : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M T A A0 : Subgroup G, ∀ p : ℕ, IsOtherLineSetup M T A A0 p →
      A ≤ T ∧ T ≤ normalizer (((sigmaCore T ⊔ A : Subgroup G)) : Set G)

@[expose]
def FTS_other_line_normalizer_sigma_centralization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M T A A0 : Subgroup G, ∀ p : ℕ, IsOtherLineSetup M T A A0 p →
      p ∉ sigmaPrimes M → ⁅A, sigmaCore M ⊓ T⁆ = ⊥

@[expose]
def FTS_outside_beta_invariant_sylow_centralizes_derived_complement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M E V : Subgroup G, ∀ q : ℕ, IsCoatom M → E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
      q.Prime → Odd q → q ∉ betaPrimes ↥M →
      IsSylowOf q V (sigmaCore M) → E ≤ normalizer ((V : Subgroup G) : Set G) →
      ⁅V, ⁅E, E⁆⁆ = ⊥

@[expose]
def FTS_outside_sigma_core_centralizer_rank_one : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K : Subgroup G, IsCoatom M → K ≤ M →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p ∉ sigmaPrimes M) →
      ∀ p : ℕ,
        elementaryAbelianPRank p ↥(K ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)) ≤ 1

@[expose]
def FTS_outside_sigma_derived_centralizer_cyclic : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K Y : Subgroup G, IsCoatom M → K ≤ M →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p ∉ sigmaPrimes M) →
      Y = K ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G) ⊓ ⁅M, M⁆ →
      IsCyclic ↥Y ∧ M ≤ normalizer ((Y : Subgroup G) : Set G)

@[expose]
def FTS_outside_sigma_fixed_free_line_commutator : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K P : Subgroup G, ∀ p : ℕ, IsCoatom M → p.Prime → p ∉ sigmaPrimes M →
      K ≤ M → IsMulCommutative ↥K →
      (∀ s : ℕ, s.Prime → s ∣ Nat.card ↥K → s ∉ sigmaPrimes M) →
      ¬ p ∣ Nat.card ↥K →
      P ≤ normalizer ((K : Subgroup G) : Set G) ⊓ M → Nat.card ↥P = p →
      sigmaCore M ⊓ centralizer ((P : Subgroup G) : Set G) = ⊥ →
      ⁅K, P⁆ ≤ centralizer ((sigmaCore M : Subgroup G) : Set G) ∧
        IsCyclic ↥⁅K, P⁆ ∧ M ≤ normalizer ((⁅K, P⁆ : Subgroup G) : Set G)

@[expose]
def FTS_outside_sigma_plane_complement_normality : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M A E : Subgroup G, ∀ p : ℕ, IsCoatom M → p.Prime → p ∉ sigmaPrimes M →
      A ≤ M → IsPlaneAt p A → E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E → A ≤ E →
      E ≤ normalizer ((A : Subgroup G) : Set G)

@[expose]
def FTS_outside_sigma_plane_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M A : Subgroup G, ∀ p : ℕ, IsCoatom M → p.Prime → p ∉ sigmaPrimes M →
      A ≤ M → IsPlaneAt p A →
      Group.IsNilpotent ↥(sigmaCore M) ∧
        sigmaCore M ⊓ centralizer ((A : Subgroup G) : Set G) = ⊥ ∧
        M ≤ normalizer (((sigmaCore M ⊔ A : Subgroup G)) : Set G)

@[expose]
def FTS_packet_cardinality : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M →
      (sigmaPacketSupport G M).ncard = (Nat.card ↥(sigmaCore M) - 1) * M.index ∧
        (sigmaPacketSupport G M).Nonempty

@[expose]
def FTS_packet_conjugation_description : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ XM : Set G,
      XM = ⋃ g : G, conjSet ((sigmaCore M : Set G) \ {1}) g →
      sigmaPacketSupport G M = ⋃ x ∈ XM, x • (sigmaCoreSignalizer G x : Set G) ∧
        (∀ g : G, sigmaPacket G (conjSubgroup M g) = conjSet (sigmaPacket G M) g) ∧
        (∀ g : G, sigmaPacketSupport G (conjSubgroup M g) = sigmaPacketSupport G M) ∧
        (∀ g : G, conjSet (sigmaPacketSupport G M) g = sigmaPacketSupport G M) ∧
        (1 : G) ∉ sigmaPacketSupport G M

@[expose]
def FTS_plane_centralizing_subgroup_unique_centralizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M A X : Subgroup G, ∀ p : ℕ, IsCoatom M → p.Prime → p ∉ sigmaPrimes M →
      A ≤ M → IsPlaneAt p A → X ≤ M → X ≠ ⊥ → ⁅X, A⁆ = ⊥ →
      sigmaCore M ⊓ centralizer ((X : Subgroup G) : Set G) ≠ ⊥ →
      centralizer ((X : Subgroup G) : Set G) ≤ M ∧
        ∀ N : Subgroup G, IsCoatom N → centralizer ((X : Subgroup G) : Set G) ≤ N → N = M

@[expose]
def FTS_plane_maximal_overgroups : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M A : Subgroup G, ∀ p : ℕ, IsCoatom M → p.Prime → A ≤ M → IsPlaneAt p A →
      centralizer ((A : Subgroup G) : Set G) ≤ M ∧
        (p ∉ sigmaPrimes M → ∃ A0 : Subgroup G, A0 ≤ A ∧ Nat.card ↥A0 = p ∧
          normalizer ((A0 : Subgroup G) : Set G) ≤ M)

@[expose]
def FTS_proper_subgroup_p_length_one : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ p : ℕ, p.Prime → ∀ H : Subgroup G, H ≠ ⊤ →
      ¬ p ∣ (Subgroup.comap (QuotientGroup.mk' (pComplCore p ↥H))
        (pCore p (↥H ⧸ pComplCore p ↥H))).index

@[expose]
def FTS_regular_plane_fixed_lines_not_conjugate : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M E A Q D X : Subgroup G, ∀ p q : ℕ, IsCoatom M → E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
      p ∈ tauTwoPrimes M → A ≤ E → IsPlaneAt p A →
      q ∈ tau1Primes M → Q ≤ E → Nat.card ↥Q = q →
      sigmaCore M ⊓ centralizer ((Q : Subgroup G) : Set G) = ⊥ → ⁅A, Q⁆ ≠ ⊥ →
      D = ⁅A, Q⁆ → X = A ⊓ centralizer ((Q : Subgroup G) : Set G) →
      Nat.card ↥D = p ∧ Nat.card ↥X = p ∧
        (D ⊔ X = A ∧ D ⊓ X = ⊥ ∧ ⁅D, X⁆ = ⊥) ∧
        D = A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G) ∧
        M ≤ normalizer ((D : Subgroup G) : Set G) ∧
        ¬ q ∣ Nat.card ↥(centralizer ((D : Subgroup G) : Set G)) ∧
        q ∣ Nat.card ↥(centralizer ((X : Subgroup G) : Set G)) ∧
        ∀ g : G, conjSubgroup D g ≠ X

@[expose]
def FTS_regular_tau_one_alpha_centralizer_rank_bounds : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M P Q : Subgroup G, ∀ p q : ℕ, IsRegularTauOneAlphaSetup M P Q p q →
      ∀ r : ℕ,
        elementaryAbelianPRank r ↥(alphaCoreOf M ⊓ centralizer ((P : Subgroup G) : Set G)) ≤ 1 ∧
        elementaryAbelianPRank r ↥(alphaCoreOf M ⊓ centralizer ((Q : Subgroup G) : Set G)) ≤ 1

@[expose]
def FTS_regular_tau_one_alpha_fixed_points : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M P Q : Subgroup G, ∀ p q : ℕ, IsRegularTauOneAlphaSetup M P Q p q →
      alphaCoreOf M ≠ ⊥ →
      alphaCoreOf M ⊓ centralizer ((P : Subgroup G) : Set G) ≠ ⊥ ∧
        alphaCoreOf M ⊓ centralizer (((Q ⊔ P : Subgroup G)) : Set G) = ⊥

@[expose]
def FTS_residual_exterior_power_ti : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K U B : Subgroup G, IsCoatom M → IsHallOf (kappaPrimes M) K M → U ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K) →
      FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K →
      B = sigmaCore M ⊔ U →
      ∀ D : Set G,
        D = {y | y ∈ B ∧ y ∉ sigmaCore M ∧
          sigmaCore M ⊓ centralizer ({y} : Set G) ≠ ⊥} →
        (∀ k : ℕ, Nat.card ↥(sigmaCore M) ∣ k → (Nat.card ↥U : ℤ) ∣ (k : ℤ) - 1 →
            ∀ y ∈ D, y ^ k ≠ 1 ∧ orderOf (y ^ k) ∣ Nat.card ↥U ∧
              IsUniqueMaximalOvergroup (centralizer ({y ^ k} : Set G)) M) ∧
        (D.Nonempty →
          normalizer D = M ∧
          (∀ g : G, g ∉ M → D ∩ conjSet D g = ∅) ∧
          (∀ y ∈ D, ∀ z ∈ D, ∀ g : G, g⁻¹ * y * g = z → g ∈ M) ∧
          ∀ y ∈ D, centralizer ({y} : Set G) ≤ M)

@[expose]
def FTS_residual_normalizer_single_rank_two_prime : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K U A Mstar R H : Subgroup G, ∀ r : ℕ,
      IsKappaResidualSetup M K U A Mstar R H r → (tauTwoPrimes H).Nonempty →
      (Nat.card ↥K).Prime ∧ tauTwoPrimes H = {Nat.card ↥K} ∧
        Nat.card ↥K ∉ betaPrimes G ∧ Nat.card ↥K ∉ betaPrimes ↥Mstar

@[expose]
def FTS_residual_partner_nilpotent_nonabelian_sylow : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K U A Mstar R H : Subgroup G, ∀ r : ℕ,
      IsKappaResidualSetup M K U A Mstar R H r → (tauTwoPrimes H).Nonempty →
      Group.IsNilpotent ↥(sigmaCore Mstar) ∧
        FreeCore.IsInternalSemidirectProduct Mstar (sigmaCore Mstar) A ∧
        ⁅Mstar, Mstar⁆ = sigmaCore Mstar ∧
        ¬ IsMulCommutative ↥(pCoreOfSubgroup (Nat.card ↥K) Mstar) ∧
        Mstar ≤ normalizer ((pCoreOfSubgroup (Nat.card ↥K) Mstar : Subgroup G) : Set G) ∧
        IsSylowOf (Nat.card ↥K) (pCoreOfSubgroup (Nat.card ↥K) Mstar) Mstar ∧
        IsSylowOf (Nat.card ↥K) (pCoreOfSubgroup (Nat.card ↥K) Mstar) ⊤

@[expose]
def FTS_residual_rank_two_plane_partner_fitting : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M K U A Mstar R H : Subgroup G, ∀ r : ℕ,
      IsKappaResidualSetup M K U A Mstar R H r → (tauTwoPrimes H).Nonempty →
      (∀ p : ℕ, p ∈ tauTwoPrimes H → ∀ B : Subgroup G, B ≤ H ⊓ Mstar → IsPlaneAt p B →
        (Nat.card ↥K).Prime ∧ ⁅B, K⁆ = ⊥ ∧ p ∈ sigmaPrimes Mstar ∧ B ≤ fittingOf Mstar ∧
          IsSylowOf (Nat.card ↥K) (pCoreOfSubgroup (Nat.card ↥K) Mstar) Mstar ∧
          Mstar ≤ normalizer ((pCoreOfSubgroup (Nat.card ↥K) Mstar : Subgroup G) : Set G) ∧
          IsUniqueMaximalOvergroup (pCoreOfSubgroup (Nat.card ↥K) Mstar) Mstar) ∧
      ∀ p : ℕ, p ∈ tauTwoPrimes H → ∃ B : Subgroup G, B ≤ H ⊓ Mstar ∧ IsPlaneAt p B

@[expose]
def FTS_shared_sigma_sylow_setup : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M L : Subgroup G, ∀ q : ℕ, IsCoatom M → IsCoatom L →
      (∀ x : G, L ≠ conjSubgroup M x) →
      q ∈ sigmaPrimes M → q ∈ sigmaPrimes L →
      ∃ E Q : Subgroup G, ∃ g : G,
        E ≤ M ∧ E ≠ ⊥ ∧ FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E ∧
        Q ≠ ⊥ ∧ IsSylowOf q Q (sigmaCore M) ∧ IsSylowOf q Q M ∧ IsSylowOf q Q ⊤ ∧
        IsSylowOf q Q (conjSubgroup L g) ∧ IsSylowOf q Q (sigmaCore (conjSubgroup L g)) ∧
        E ≤ normalizer ((Q : Subgroup G) : Set G) ∧
        normalizer ((Q : Subgroup G) : Set G) ≤ M ⊓ conjSubgroup L g ∧
        E ≤ M ⊓ conjSubgroup L g ∧
        Q ≤ sigmaCore M ⊓ sigmaCore (conjSubgroup L g) ∧
        ∀ x : G, conjSubgroup L g ≠ conjSubgroup M x

@[expose]
def FTS_sigma_complement_exists_nontrivial : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M →
      (∃ E : Subgroup G, E ≤ M ∧ E ≠ ⊥ ∧
        FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) ∧
      ∀ E : Subgroup G, E ≤ M → FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
        IsHallOf {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} E M ∧
          (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥E)

@[expose]
def FTS_sigma_core_fusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsMinimalSimpleOddOrder G →
    ∀ M : Subgroup G, IsCoatom M → ∀ x ∈ sigmaCore M, ∀ g : G,
      g⁻¹ * x * g ∈ sigmaCore M → ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m

end Statements

end

end CFSG.FeitThompson
