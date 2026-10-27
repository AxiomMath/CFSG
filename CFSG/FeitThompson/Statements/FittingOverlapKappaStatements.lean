module

public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
public import CFSG.FeitThompson.Local.Omega1CentralizerCommutatorBound
public import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.OddOrder.PairedMaximalSubgroupsSwap

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

structure IsFBGAmbient (G : Type*) [Group G] [Finite G] : Prop where
  odd_natCard : Odd (Nat.card G)
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  isSolvable : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K

@[expose]
def conjSubgroup (Y : Subgroup G) (g : G) : Subgroup G := Y.map (MulAut.conj g⁻¹ : G →* G)

@[expose]
def conjSet (Y : Set G) (g : G) : Set G := (fun y => g⁻¹ * y * g) '' Y

@[expose]
def sharp (Y : Subgroup G) : Set G := (Y : Set G) \ {1}

@[expose]
def sat (Y : Set G) : Set G := ⋃ g : G, conjSet Y g

@[expose]
def hallCoreIn (M : Subgroup G) : Subgroup G := (hallCore M).map M.subtype

@[expose]
def alphaCoreIn [Finite G] (M : Subgroup G) : Subgroup G := (alphaCore M).map M.subtype

@[expose]
def centralizerWithin (X Y : Subgroup G) : Subgroup G := X ⊓ centralizer (Y : Set G)

@[expose]
def centralizerWithinElem (X : Subgroup G) (y : G) : Subgroup G := X ⊓ centralizer {y}

@[expose]
def IsMulCommutativeQuotient (X Y : Subgroup G) : Prop :=
  ∃ h : (Y.subgroupOf X).Normal, letI := h; IsMulCommutative (↥X ⧸ Y.subgroupOf X)

@[expose]
def IsNilpotentQuotient (X Y : Subgroup G) : Prop :=
  ∃ h : (Y.subgroupOf X).Normal, letI := h; Group.IsNilpotent (↥X ⧸ Y.subgroupOf X)

@[expose]
def IsCyclicQuotient (X Y : Subgroup G) : Prop :=
  ∃ h : (Y.subgroupOf X).Normal, letI := h; IsCyclic (↥X ⧸ Y.subgroupOf X)

@[expose]
def IsQuotientMulEquivTo (X Y Z : Subgroup G) : Prop :=
  ∃ h : (Y.subgroupOf X).Normal, letI := h; Nonempty ((↥X ⧸ Y.subgroupOf X) ≃* ↥Z)

@[expose]
def IsSylowSubgroupIn (Q X : Subgroup G) (p : ℕ) : Prop :=
  Q ≤ X ∧ Nat.card ↥Q = p ^ (Nat.card ↥X).factorization p

@[expose]
def IsSylowProduct (Y X : Subgroup G) (π : Set ℕ) : Prop :=
  ∃ Q : ℕ → Subgroup G,
    (∀ p ∈ π, p ∣ Nat.card ↥X → IsSylowSubgroupIn (Q p) X p) ∧
      Y = ⨆ p ∈ {p ∈ π | p ∣ Nat.card ↥X}, Q p

@[expose]
def IsIrreducibleConjAction (U P : Subgroup G) (p : ℕ) : Prop :=
  (∃ d : ℕ, 1 ≤ d ∧ Nonempty (↥P ≃* (Fin d → Multiplicative (ZMod p)))) ∧
    ∀ V : Subgroup G, V ≤ P → U ≤ normalizer (V : Set G) → V = ⊥ ∨ V = P

@[expose]
def localTypes [Finite G] (M : Subgroup G) : Fin 5 → Prop
  | 0 => IsTypeI M
  | 1 => IsTypeII M
  | 2 => IsTypeIII M
  | 3 => IsTypeIV M
  | 4 => IsTypeV M

theorem conjSubgroup_eq (Y : Subgroup G) (g : G) :
    conjSubgroup Y g = Y.map (MulAut.conj g⁻¹ : G →* G) := (rfl)

@[simp]
theorem mem_conjSubgroup {Y : Subgroup G} {g x : G} :
    x ∈ conjSubgroup Y g ↔ ∃ y ∈ Y, g⁻¹ * y * g = x := by
  simp [conjSubgroup, mul_assoc]

@[simp]
theorem conjSubgroup_one (Y : Subgroup G) : conjSubgroup Y 1 = Y := by
  ext x; simp

theorem coe_conjSubgroup (Y : Subgroup G) (g : G) :
    ((conjSubgroup Y g : Subgroup G) : Set G) = conjSet (Y : Set G) g := by
  ext x; simp [conjSet, eq_comm]

theorem conjSet_eq (Y : Set G) (g : G) : conjSet Y g = (fun y => g⁻¹ * y * g) '' Y := (rfl)

@[simp]
theorem mem_conjSet {Y : Set G} {g x : G} : x ∈ conjSet Y g ↔ ∃ y ∈ Y, g⁻¹ * y * g = x := Iff.rfl

@[simp]
theorem conjSet_one (Y : Set G) : conjSet Y 1 = Y := by simp [conjSet]

theorem sharp_eq (Y : Subgroup G) : sharp Y = (Y : Set G) \ {1} := (rfl)

@[simp]
theorem mem_sharp {Y : Subgroup G} {x : G} : x ∈ sharp Y ↔ x ∈ Y ∧ x ≠ 1 := Iff.rfl

@[simp]
theorem one_notMem_sharp (Y : Subgroup G) : (1 : G) ∉ sharp Y := by simp

theorem sharp_nonempty_iff {Y : Subgroup G} : (sharp Y).Nonempty ↔ Y ≠ ⊥ := by
  refine ⟨fun ⟨x, hx, hx1⟩ h => hx1 (by simpa [h] using hx), fun h => ?_⟩
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  exact ⟨(x : G), x.2, fun hc => hx (Subtype.ext hc)⟩

theorem sat_eq (Y : Set G) : sat Y = ⋃ g : G, conjSet Y g := (rfl)

theorem subset_sat (Y : Set G) : Y ⊆ sat Y := fun _ hy =>
  Set.mem_iUnion.2 ⟨1, by rwa [conjSet_one]⟩

theorem mem_sat_iff {Y : Set G} {x : G} : x ∈ sat Y ↔ ∃ g : G, x ∈ conjSet Y g :=
  Set.mem_iUnion

theorem hallCoreIn_eq (M : Subgroup G) : hallCoreIn M = (hallCore M).map M.subtype := (rfl)

theorem hallCoreIn_le (M : Subgroup G) : hallCoreIn M ≤ M := Subgroup.map_subtype_le _

theorem hallCoreSharp_eq_sharp_hallCoreIn (M : Subgroup G) :
    hallCoreSharp M = sharp (hallCoreIn M) := by
  rw [hallCoreSharp_eq, sharp_eq, hallCoreIn_eq]

theorem alphaCoreIn_eq [Finite G] (M : Subgroup G) :
    alphaCoreIn M = (alphaCore M).map M.subtype := (rfl)

theorem alphaCoreIn_le [Finite G] (M : Subgroup G) : alphaCoreIn M ≤ M := Subgroup.map_subtype_le _

theorem centralizerWithin_eq (X Y : Subgroup G) :
    centralizerWithin X Y = X ⊓ centralizer (Y : Set G) := (rfl)

theorem centralizerWithin_le (X Y : Subgroup G) : centralizerWithin X Y ≤ X := inf_le_left

@[simp]
theorem mem_centralizerWithin {X Y : Subgroup G} {x : G} :
    x ∈ centralizerWithin X Y ↔ x ∈ X ∧ ∀ y ∈ Y, y * x = x * y := by
  simp [centralizerWithin, Subgroup.mem_centralizer_iff]

theorem centralizerWithinElem_eq (X : Subgroup G) (y : G) :
    centralizerWithinElem X y = X ⊓ centralizer {y} := (rfl)

theorem centralizerWithinElem_le (X : Subgroup G) (y : G) : centralizerWithinElem X y ≤ X :=
  inf_le_left

theorem centralizerWithinElem_eq_centralizerWithin_closure (X : Subgroup G) (y : G) :
    centralizerWithinElem X y = centralizerWithin X (closure {y}) := by
  rw [centralizerWithinElem_eq, centralizerWithin_eq, Subgroup.centralizer_closure]

theorem isMulCommutativeQuotient_iff {X Y : Subgroup G} (h : (Y.subgroupOf X).Normal) :
    IsMulCommutativeQuotient X Y ↔ _root_.commutator ↥X ≤ Y.subgroupOf X := by
  let _ := h
  exact ⟨fun hq => Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hq.2,
    fun hc => ⟨h, Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hc⟩⟩

theorem isNilpotentQuotient_iff {X Y : Subgroup G} (h : (Y.subgroupOf X).Normal) :
    IsNilpotentQuotient X Y ↔ Group.IsNilpotent (↥X ⧸ Y.subgroupOf X) := by
  let _ := h
  exact ⟨fun hq => hq.2, fun hq => ⟨h, hq⟩⟩

theorem isCyclicQuotient_iff {X Y : Subgroup G} (h : (Y.subgroupOf X).Normal) :
    IsCyclicQuotient X Y ↔ IsCyclic (↥X ⧸ Y.subgroupOf X) := by
  let _ := h
  exact ⟨fun hq => hq.2, fun hq => ⟨h, hq⟩⟩

theorem isQuotientMulEquivTo_iff {X Y Z : Subgroup G} (h : (Y.subgroupOf X).Normal) :
    IsQuotientMulEquivTo X Y Z ↔ Nonempty ((↥X ⧸ Y.subgroupOf X) ≃* ↥Z) := by
  let _ := h
  exact ⟨fun hq => hq.2, fun hq => ⟨h, hq⟩⟩

theorem IsCyclicQuotient.normal {X Y : Subgroup G} (h : IsCyclicQuotient X Y) :
    (Y.subgroupOf X).Normal := h.1

theorem IsCyclicQuotient.isMulCommutativeQuotient {X Y : Subgroup G} (h : IsCyclicQuotient X Y) :
    IsMulCommutativeQuotient X Y := by
  obtain ⟨hn, hc⟩ := h
  let _ := hn
  let _ := hc
  exact ⟨hn, IsCyclic.isMulCommutative⟩

theorem IsMulCommutativeQuotient.isNilpotentQuotient {X Y : Subgroup G}
    (h : IsMulCommutativeQuotient X Y) : IsNilpotentQuotient X Y := by
  obtain ⟨hn, hc⟩ := h
  let _ := hn
  exact ⟨hn, 1, by rw [_root_.upperCentralSeries_one]; exact Subgroup.center_eq_top_iff.2 hc⟩

theorem isSylowSubgroupIn_iff {Q X : Subgroup G} {p : ℕ} :
    IsSylowSubgroupIn Q X p ↔ Q ≤ X ∧ Nat.card ↥Q = p ^ (Nat.card ↥X).factorization p := Iff.rfl

theorem IsSylowSubgroupIn.le {Q X : Subgroup G} {p : ℕ} (h : IsSylowSubgroupIn Q X p) : Q ≤ X :=
  h.1

theorem isSylowProduct_iff {Y X : Subgroup G} {π : Set ℕ} :
    IsSylowProduct Y X π ↔ ∃ Q : ℕ → Subgroup G,
      (∀ p ∈ π, p ∣ Nat.card ↥X → IsSylowSubgroupIn (Q p) X p) ∧
        Y = ⨆ p ∈ {p ∈ π | p ∣ Nat.card ↥X}, Q p := Iff.rfl

theorem isSylowProduct_bot_of_forall_not_dvd {X : Subgroup G} {π : Set ℕ}
    (h : ∀ p ∈ π, ¬ p ∣ Nat.card ↥X) : IsSylowProduct ⊥ X π := by
  refine ⟨fun _ => ⊥, fun p hp hdvd => absurd hdvd (h p hp), ?_⟩
  have : {p ∈ π | p ∣ Nat.card ↥X} = (∅ : Set ℕ) := by
    ext p
    exact ⟨fun hp => absurd hp.2 (h p hp.1), fun hp => hp.elim⟩
  simp [this]

theorem isIrreducibleConjAction_iff {U P : Subgroup G} {p : ℕ} :
    IsIrreducibleConjAction U P p ↔
      (∃ d : ℕ, 1 ≤ d ∧ Nonempty (↥P ≃* (Fin d → Multiplicative (ZMod p)))) ∧
        ∀ V : Subgroup G, V ≤ P → U ≤ normalizer (V : Set G) → V = ⊥ ∨ V = P := Iff.rfl

theorem IsIrreducibleConjAction.isMulCommutative {U P : Subgroup G} {p : ℕ}
    (h : IsIrreducibleConjAction U P p) : IsMulCommutative ↥P := by
  obtain ⟨⟨d, -, ⟨e⟩⟩, -⟩ := h
  exact ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

@[simp] theorem localTypes_zero [Finite G] (M : Subgroup G) : localTypes M 0 = IsTypeI M := rfl
@[simp] theorem localTypes_one [Finite G] (M : Subgroup G) : localTypes M 1 = IsTypeII M := rfl
@[simp] theorem localTypes_two [Finite G] (M : Subgroup G) : localTypes M 2 = IsTypeIII M := rfl
@[simp] theorem localTypes_three [Finite G] (M : Subgroup G) : localTypes M 3 = IsTypeIV M := rfl
@[simp] theorem localTypes_four [Finite G] (M : Subgroup G) : localTypes M 4 = IsTypeV M := rfl

structure IsAbelianAmbientSetup [Finite G] (M : Subgroup G) (p : ℕ) (A E P : Subgroup G) :
    Prop where
  isCoatom : IsCoatom M
  prime : p.Prime
  notMem_sigmaPrimes : p ∉ sigmaPrimes M
  le_M_A : A ≤ M
  plane : Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p)))
  le_M_E : E ≤ M
  semidirect : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E
  le_E_A : A ≤ E
  isMulCommutative_P : IsMulCommutative ↥P
  isSylow_P : ∃ Q : Sylow p G, (Q : Subgroup G) = P
  le_P_A : A ≤ P

structure IsTauHallDecomposition (M E E₁ E₂ E₃ K : Subgroup G) : Prop where
  le_E_E₁ : E₁ ≤ E
  le_E_E₂ : E₂ ≤ E
  le_E_E₃ : E₃ ≤ E
  hall_E₁ : IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E)
  hall_E₂ : IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf E)
  hall_E₃ : IsHallPiSubgroup (tau3Primes M) (E₃.subgroupOf E)
  semidirect_outer : FreeCore.IsInternalSemidirectProduct E E₃ (E₂ ⊔ E₁)
  semidirect_inner : FreeCore.IsInternalSemidirectProduct (E₂ ⊔ E₁) E₂ E₁
  K_eq : K = E₂ ⊔ E₃

structure IsLocalKappaSetup [Finite G] (M K U : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  le_M_K : K ≤ M
  hall_K : IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M)
  le_M_U : U ≤ M
  le_normalizer_U : K ≤ normalizer (U : Set G)
  semidirect_M : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K)
  semidirect_UK : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K

structure IsKappaResidualSetup [Finite G] (M K U : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  kappaPrimes_nonempty : (kappaPrimes M).Nonempty
  le_M_K : K ≤ M
  hall_K : IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M)
  le_M_U : U ≤ M
  ne_bot_U : U ≠ ⊥
  semidirect_M : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K)
  semidirect_UK : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K

structure IsFittingOverlapSetup [Finite G] (M X : Subgroup G) (g : G) : Prop where
  isCoatom : IsCoatom M
  notMem : g ∉ M
  eq : X = mixedFitting M ⊓ conjSubgroup (mixedFitting M) g
  ne_bot : X ≠ ⊥

structure IsNonconjugateSetup [Finite G] (M L E : Subgroup G) (p : ℕ) : Prop where
  isCoatom_M : IsCoatom M
  isCoatom_L : IsCoatom L
  nonconj : ∀ g : G, L ≠ conjSubgroup M g
  le_M_E : E ≤ M
  semidirect : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E
  prime : p.Prime
  dvd_natCard_E : p ∣ Nat.card ↥E
  dvd_natCard_L : p ∣ Nat.card ↥L

structure IsOppositeSupportingSetup [Finite G] (S T U V W₁ W₂ : Subgroup G) (p q : ℕ) :
    Prop where
  isCoatom_S : IsCoatom S
  isCoatom_T : IsCoatom T
  ne : S ≠ T
  pconfig_S : IsWitnessedPConfiguration S U W₁ W₂
  pconfig_T : IsWitnessedPConfiguration T V W₂ W₁
  natCard_W₂ : Nat.card ↥W₂ = p
  natCard_W₁ : Nat.card ↥W₁ = q
  prime_p : p.Prime
  prime_q : q.Prime
  odd_p : Odd p
  odd_q : Odd q
  lt : q < p
  irreducible : IsIrreducibleConjAction U (hallCoreIn S) p

structure IsOppositeSupportingPair [Finite G] (S T U V W₁ W₂ : Subgroup G) (p q : ℕ) :
    Prop where
  base : IsOppositeSupportingSetup S T U V W₁ W₂ p q
  isTypeII_S : IsTypeII S
  isTypeII_T : IsTypeII T
  isCyclic_sup : IsCyclic (W₁ ⊔ W₂ : Subgroup G)
  inf_eq : S ⊓ T = W₁ ⊔ W₂
  conj_of_not_isTypeI : ∀ N : Subgroup G, IsCoatom N → ¬ IsTypeI N →
    (∃ g : G, conjSubgroup N g = S) ∨ (∃ g : G, conjSubgroup N g = T)

theorem IsAbelianAmbientSetup.ne_top [Finite G] {M : Subgroup G} {p : ℕ} {A E P : Subgroup G}
    (h : IsAbelianAmbientSetup M p A E P) : M ≠ ⊤ := h.isCoatom.1

theorem IsLocalKappaSetup.ne_top [Finite G] {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) :
    M ≠ ⊤ := h.isCoatom.1

theorem IsKappaResidualSetup.isLocalKappaSetup [Finite G] {M K U : Subgroup G}
    (h : IsKappaResidualSetup M K U) : IsLocalKappaSetup M K U where
  isCoatom := h.isCoatom
  le_M_K := h.le_M_K
  hall_K := h.hall_K
  le_M_U := h.le_M_U
  le_normalizer_U := h.semidirect_UK.right_le_normalizer
  semidirect_M := h.semidirect_M
  semidirect_UK := h.semidirect_UK

theorem IsFittingOverlapSetup.le [Finite G] {M X : Subgroup G} {g : G}
    (h : IsFittingOverlapSetup M X g) : X ≤ mixedFitting M := h.eq ▸ inf_le_left

theorem IsOppositeSupportingPair.ne [Finite G] {S T U V W₁ W₂ : Subgroup G} {p q : ℕ}
    (h : IsOppositeSupportingPair S T U V W₁ W₂ p q) : S ≠ T := h.base.ne

namespace Statements

universe u

@[expose]
def FBG_abelian_ambient_characteristic_chain : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M : Subgroup G) (p : ℕ) (A E P E₁ E₂ E₃ K : Subgroup G),
      IsAbelianAmbientSetup M p A E P → IsTauHallDecomposition M E E₁ E₂ E₃ K →
        IsCyclic ↥E₁ ∧ IsCyclic ↥E₃ ∧ IsMulCommutative ↥K ∧ (K.subgroupOf E).Normal ∧
          K ≤ centreIn (mixedFitting E) ∧ A ≤ P ∧ P ≤ E₂ ∧ E₂ ≤ K ∧ K ≤ mixedFitting E ∧
          (A.subgroupOf P).Characteristic ∧ (P.subgroupOf E₂).Characteristic ∧
          (E₂.subgroupOf K).Characteristic ∧ (K.subgroupOf (mixedFitting E)).Characteristic

@[expose]
def FBG_abelian_ambient_normalizer_chain : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M : Subgroup G) (p : ℕ) (A E P E₁ E₂ E₃ K : Subgroup G),
      IsAbelianAmbientSetup M p A E P → IsTauHallDecomposition M E E₁ E₂ E₃ K →
        normalizer (A : Set G) = normalizer (P : Set G) ∧
          normalizer (P : Set G) = normalizer (E₂ : Set G) ∧
          normalizer (E₂ : Set G) = normalizer (K : Set G) ∧
          normalizer (K : Set G) = normalizer ((mixedFitting E : Subgroup G) : Set G) ∧
          E ≤ normalizer (A : Set G) ∧
          (K.subgroupOf (normalizer (A : Set G))).Normal ∧
          ⁅normalizer (A : Set G), normalizer (A : Set G)⁆ ≤ centralizer (K : Set G)

@[expose]
def FBG_abelian_ambient_normalizer_fixed_displacement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M : Subgroup G) (p : ℕ) (A E P : Subgroup G), IsAbelianAmbientSetup M p A E P →
      ∀ X : Subgroup G, X ≤ normalizer (P : Set G) →
        ((centralizerWithin P X).subgroupOf (normalizer (P : Set G))).Normal ∧
          ((⁅P, X⁆ : Subgroup G).subgroupOf (normalizer (P : Set G))).Normal

@[expose]
def FBG_abelian_ambient_regular_first_factor_central : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M : Subgroup G) (p : ℕ) (A E P E₁ E₂ E₃ K : Subgroup G),
      IsAbelianAmbientSetup M p A E P → IsTauHallDecomposition M E E₁ E₂ E₃ K →
        ∀ q : ℕ, q.Prime → ∀ X : Subgroup G, X ≤ E₁ → Nat.card ↥X = q →
          centralizerWithin (sigmaCore M) X = ⊥ → X ≤ centreIn E

@[expose]
def FBG_abelian_ambient_tau_two_fitting : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M : Subgroup G) (p : ℕ) (A E P : Subgroup G), IsAbelianAmbientSetup M p A E P →
      P ≤ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ∧
        ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ≤ mixedFitting E ∧
        mixedFitting E ≤ centralizer (P : Set G) ∧
        (centralizer (P : Set G) : Subgroup G) ≤ E ∧
        mixedFitting (normalizer (A : Set G)) = mixedFitting E ∧
        P ≤ centreIn (mixedFitting E)

@[expose]
def FBG_abelian_fitting_overlap_rank_two : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M X : Subgroup G) (g : G), IsFittingOverlapSetup M X g →
      IsMulCommutative ↥(hallCoreIn M) →
        maxElementaryAbelianPRank ↥(hallCoreIn M) = 2 ∧ kappaPrimes M = ∅

@[expose]
def FBG_beta_normal_prime_centralizer_position : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M : Subgroup G, IsCoatom M → ∀ P : Subgroup G, P ≤ M → P ≠ ⊥ →
      centralizerWithin (betaCore M) P ≠ ⊥ →
      ∀ H : Subgroup G, H ≤ centralizer (P : Set G) → centralizerWithin (betaCore M) P ≤ H →
      ∀ s ∈ betaPrimes ↥M, s.Prime →
      ∀ X : Subgroup G, X ≤ H → (X.subgroupOf H).Normal → X ≠ ⊥ →
        (∃ n : ℕ, Nat.card ↥X = s ^ n) → H ≤ M ∧ X ≤ betaCore M

@[expose]
def FBG_common_sylow_normalizer_beta_factor : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
      ∀ q : ℕ, q.Prime → ∀ Q : Sylow q G,
        normalizer ((Q : Subgroup G) : Set G) ≤ M ⊓ T →
          (M : Set G) = (betaCore M : Set G) * ((M ⊓ T : Subgroup G) : Set G) ∧
            alphaPrimes ↥M = betaPrimes ↥M ∧ alphaCoreIn M = betaCore M ∧ betaCore M ≠ ⊥

@[expose]
def FBG_common_sylow_normalizer_tau_one_transfer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M T : Subgroup G, IsCoatom M → IsCoatom T → M ≠ T →
      ∀ q : ℕ, q.Prime → ∀ Q : Sylow q G,
        normalizer ((Q : Subgroup G) : Set G) ≤ M ⊓ T →
          tau1Primes T ⊆ tau1Primes M ∪ alphaPrimes ↥M

@[expose]
def FBG_field_p_configuration_prime_support : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (S U W₁ W₂ : Subgroup G) (p : ℕ), IsCoatom S → IsWitnessedPConfiguration S U W₁ W₂ →
      Nat.card ↥W₂ = p → p.Prime → IsIrreducibleConjAction U (hallCoreIn S) p →
      ∀ g : G, g ∉ sat (sharp (hallCoreIn S)) → g ∉ sat (sharp (W₁ ⊔ W₂)) →
        Nat.Coprime (orderOf g) p

@[expose]
def FBG_fitting_overlap_prime_centralizer_small : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M X : Subgroup G) (g : G), IsFittingOverlapSetup M X g →
      ∀ p : ℕ, p.Prime → ∀ L : Subgroup G, L ≤ X → Nat.card ↥L = p →
        centralizerWithin (hallCoreIn M) L ≠ ⊥ ∧
          IsMulCommutative ↥(centralizerWithin (hallCoreIn M) L) ∧
          maxElementaryAbelianPRank ↥(centralizerWithin (hallCoreIn M) L) ≤ 2 ∧
          (¬ ∃ N : Subgroup G, IsUniqueMaximalOvergroup (centralizerWithin (hallCoreIn M) L) N) ∧
          ¬ (centralizer (L : Set G) : Subgroup G) ≤ M

@[expose]
def FBG_five_type_local_classification : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    (∀ M : Subgroup G, IsCoatom M → ∃! i : Fin 5, localTypes M i) ∧
      ∀ M K U : Subgroup G, IsLocalKappaSetup M K U →
        (IsTypeI M ↔ K = ⊥) ∧ (IsTypeII M ↔ K ≠ ⊥ ∧ U ≠ ⊥) ∧
          (K ≠ ⊥ → U = ⊥ →
            (IsTypeV M ↔ hallCoreIn M = sigmaCore M) ∧
              (hallCoreIn M ≠ sigmaCore M →
                (IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M) → IsTypeIII M) ∧
                (¬ IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M) → IsTypeIV M)))

@[expose]
def FBG_kappa_complement_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M : Subgroup G, IsCoatom M →
      ∃ K U : Subgroup G, K ≤ M ∧ IsCyclic ↥K ∧
        IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M) ∧ U ≤ M ∧
        FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K) ∧
        FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K ∧
        (∀ k ∈ K, k ≠ 1 → centralizerWithinElem U k = ⊥) ∧
        (K ≠ ⊥ → IsMulCommutative ↥U ∧ ¬ normalizer (U : Set G) ≤ M ∧
          (∀ k ∈ K, k ≠ 1 →
            centralizerWithinElem (sigmaCore M) k = centralizerWithin (sigmaCore M) K) ∧
          centralizerWithin (sigmaCore M) K ≠ ⊥)

@[expose]
def FBG_kappa_fixed_subgroup_derived_and_hall : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K : Subgroup G, IsCoatom M → K ≠ ⊥ → K ≤ M →
      IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M) →
        centralizerWithin (sigmaCore M) K ≠ ⊥ ∧
          IsCyclic ↥(centralizerWithin (sigmaCore M) K) ∧
          centralizerWithin (sigmaCore M) K ≤
            hallCoreIn M ⊓ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ∧
          ∀ k ∈ K, k ≠ 1 → centralizerWithinElem (⁅M, M⁆ : Subgroup G) k =
            centralizerWithin (sigmaCore M) K

@[expose]
def FBG_kappa_nontrivial_complement_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsKappaResidualSetup M K U →
      (Nat.card ↥K).Prime ∧ sigmaPrimes M = betaPrimes ↥M ∧
        Group.IsNilpotent ↥(sigmaCore M) ∧
        normalizer (sharp (sigmaCore M)) = M ∧
        ∀ g : G, g ∉ M → sharp (sigmaCore M) ∩ conjSet (sharp (sigmaCore M)) g = ∅

@[expose]
def FBG_kappa_residual_beta_equality : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsKappaResidualSetup M K U → sigmaPrimes M = betaPrimes ↥M

@[expose]
def FBG_kappa_residual_fixed_space_and_prime_order : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsKappaResidualSetup M K U →
      (Nat.card ↥K).Prime ∧ Group.IsNilpotent ↥(sigmaCore M) ∧
        ∃ V : Subgroup G, V ≠ ⊥ ∧ IsMulCommutative ↥V ∧ V ≤ M ∧
          IsHallPiSubgroup {r : ℕ | r.Prime ∧ r ∉ sigmaPrimes M ∪ kappaPrimes M}
            (V.subgroupOf M) ∧
          FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (V ⊔ K) ∧
          FreeCore.IsInternalSemidirectProduct (V ⊔ K) V K ∧
          centralizerWithin (sigmaCore M) V = ⊥ ∧
          (∀ k ∈ K, k ≠ 1 → centralizerWithinElem V k = ⊥) ∧
          V = ⁅V, K⁆ ∧ V ≤ ⁅(V ⊔ K : Subgroup G), (V ⊔ K : Subgroup G)⁆

@[expose]
def FBG_local_inertia_and_exponent_complement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsLocalKappaSetup M K U → U ≠ ⊥ →
      hallCoreIn M = sigmaCore M ∧
        ∃ U₁ U₀ : Subgroup G, U₁ ≤ U ∧ U₀ ≤ U ∧ IsMulCommutative ↥U₁ ∧
          (U₁.subgroupOf U).Normal ∧
          (∀ h ∈ hallCoreIn M, h ≠ 1 → centralizerWithinElem U h ≤ U₁) ∧
          Monoid.exponent ↥U₀ = Monoid.exponent ↥U ∧
          ∀ x ∈ U₀, x ≠ 1 → centralizerWithinElem (hallCoreIn M) x = ⊥

@[expose]
def FBG_local_nilpotent_hall_core : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsLocalKappaSetup M K U →
      (⊥ < hallCoreIn M ∧ hallCoreIn M ≤ sigmaCore M ∧ sigmaCore M ≤ ⁅M, M⁆ ∧
          IsNilpotentQuotient (⁅M, M⁆ : Subgroup G) (hallCoreIn M) ∧
          ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ mixedFitting M ∧
          ((mixedFitting M : Set G) = (hallCoreIn M : Set G) *
            ((centralizerWithin M (hallCoreIn M) : Subgroup G) : Set G)) ∧
          (K ≠ ⊥ → mixedFitting M ≤ ⁅M, M⁆)) ∧
        (hallCoreIn M ≠ sigmaCore M →
          U = ⊥ ∧ (Nat.card ↥K).Prime ∧ IsTIWithNormalizer (sharp (mixedFitting M)) M)

@[expose]
def FBG_local_p_core_centralizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsLocalKappaSetup M K U → K ≠ ⊥ →
      centralizerWithin (sigmaCore M) K ≠ ⊥ ∧
        IsCyclic ↥(centralizerWithin (sigmaCore M) K) ∧
        centralizerWithin (sigmaCore M) K ≤
          hallCoreIn M ⊓ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ∧
        ¬ IsCyclic ↥(hallCoreIn M) ∧
        ((⁅M, M⁆ : Subgroup G) : Set G) = (sigmaCore M : Set G) * (U : Set G) ∧
        ∀ k ∈ K, k ≠ 1 → centralizerWithinElem (⁅M, M⁆ : Subgroup G) k =
          centralizerWithin (sigmaCore M) K

@[expose]
def FBG_local_p_nontrivial_U_case : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsLocalKappaSetup M K U → K ≠ ⊥ → U ≠ ⊥ →
      (Nat.card ↥K).Prime ∧ IsTIWithNormalizer (sharp (mixedFitting M)) M ∧
        hallCoreIn (⁅M, M⁆ : Subgroup G) = hallCoreIn M ∧ hallCoreIn M = sigmaCore M

@[expose]
def FBG_local_p_trivial_U_alternative : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsLocalKappaSetup M K U → K ≠ ⊥ → U = ⊥ →
      hallCoreIn M = sigmaCore M →
        IsTIWithNormalizer (sharp (hallCoreIn M)) M ∨
          (∃ r ∈ (Nat.card ↥(hallCoreIn M)).primeFactors,
            IsCyclic ↥(pComplCoreIn r (hallCoreIn M)) ∧ Nat.card ↥K ∣ r - 1) ∨
          (∃ r ∈ (Nat.card ↥(hallCoreIn M)).primeFactors,
            IsCyclic ↥(pComplCoreIn r (hallCoreIn M)) ∧
              Nat.card ↥(pCoreIn r (hallCoreIn M)) = r ^ 3 ∧ Nat.card ↥K ∣ r + 1)

@[expose]
def FBG_local_type_I_alternative : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M K U : Subgroup G, IsLocalKappaSetup M K U → K = ⊥ →
      IsTIWithNormalizer (sharp (hallCoreIn M)) M ∨
        (IsMulCommutative ↥(hallCoreIn M) ∧ maxElementaryAbelianPRank ↥(hallCoreIn M) = 2) ∨
        ((∀ r ∈ (Nat.card ↥(hallCoreIn M)).primeFactors, Monoid.exponent ↥U ∣ r - 1) ∧
          ∃ r ∈ (Nat.card ↥(hallCoreIn M)).primeFactors,
            IsCyclic ↥(pComplCoreIn r (hallCoreIn M)))

@[expose]
def FBG_maximal_type_dichotomy : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    (∀ M : Subgroup G, IsCoatom M → ∃! i : Fin 5, localTypes M i) ∧
      ((∀ M : Subgroup G, IsCoatom M → IsTypeI M) ∨
        ∃ S T W₁ W₂ : Subgroup G, IsTypePPair S T W₁ W₂)

@[expose]
def FBG_nilpotent_sigma_core_fitting_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M : Subgroup G, IsCoatom M → Group.IsNilpotent ↥(sigmaCore M) →
      ∀ Y : Subgroup G,
        IsSylowProduct Y (mixedFitting M) {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} →
          hallCoreIn M = sigmaCore M ∧ sigmaCore M ≠ ⊥ ∧ IsCyclic ↥Y ∧
            ((Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tauTwoPrimes M ∧
            IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y ∧
            ((mixedFitting M : Set G) = (sigmaCore M : Set G) *
              ((centralizerWithin M (sigmaCore M) : Subgroup G) : Set G)) ∧
            hallCoreIn M ≤ ⁅M, M⁆ ∧
            IsMulCommutativeQuotient (⁅M, M⁆ : Subgroup G) (hallCoreIn M) ∧
            ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ sigmaCore M

@[expose]
def FBG_nonabelian_fitting_overlap_central_lines : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M X : Subgroup G) (g : G), IsFittingOverlapSetup M X g →
      ¬ IsMulCommutative ↥(hallCoreIn M) →
        (Nat.card ↥X).Prime ∧
          IsCyclic ↥(pComplCoreIn (Nat.card ↥X) (hallCoreIn M)) ∧
          ∀ q ∈ (Nat.card ↥(hallCoreIn M)).primeFactors, ∃ Z₀ : Subgroup G,
            (Z₀ : Set G) = pTorsionSet q (centreIn (pCoreIn q (hallCoreIn M))) ∧
              (Z₀.subgroupOf (hallCoreIn M)).Characteristic ∧ Nat.card ↥Z₀ = q

@[expose]
def FBG_nonabelian_fitting_overlap_maximal_plane : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M X : Subgroup G) (g : G), IsFittingOverlapSetup M X g →
      ¬ IsMulCommutative ↥(hallCoreIn M) →
      ∀ p ∈ (Nat.card ↥X).primeFactors, ∀ L : Subgroup G, L ≤ X → Nat.card ↥L = p →
        ¬ IsMulCommutative ↥(pCoreIn p (hallCoreIn M)) ∧
          (∃ Q : Sylow p G, (Q : Subgroup G) = pCoreIn p (hallCoreIn M)) ∧
          (∃ Z₀ : Subgroup G,
            (Z₀ : Set G) = pTorsionSet p (centreIn (pCoreIn p (hallCoreIn M))) ∧
              (Z₀.subgroupOf (pCoreIn p (hallCoreIn M))).Characteristic ∧
              Nat.card ↥Z₀ = p ∧
              ∃ A : Subgroup G, IsInternalDirectProduct A L Z₀ ∧ IsElementaryAbelian p A ∧
                Nat.card ↥A = p ^ 2 ∧ Maximal (IsElementaryAbelian p) A) ∧
          X = L ∧ Nat.card ↥X = p

@[expose]
def FBG_nonabelian_fitting_overlap_primary : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M X : Subgroup G) (g : G), IsFittingOverlapSetup M X g →
      ¬ IsMulCommutative ↥(hallCoreIn M) →
      ∀ p ∈ (Nat.card ↥X).primeFactors,
        IsCyclic ↥X ∧ IsPGroup p ↥X ∧ X ≤ pCoreIn p (hallCoreIn M) ∧
          ¬ IsMulCommutative ↥(pCoreIn p (hallCoreIn M)) ∧
          IsMulCommutative ↥(pComplCoreIn p (hallCoreIn M)) ∧
          IsInternalDirectProduct (hallCoreIn M) (pCoreIn p (hallCoreIn M))
            (pComplCoreIn p (hallCoreIn M)) ∧
          ∀ L : Subgroup G, L ≤ X → Nat.card ↥L = p →
            ¬ L ≤ centreIn (pCoreIn p (hallCoreIn M))

@[expose]
def FBG_nonconjugate_derived_prime_intersection_centralization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M L E : Subgroup G) (p : ℕ), IsNonconjugateSetup M L E p →
      (p ∈ sigmaPrimes L ∨ p ∈ tau3Primes L) →
      ∀ P : Subgroup G, P ≤ M ⊓ L → IsPGroup p ↥P →
        P ≤ centralizer ((sigmaCore M ⊓ L : Subgroup G) : Set G)

@[expose]
def FBG_nonconjugate_intersection_excludes_tau_two : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M L E : Subgroup G) (p : ℕ), IsNonconjugateSetup M L E p →
      ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ ≠ ⊥ → p ∉ tauTwoPrimes L

@[expose]
def FBG_nonconjugate_intersection_prime_centralization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M L E : Subgroup G) (p : ℕ), IsNonconjugateSetup M L E p → p ∉ tau1Primes L →
      ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ ≠ ⊥ →
      ∀ P : Subgroup G, P ≤ M ⊓ L → IsPGroup p ↥P →
        ⁅P, (sigmaCore M ⊓ L : Subgroup G)⁆ = ⊥

@[expose]
def FBG_nonnilpotent_sigma_core_hall_structure : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M : Subgroup G, IsCoatom M → ¬ Group.IsNilpotent ↥(sigmaCore M) →
      (kappaPrimes M).Nonempty ∧
        (∀ K : Subgroup G, K ≤ M → IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M) →
          FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K ∧ (Nat.card ↥K).Prime ∧
            (Nat.card ↥(centralizerWithin (sigmaCore M) K)).Prime) ∧
        ⊥ < hallCoreIn M ∧ hallCoreIn M < sigmaCore M ∧ sigmaCore M = ⁅M, M⁆ ∧
        IsNilpotentQuotient (⁅M, M⁆ : Subgroup G) (hallCoreIn M) ∧
        ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ mixedFitting M ∧
        ((mixedFitting M : Set G) = (hallCoreIn M : Set G) *
          ((centralizerWithin M (hallCoreIn M) : Subgroup G) : Set G)) ∧
        mixedFitting M < ⁅M, M⁆ ∧
        normalizer (sharp (mixedFitting M)) = M ∧
        ∀ g : G, g ∉ M → sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g = ∅

@[expose]
def FBG_nonti_fitting_cyclic_complement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M : Subgroup G) (g : G), IsCoatom M → g ∉ M →
      mixedFitting M ⊓ conjSubgroup (mixedFitting M) g ≠ ⊥ →
        tau3Primes M = ∅ ∧
          ∀ E : Subgroup G, E ≤ M → FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
            (∀ E₂ : Subgroup G, E₂ ≤ E → IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf E) →
              (E₂.subgroupOf E).Normal ∧ IsCyclicQuotient E E₂ ∧
                ∀ E₁ : Subgroup G, E₁ ≤ E →
                  IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E) →
                  FreeCore.IsInternalSemidirectProduct E E₂ E₁ ∧
                    IsQuotientMulEquivTo E E₂ E₁) ∧
            (tauTwoPrimes M = ∅ → IsCyclic ↥E) ∧
            (∀ E₃ : Subgroup G, E₃ ≤ E →
              IsHallPiSubgroup (tau3Primes M) (E₃.subgroupOf E) → E₃ = ⊥)

@[expose]
def FBG_nonti_fitting_nilpotent_core_and_beta_exclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (M X : Subgroup G) (g : G), IsFittingOverlapSetup M X g →
      ∀ Y : Subgroup G,
        IsSylowProduct Y (mixedFitting M) {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} →
          Group.IsNilpotent ↥(sigmaCore M) ∧ hallCoreIn M = sigmaCore M ∧
            X ≤ sigmaCore M ∧ betaPrimes ↥M = ∅ ∧ (⁅M, M⁆ : Subgroup G) ≤ mixedFitting M ∧
            IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y ∧ IsCyclic ↥Y ∧
            ((Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tauTwoPrimes M

@[expose]
def FBG_normal_beta_sylow_fitting_ti : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M : Subgroup G, IsCoatom M → ∀ q ∈ betaPrimes ↥M, q.Prime →
      ∀ Q : Sylow q ↥M, (Q : Subgroup ↥M).Normal → mixedFitting M ≤ sigmaCore M →
        normalizer (sharp (mixedFitting M)) = M ∧
          ∀ g : G, g ∉ M → sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g = ∅

@[expose]
def FBG_normal_hall_core_sigma_containment : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ M : Subgroup G, IsCoatom M →
      hallCoreIn M ≤ sigmaCore M ∧
        (hallCoreIn M = sigmaCore M ↔ Group.IsNilpotent ↥(sigmaCore M))

@[expose]
def FBG_opposite_supporting_kernel_equality : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (S T U V W₁ W₂ : Subgroup G) (p q : ℕ),
      IsOppositeSupportingPair S T U V W₁ W₂ p q →
      ∀ M : Subgroup G, IsCoatom M → normalizer (V : Set G) ≤ M →
        IsTypeI M ∧ hallCoreIn M = V ∧ (hallCoreIn M).relIndex M = p * q ∧
          ∃ y ∈ hallCoreIn S,
            FreeCore.IsInternalSemidirectProduct M V (W₂ ⊔ conjSubgroup W₁ y) ∧
              ∀ w ∈ (W₂ ⊔ conjSubgroup W₁ y : Subgroup G), w ≠ 1 →
                centralizerWithinElem V w = ⊥

@[expose]
def FBG_opposite_supporting_kernel_growth : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (S T U V W₁ W₂ : Subgroup G) (p q : ℕ),
      IsOppositeSupportingPair S T U V W₁ W₂ p q →
      ∀ M : Subgroup G, IsCoatom M → normalizer (V : Set G) ≤ M →
        IsTypeI M ∧ V ≤ hallCoreIn M ∧
          ((hallCoreIn M).relIndex M = p ∨ (hallCoreIn M).relIndex M = p * q) ∧
          W₂ ≤ normalizer ((hallCoreIn M : Subgroup G) : Set G) ∧
          W₂ ≤ normalizer (V : Set G) ∧
          (∀ w ∈ W₂, w ≠ 1 → centralizerWithinElem (hallCoreIn M) w = ⊥) ∧
          (V < hallCoreIn M →
            2 * p * Nat.card ↥V < Nat.card ↥(hallCoreIn M) ∧
              ((Nat.card ↥U : ℚ) - 1) / (q : ℚ) < ((Nat.card ↥V : ℚ) - 1) / (p : ℚ) ∧
              ((Nat.card ↥V : ℚ) - 1) / (p : ℚ) <
                ((Nat.card ↥(hallCoreIn M) : ℚ) - 1) / ((hallCoreIn M).relIndex M : ℚ))

@[expose]
def FBG_opposite_supporting_kernel_norm_bound : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (S T U V W₁ W₂ : Subgroup G) (p q : ℕ),
      IsOppositeSupportingPair S T U V W₁ W₂ p q →
      ∀ M : Subgroup G, IsCoatom M → normalizer (V : Set G) ≤ M →
        V < hallCoreIn M →
          1 / (p : ℚ) + 1 / (q : ℚ) ≤
            ((p : ℚ) * q) / (Nat.card ↥(hallCoreIn M) : ℚ) + 2 / ((p : ℚ) * q) +
              1 / ((Nat.card ↥U : ℚ) * q) + 1 / ((Nat.card ↥V : ℚ) * p)

@[expose]
def FBG_ordered_field_pair_order_estimates : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsFBGAmbient G →
    ∀ (S T U V W₁ W₂ : Subgroup G) (p q : ℕ),
      IsOppositeSupportingSetup S T U V W₁ W₂ p q →
        IsIrreducibleConjAction V (hallCoreIn T) q ∧
          1 < Nat.card ↥U ∧
          (Nat.card ↥U : ℚ) ≤ ((p : ℚ) ^ q - 1) / ((p : ℚ) - 1) ∧
          (Nat.card ↥V : ℚ) = ((q : ℚ) ^ p - 1) / ((q : ℚ) - 1) ∧
          2 * q < Nat.card ↥U ∧ 2 * p < Nat.card ↥V ∧
          p * q ∣ Nat.card ↥V - 1 ∧
          ((Nat.card ↥U : ℚ) - 1) / (q : ℚ) < ((Nat.card ↥V : ℚ) - 1) / (p : ℚ) ∧
          p * q + 1 ≤ Nat.card ↥V

end Statements

end

end CFSG.FeitThompson
