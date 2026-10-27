module

public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def oddCoreOf (H : Subgroup G) : Subgroup G :=
  (classicalInvolutionOddCore ↥H).map H.subtype

@[expose] def RSet (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {R | ∃ J ∈ Ω, ∃ P : Sylow 2 ↥J, R = Subgroup.map J.subtype (P : Subgroup ↥J)}

@[expose] def USet (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {U | ∃ R ∈ RSet Ω, U ≤ R ∧ IsCyclic ↥U ∧ U.relIndex R = 2}

@[expose] def omegaNbr (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ J ≠ K ∧ ∃ R ∈ RSet Ω, R ≤ J ∧ R ≤ Subgroup.normalizer (K : Set G)}

@[expose] def omegaStarNbr (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ J ≠ K ∧ ∃ U ∈ USet Ω, U ≤ J ∧ U ≤ Subgroup.normalizer (K : Set G)}

@[expose] def KPerp (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  insert K (omegaNbr Ω K)

@[expose] def twinSet (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ ∃ z : G, IsUniqueInvolution K z ∧ IsUniqueInvolution J z}

@[expose] def dstarAdj (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  J ∈ Ω ∧ (J ∈ omegaStarNbr Ω K ∨ K ∈ omegaStarNbr Ω J)

@[expose] def dstarComp (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | Relation.ReflTransGen (dstarAdj Ω) K J}

@[expose] def pairNormalizers (K J : Subgroup G) (zK zJ : G) : Subgroup G :=
  (K ⊓ Subgroup.normalizer ((Subgroup.closure {zK, zJ} : Subgroup G) : Set G)) ⊔
    (J ⊓ Subgroup.normalizer ((Subgroup.closure {zK, zJ} : Subgroup G) : Set G))

@[expose] def AEmpty (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop :=
  ∀ J ∈ omegaStarNbr Ω K, J ∉ omegaNbr Ω K → ∀ zK zJ : G, IsUniqueInvolution K zK →
    IsUniqueInvolution J zJ → ∃ g ∈ pairNormalizers K J zK zJ, conjSub g K = J

@[expose] def InDistinctMembers (Ω : Set (Subgroup G)) (η : Set (Subgroup G)) : Prop :=
  ∀ U ∈ η, ∀ U' ∈ η, U ≠ U' → ∀ J ∈ Ω, ¬ (U ≤ J ∧ U' ≤ J)

@[expose] def etaSet (Ω : Set (Subgroup G)) (S : Subgroup G) : Set (Set (Subgroup G)) :=
  {η | η ⊆ {U | U ∈ USet Ω ∧ U ≤ S} ∧ InDistinctMembers Ω η ∧
    ∀ η' : Set (Subgroup G), η' ⊆ {U | U ∈ USet Ω ∧ U ≤ S} → InDistinctMembers Ω η' →
      η'.ncard ≤ η.ncard}

@[expose] def etaG (Ω : Set (Subgroup G)) : Set (Set (Subgroup G)) :=
  {η | ∃ S : Sylow 2 G, η ∈ etaSet Ω (S : Subgroup G) ∧
    ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η}

@[expose] def WSet (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {W | ∃ η ∈ etaG Ω, W = ⨆ U ∈ η, U}

variable (p f : ℕ) [Fact p.Prime]

structure HypOmega (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  classical : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z
  exact : ExactMembers Ω
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → Commutes K J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)

structure HypOmegaMod (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  classical : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)

variable {p f}

theorem oddCoreOf_eq_bot_of_exact {Ω : Set (Subgroup G)} (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : oddCoreOf K = ⊥ := by
  unfold oddCoreOf
  rw [hex K hK, Subgroup.map_bot]

theorem HypOmega.toMod {Ω : Set (Subgroup G)} (h : HypOmega p f Ω) : HypOmegaMod p f Ω where
  conjInvariant := h.conjInvariant
  classical := h.classical
  omega4 K hK J hJ hKJ := by
    refine ⟨(h.omega4 K hK J hJ hKJ).1, fun he => ?_⟩
    have hc := (h.omega4 K hK J hJ hKJ).2 he
    refine le_trans (Subgroup.commutator_le.mpr fun g hg x hx => ?_) bot_le
    have : g * x = x * g := hc g hg x hx
    simp [commutatorElement_def, this]
  omega5 := h.omega5

theorem HypOmegaMod.toExact {Ω : Set (Subgroup G)} (h : HypOmegaMod p f Ω) (hex : ExactMembers Ω) :
    HypOmega p f Ω where
  conjInvariant := h.conjInvariant
  classical := h.classical
  exact := hex
  omega4 K hK J hJ hKJ := by
    refine ⟨(h.omega4 K hK J hJ hKJ).1, fun he g hg x hx => ?_⟩
    have hle := (h.omega4 K hK J hJ hKJ).2 he
    rw [oddCoreOf_eq_bot_of_exact hex hK, bot_inf_eq, le_bot_iff] at hle
    have hmem : ⁅g, x⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator hg hx
    rw [hle] at hmem
    have h1 : ⁅g, x⁆ = 1 := (Subgroup.mem_bot.mp hmem)
    rw [commutatorElement_def] at h1
    calc g * x = (g * x * g⁻¹ * x⁻¹) * (x * g) := by group
      _ = x * g := by rw [h1, one_mul]
  omega5 := h.omega5

end CFSG.ClassicalInvolution.Asc77
