module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Core
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open scoped MatrixGroups

abbrev reeExp (a : ℕ) : Fin Tag.F4.rank → ℕ :=
  fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)

abbrev ReeQuot (K : Type) [Field K] (a : ℕ) : Type :=
  DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm (reeExp a))

inductive ExcModel {G : Type} [Group G] (A : Subgroup G) : Type 1
  | g2 (m : ℕ) (hm : 2 ≤ m) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
      (e : rankTwoQuot A ≃* AdjointQuotient .G2 K)
  | f4 (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
      (e : rankTwoQuot A ≃* AdjointQuotient .F4 K)
  | e6 (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
      (e : rankTwoQuot A ≃* AdjointQuotient .E6 K)
  | e7 (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
      (e : rankTwoQuot A ≃* AdjointQuotient .E7 K)
  | e8 (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
      (e : rankTwoQuot A ≃* AdjointQuotient .E8 K)
  | triality (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
      (hK : Nat.card K = (2 ^ m) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ m)
      (e : rankTwoQuot A ≃* DerivedCentralQuotient (twistedFixedGroup .D4 K σ))
  | twistedE6 (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
      (hK : Nat.card K = (2 ^ m) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ m)
      (e : rankTwoQuot A ≃* DerivedCentralQuotient (twistedFixedGroup .E6 K σ))
  | ree (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
      (e : rankTwoQuot A ≃* ReeQuot K a)
  | tits (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (e : rankTwoQuot A ≃* ReeQuot K 0)

namespace ExcModel

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def q : ExcModel A → ℕ
  | g2 m .. => 2 ^ m
  | f4 m .. => 2 ^ m
  | e6 m .. => 2 ^ m
  | e7 m .. => 2 ^ m
  | e8 m .. => 2 ^ m
  | triality m .. => 2 ^ m
  | twistedE6 m .. => 2 ^ m
  | ree a .. => 2 ^ (2 * a + 1)
  | tits .. => 2

@[expose] def tag : ExcModel A → StatedLieTag
  | g2 .. => .G2
  | f4 .. => .F4
  | e6 .. => .E6
  | e7 .. => .E7
  | e8 .. => .E8
  | triality .. => .trialityD4
  | twistedE6 .. => .twistedE6
  | ree .. => .twistedF4
  | tits .. => .Tits

@[expose] def LeviType : ExcModel A → Subgroup G → Prop
  | g2 m .., L => if m = 2 then StatedClassicalModel (rankTwoQuot L) .PSL 3 2 2
      else StatedClassicalModel (rankTwoQuot L) .PSL 2 2 m
  | f4 m .., L => StatedClassicalModel (rankTwoQuot L) .PSp 3 2 m
  | e6 m .., L => StatedClassicalModel (rankTwoQuot L) .PSL 6 2 m
  | e7 m .., L => StatedClassicalModel (rankTwoQuot L) .POmegaPlus 6 2 m
  | e8 m .., L => ChevalleyExceptionalModel (rankTwoQuot L) .E7 2 m
  | triality m .., L => StatedClassicalModel (rankTwoQuot L) .PSL 3 2 m ∨
      StatedClassicalModel (rankTwoQuot L) .PSL 2 2 (3 * m)
  | twistedE6 m .., L => StatedClassicalModel (rankTwoQuot L) .PSU 6 2 m ∨
      StatedClassicalModel (rankTwoQuot L) .POmegaMinus 4 2 m
  | ree a .., L => StatedClassicalModel (rankTwoQuot L) .PSL 2 2 (2 * a + 1)
  | tits .., _ => False

@[expose] def IsTrialityFour : ExcModel A → Prop
  | triality m .. => m = 2
  | _ => False

end ExcModel

theorem nonempty_excModel {G : Type} [Group G] {A : Subgroup G}
    (h : RankTwoExceptionalEvenType (rankTwoQuot A)) : Nonempty (ExcModel A) := by
  rcases h with ⟨m, hm, -, K, _, _, hK, ⟨e⟩⟩ | ⟨t, ht, m, hm, hD⟩ |
      ⟨m, hm, -, a, ha, K, _, _, hK, ⟨e⟩⟩ | ⟨-, a, ha, K, _, _, hK, ⟨e⟩⟩
  · exact ⟨.g2 m hm K hK e⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hD
      exact ⟨.triality m hm K hK σ hσ e⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hD
      exact ⟨.f4 m hm K hK e⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hD
      exact ⟨.e6 m hm K hK e⟩
    · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hD
      exact ⟨.twistedE6 m hm K hK σ hσ e⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hD
      exact ⟨.e7 m hm K hK e⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hD
      exact ⟨.e8 m hm K hK e⟩
  · obtain rfl : a = m := by omega
    exact ⟨.ree a hm K hK e⟩
  · obtain rfl : a = 0 := by omega
    exact ⟨.tits K hK e⟩

section Config

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def InducesInner (y : G) (L : Subgroup G) : Prop :=
  ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ (center ↥L).map L.subtype

structure Config814 (D : ExcModel A) (g : G) (R T Q : Subgroup G) : Prop where
  not_mem : g ∉ normalizer (A : Set G)
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  sylowT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)
  le_normalizer : T ≤ normalizer (A : Set G)
  commute : ⁅T, R⁆ = ⊥
  two_lt_q : 2 < D.q
  le : Q ≤ A
  ne_bot : Q ≠ ⊥
  quasisimple : CFSG.Open.IsQuasisimple ↥(AS76b.layerCentralizer A Q)
  odd_center : Odd (Nat.card (center ↥(AS76b.layerCentralizer A Q)))
  levi : D.LeviType (AS76b.layerCentralizer A Q)
  sylow_inf : IsSylowOf 2 R (centralizer (Q : Set G) ⊓
    centralizer (AS76b.layerCentralizer A Q : Set G) ⊓ normalizer (R : Set G))
  le_sup : T ≤ R ⊔ AS76b.layerCentralizer A Q
  inf_eq_bot : T ⊓ AS76b.layerCentralizer A Q = ⊥
  not_le : ¬ centralizer (Q : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G)
  noConj : ∀ n : ℕ, 2 ^ n = Nat.card R →
    Nonempty (↥(AS76b.layerCentralizer A Q) ≃* SL(2, GaloisField 2 n)) →
      ∀ c : G, ¬ R.map (MulAut.conj c).toMonoidHom ≤ AS76b.layerCentralizer A Q
  diag : D.IsTrialityFour →
    StatedClassicalModel (rankTwoQuot (AS76b.layerCentralizer A Q)) .PSL 3 2 2 →
      ∃ y ∈ A ⊓ centralizer (Q : Set G), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
        ¬ InducesInner y (AS76b.layerCentralizer A Q)

end Config

@[expose] def Step83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), AS76b.Hyp31 A →
    RankTwoExceptionalEvenType (rankTwoQuot A) → Odd (Nat.card (center A))

@[expose] def Step814 (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ExcModel A), D.tag = t →
    AS76b.Hyp31 A → Odd (Nat.card (center A)) →
      ∃ (g : G) (R T Q : Subgroup G), Config814 D g R T Q

@[expose] def ExcAt (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop :=
  RankTwoHyp G A → standardComponentOddCore G = ⊥ →
    RankTwoExceptionalEvenType (rankTwoQuot A) →
      ChevalleyExceptionalModel A .G2 2 2 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Co1

@[expose] def L3EvenAt (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop :=
  RankTwoHyp G A → ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
    (standardComponentOddCore G = ⊥ → m = 2) ∧
    (m = 2 →
      (NativeSporadic.IsSporadic (rankTwoX A ⧸ center (rankTwoX A)) .Suz ∧
          Nat.card (center (rankTwoX A)) ∣ 3) ∨
        (Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
          NativeSporadic.IsSporadic (rankTwoX A) .He)) ∧
    (standardComponentOddCore G = ⊥ →
      NativeSporadic.IsSporadic (rankTwoX A) .Suz ∨
        (Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
          NativeSporadic.IsSporadic (rankTwoX A) .He))

theorem rankTwoExceptionalEvenStandard_iff :
    RankTwoExceptionalEvenStandard ↔
      ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), ExcAt G A :=
  Iff.rfl

theorem rankTwoL3EvenStandard_iff :
    RankTwoL3EvenStandard ↔ ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), L3EvenAt G A :=
  Iff.rfl

@[expose] def ExcHypII : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    RankTwoExceptionalEvenType (A ⧸ center A) → AS76b.HypII A

@[expose] def G2FourOddCenter : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    ChevalleyExceptionalModel (A ⧸ center A) .G2 2 2 → Odd (Nat.card (center A)) →
      center A = ⊥

@[expose] def L34DiagFact (X₀ : Type) [Group X₀] : Prop :=
  ∀ (L : Subgroup X₀) (U : Subgroup (MulAut X₀)) (σ : MulAut X₀), CFSG.Open.IsQuasisimple ↥L →
    StatedClassicalModel (rankTwoQuot L) .PSL 3 2 2 → (∀ u ∈ U, ∀ x ∈ L, u x = x) →
    IsElemAbelian 2 U → 4 ≤ Nat.card U → (∀ x, x ∈ L ↔ σ x ∈ L) →
    (∀ u ∈ U, σ * u = u * σ) → (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∃ l ∈ L, ∀ x ∈ L, σ x * (l * x * l⁻¹)⁻¹ ∈ (center ↥L).map L.subtype

@[expose] def SuzL34DiagInput : Prop :=
  L34DiagFact NativeSporadic.Suz

end CFSG.ComponentClassification.RankTwoExceptional
