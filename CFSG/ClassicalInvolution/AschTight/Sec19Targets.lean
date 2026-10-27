module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm6
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.AschTight.MuZ2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

structure Sec19Data {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G) : Prop where
  tight : S19R.TightStd p f K z
  mu : ¬ AllTypeTwo K z
  ih : CITBelowAll p (Nat.card G)
  cex : ¬ ConcOrTF4 G
  sylow : ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G)
  hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  hW : W ∈ WSet (CoreAssembly.conjClass K)
  hWS : W ≤ (S : Subgroup G)

@[expose] def C19_6Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      W ⊔ centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K =
          oddCoreOf (centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K) ⊔ W ∨
        IsQuaternionSub ((S : Subgroup G) ⊓
          centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K)

@[expose] def C19_14Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      W ⊔ centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K ≠
        oddCoreOf (centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K) ⊔ W

@[expose] def L6_11ModTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
      ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

@[expose] def L6_12ModTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
      ∀ S : Sylow 2 G,
        let M : Subgroup G := ⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧
          U ≤ (S : Subgroup G)}, U
        (∃ η ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η, conjSub m U ∈ η) ∧
          (∀ η' ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η', conjSub m U ∈ η') → η' = η) ∧
          ∀ g : G, (∀ U ∈ η, conjSub g U ≤ (S : Subgroup G)) → ∀ U ∈ η, conjSub g U ∈ η) ∨
        ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω

@[expose] def L7_6ModTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
      ∀ W ∈ WSet Ω, ¬ IsMulCommutative ↥(muGroup Ω W) →
        (∀ x ∈ Subgroup.centralizer (W : Set G), ∀ g : G,
            g * x * g⁻¹ ∈ Subgroup.centralizer (W : Set G) →
              ∃ n ∈ Subgroup.normalizer (W : Set G), n * x * n⁻¹ = g * x * g⁻¹) ∧
          ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ g : G, conjSub g R = T →
            ∃ n ∈ Subgroup.normalizer (W : Set G), conjSub n R = T

@[expose] def L7_13ModTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ J ∈ Ω, ∀ a : G, IsUniqueInvolution J a →
      a ∈ Subgroup.normalizer (W : Set G) → DOrder3 W R (conjSub a R) →
        ∀ T ∈ DSet Ω W, T ≤ R ⊔ conjSub a R ⊔ W ⊔ OCW W →
          ¬ T ≤ R ⊔ W ⊔ OCW W → ¬ T ≤ conjSub a R ⊔ W ⊔ OCW W →
            ∀ L ∈ Ω, T ≤ L → L = J ∨ L ∈ omegaStarNbr Ω J

@[expose] def L7_14ModTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, DOrder3 W R T →
      ∀ L U : Subgroup G, L = R ⊔ T → U = L ⊓ W →
        ∀ x : G, IsPGroup 2 (Subgroup.zpowers x) → conjSub x L = L →
          (∀ y ∈ U, y * y = 1 → x * y = y * x) →
            (∀ u v : G, Subgroup.zpowers u = R ⊓ W → Subgroup.zpowers v = T ⊓ W →
              ∀ k : ℤ, (∃ i : ℕ, x ^ i * u * (x ^ i)⁻¹ = u ^ k) ↔
                (∃ i : ℕ, x ^ i * v * (x ^ i)⁻¹ = v ^ k)) ∧
            ((∀ y ∈ U, x * y = y * x) →
              Subgroup.zpowers x ⊔ U =
                  centralizerModOdd (Subgroup.zpowers x ⊔ U) L ⊔ U ∧
                centralizerModOdd (Subgroup.zpowers x ⊔ U) L ⊓ U = ⊥) ∧
            (oddCoreOf L = ⊥ → x * x = 1 →
              IsQuaternionSub (R ⊓ Subgroup.centralizer ({x} : Set G)) →
                Nat.card ↥(R ⊓ Subgroup.centralizer ({x} : Set G)) * 2 = Nat.card ↥R →
                  ∀ R₁ ∈ DSet Ω W, R₁ ≤ L → ∀ R₂ ∈ DSet Ω W, R₂ ≤ L →
                    ∃ c ∈ L ⊓ Subgroup.centralizer ({x} : Set G), conjSub c R₁ = R₂)

@[expose] def InA {G : Type} [Group G] (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  J ∈ omegaStarNbr Ω K ∧ J ∉ omegaNbr Ω K ∧ ∃ zK zJ : G, IsUniqueInvolution K zK ∧
    IsUniqueInvolution J zJ ∧ ¬ ∃ g ∈ pairNormalizers K J zK zJ, conjSub g K = J

end CFSG.ClassicalInvolution.Disconnected.AschTight
