module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Strong

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo)

@[expose] def S622IsSimpleSection {A : Type} [Group A] (L D : Subgroup A) : Prop :=
  D ≤ L ∧ (D.subgroupOf L).Normal ∧ D ≠ L ∧
    (∀ N : Subgroup A, D ≤ N → N ≤ L → (N.subgroupOf L).Normal → N = D ∨ N = L) ∧
    ¬ ∀ a ∈ L, ∀ b ∈ L, a * b * a⁻¹ * b⁻¹ ∈ D

@[expose] def S622KFactD : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (D V M₀ : Subgroup A) (z : A),
    p.Prime → 5 ≤ p → CFSG.Open.IsKGroup ↥D → orderOf z = p → z ∈ normalizer (D : Set A) →
    ¬ p ∣ Nat.card D → CFSG.ABGLocalTools.IsSylowOf 2 V D → z ∈ normalizer (V : Set A) →
    M₀ ≤ D →
    (∀ U : Subgroup A, U ≤ V → U ≠ ⊥ → z ∈ normalizer (U : Set A) →
      normalizer (U : Set A) ⊓ D ≤ M₀) →
    centralizer ({z} : Set A) ⊓ D ≤ M₀ →
    (∀ U : Subgroup A, U ≤ D → IsPGroup 2 U → U ≠ ⊥ → U ≤ centralizer ({z} : Set A) →
      normalizer (U : Set A) ⊓ D ≤ M₀) →
    D ≤ M₀ ⊔ rankThreePrimeCore 2 D

@[expose] def S622KFactSimple : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (x z : A) (Q M : Subgroup A),
    p.Prime → 5 ≤ p → CFSG.Open.IsKGroup ↥(centralizer ({x} : Set A)) →
    orderOf x = p → orderOf z = p → x * z = z * x → x ∉ zpowers z →
    CFSG.ABGLocalTools.IsSylowOf p Q (centralizer ({x} : Set A)) →
    zpowers x ⊔ zpowers z ≤ Q → Q ≤ centralizer ({z} : Set A) →
    CFSG.Open.pRank p Q ≤ 2 → x ∉ (frattini ↥Q).map Q.subtype →
    (∀ g : A, g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z → g * z * g⁻¹ ∈ zpowers z) →
    Q ≤ M → normalizer (zpowers z : Set A) ≤ M →
    (∀ S : Subgroup A, S ≤ Q → 2 ≤ CFSG.Open.pRank p S → normalizer (S : Set A) ≤ M) →
    Odd (Nat.card (rankThreePrimeCore p (centralizer ({x} : Set A)))) →
    ¬ (centralizer ({x} : Set A) ≤
      (M ⊓ centralizer ({x} : Set A)) ⊔ rankThreePrimeCore p (centralizer ({x} : Set A))) →
    ∃ L : Subgroup A, S622IsSimpleSection L (rankThreePrimeCore p (centralizer ({x} : Set A))) ∧
      L ≤ centralizer ({x} : Set A) ∧ z ∈ L ∧ CFSG.Open.pRank p L ≤ 1 ∧
      ¬ L ≤ (M ⊓ L) ⊔ rankThreePrimeCore p (centralizer ({x} : Set A)) ∧
      M ⊓ centralizer ({x} : Set A) ≤ normalizer (L : Set A)

@[expose] def S622Prop65 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z →
      ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
        ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M → Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

@[expose] def S622Kx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T →
        rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥ →
        ∀ L : Subgroup G, S622IsSimpleSection L ⊥ → L ≤ centralizer ({x} : Set G) → z ∈ L →
          CFSG.Open.pRank p L ≤ 1 → ¬ L ≤ M →
          M ⊓ centralizer ({x} : Set G) ≤ normalizer (L : Set G) → False

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
