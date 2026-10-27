module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def KFact64iiL : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (H Q M₀ : Subgroup A) (x z : A),
    p.Prime → 5 ≤ p → CFSG.Open.IsKGroup ↥H → orderOf x = p → orderOf z = p → x * z = z * x →
    x ∉ zpowers z → CFSG.ABGLocalTools.IsSylowOf p Q H → zpowers x ⊔ zpowers z ≤ Q →
    (∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) → x ∉ (frattini ↥Q).map Q.subtype →
    (∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z) →
    Q ≤ M₀ → M₀ ≤ H → normalizer (zpowers z : Set A) ⊓ H ≤ M₀ →
    ¬ H ≤ M₀ ⊔ rankThreePrimeCore p H →
    ∃ L : Subgroup A, S622IsSimpleSection L (rankThreePrimeCore p H) ∧ L ≤ H ∧ z ∈ L ∧
      CFSG.Open.pRank p L ≤ 1 ∧ ¬ L ≤ (M₀ ⊓ L) ⊔ rankThreePrimeCore p H ∧
      M₀ ≤ normalizer (L : Set A)

@[expose] def KGL613b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z →
    ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
    ∀ Y : Subgroup G, Y ≤ M → z ∈ Y → S622IsSimpleSection Y (rankThreePrimeCore p Y) →
      ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → f ∣ (rankThreePrimeCore p Y).relIndex Y →
        CFSG.Open.GLBStronglyEmbedded f M

@[expose] def KG2024 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X S : Subgroup A) (z : A) (n p : ℕ),
    (Nonempty (↥X ≃* alternatingGroup (Fin n)) ∨ Nonempty (↥X ≃* Equiv.Perm (Fin n))) →
    6 ≤ n → p.Prime → 5 ≤ p → p ≤ n → n < 2 * p → orderOf z = p → z ∈ X → S ≤ X →
    IsPGroup 2 S → S ≠ ⊥ → z ∈ normalizer (S : Set A) →
    ∃ T Y : Subgroup A, T ≤ S ∧ T ≠ ⊥ ∧ z ∈ normalizer (T : Set A) ∧
      S ≤ normalizer (T : Set A) ∧ Y ≤ normalizer (T : Set A) ⊓ X ∧ z ∈ Y ∧
      S622IsSimpleSection Y (rankThreePrimeCore p Y) ∧ 3 ∣ (rankThreePrimeCore p Y).relIndex Y

@[expose] def KFactAutAltOrder : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 5 ≤ n → Nonempty (K ≃* alternatingGroup (Fin n)) →
    Nat.card (MulAut K) ∣ 2 * n.factorial

@[expose] def KFactAutAltEmbed : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K X : Subgroup A) (n : ℕ), 5 ≤ n → n ≠ 6 → K ≤ X →
    (K.subgroupOf X).Normal → Nonempty (↥K ≃* alternatingGroup (Fin n)) →
    (∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → c = 1) →
    Nonempty (↥X ≃* alternatingGroup (Fin n)) ∨ Nonempty (↥X ≃* Equiv.Perm (Fin n))

@[expose] def KGAltSix : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X S : Subgroup A) (z : A),
    (Nonempty (↥X ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥X ≃* Equiv.Perm (Fin 6))) →
    orderOf z = 5 → z ∈ X → S ≤ X → IsPGroup 2 S → z ∈ normalizer (S : Set A) → S = ⊥

@[expose] def KGStep4Concl (A : Type) [Group A] [Finite A] (Kb Sb : Subgroup A) : Prop :=
  CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 ↥Kb ∧
    ¬ (Nonempty (↥Kb ≃* alternatingGroup (Fin 6)) ∧
      (Nonempty (↥(Kb ⊔ Sb) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (↥(Kb ⊔ Sb) ≃* Equiv.Perm (Fin 6)))) ∧
    ∀ n : ℕ, 7 ≤ n → ¬ Nonempty (↥Kb ≃* alternatingGroup (Fin n))

structure KQCfg (A : Type) [Group A] [Finite A] (p : ℕ) (Kb Sb Bb Mb : Subgroup A) (z : A) :
    Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  simple : IsSimpleGroup ↥Kb
  nonab : ∃ a b : ↥Kb, a * b ≠ b * a
  rank : CFSG.Open.pRank p Kb ≤ 1
  z_mem_K : z ∈ Kb
  z_mem_B : z ∈ Bb
  z_order : orderOf z = p
  S_two : IsPGroup 2 Sb
  S_ne : Sb ≠ ⊥
  B_elem : IsElemAbelian p Bb
  B_card : Nat.card Bb = p ^ 2
  B_le_S : Bb ≤ normalizer (Sb : Set A)
  S_le_K : Sb ≤ normalizer (Kb : Set A)
  B_le_K : Bb ≤ normalizer (Kb : Set A)
  max_S : ∀ T : Subgroup A, IsPGroup 2 T → Bb ≤ normalizer (T : Set A) → Sb ≤ T → T = Sb
  cover : ∀ T : Subgroup A, T ≤ Sb → T ≠ ⊥ → Sb ≤ normalizer (T : Set A) →
    Bb ≤ normalizer (T : Set A) → normalizer (T : Set A) ≤ Mb
  cover_Z : normalizer (zpowers z : Set A) ≤ Mb
  not_le : ¬ Kb ≤ Mb

@[expose] def KQStrong (A : Type) [Group A] [Finite A] (p : ℕ) (Mb : Subgroup A) (z : A) : Prop :=
  ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → ∀ Y : Subgroup A, Y ≤ Mb → z ∈ Y →
    S622IsSimpleSection Y (rankThreePrimeCore p Y) → f ∣ (rankThreePrimeCore p Y).relIndex Y →
    ∀ F : Subgroup A, IsPGroup f F → F ⊓ Y ≠ ⊥ → ∀ F₁ : Subgroup A, F₁ ≤ F → F₁ ≠ ⊥ →
      normalizer (F₁ : Set A) ≤ Mb

@[expose] def KQStrongEmb (A : Type) [Group A] [Finite A] (p : ℕ) (Mb : Subgroup A) (z : A) :
    Prop :=
  ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → ∀ Y : Subgroup A, Y ≤ Mb → z ∈ Y →
    S622IsSimpleSection Y (rankThreePrimeCore p Y) → f ∣ (rankThreePrimeCore p Y).relIndex Y →
    ∀ g : A, g ∉ Mb → ¬ f ∣ Nat.card ↥(Mb ⊓ CFSG.Open.GLBConj g Mb)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
