module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie IsChevSimple)

@[expose] def KxSection {A : Type} [Group A] (z : A) (X : Subgroup A) (f : ℕ) : Prop :=
  ∃ H N : Subgroup A, H ≤ X ∧ S622IsSimpleSection H N ∧ z ∈ H ∧ z ∉ N ∧ f ∣ N.relIndex H

@[expose] def IsDihedralTypeIndex : TauCeti.LieTypeIndex → Prop
  | .A 1 q => q.p ≠ 2
  | .A 2 q => q.p ≠ 2
  | .twistedA 2 q => q.p ≠ 2
  | _ => False

@[expose] def IsReeIndex : TauCeti.LieTypeIndex → Prop
  | .reeG2 _ => True
  | _ => False

@[expose] def IsRankTwoOddIndex : TauCeti.LieTypeIndex → Prop
  | .A 3 q => q.p ≠ 2
  | .twistedA 3 q => q.p ≠ 2
  | .B 2 q => q.p ≠ 2
  | .G2 q => q.p ≠ 2
  | _ => False

@[expose] def IsParabolicTwo (A : Type) [Group A] (K P : Subgroup A) : Prop :=
  P ≤ K ∧ ∃ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K ∧ normalizer (U : Set A) ⊓ K ≤ P

@[expose] def KFactDihedralTypeAut : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L R : Subgroup A) (g : A) (r : ℕ),
    catalogIs ↥L (onLie IsDihedralTypeIndex) → R ≤ L → IsPGroup 2 R → g ∈ L →
    g ∈ normalizer (R : Set A) → r.Prime → 5 ≤ r → orderOf g = r → ∀ y ∈ R, g * y = y * g

@[expose] def KFactReeSylowTwo : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L E : Subgroup A), IsSimpleGroup ↥L →
    catalogIs ↥L (onLie IsReeIndex) → CFSG.ABGLocalTools.IsSylowOf 2 E L →
      IsElemAbelian 2 E ∧ Nat.card E = 8

@[expose] def KFactReeL28 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L T : Subgroup A) (z : A),
    catalogIs ↥L (onLie IsReeIndex) → CFSG.ABGLocalTools.IsSylowOf 2 T L → z ∈ L →
    orderOf z = 7 → z ∈ normalizer (T : Set A) →
    ∃ H N : Subgroup A, H ≤ (normalizer (zpowers z : Set A) ⊓ L) ⊔ T ∧
      S622IsSimpleSection H N ∧ z ∈ H ∧ z ∉ N ∧ 3 ∣ N.relIndex H

@[expose] def KFactReeBorel : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L E : Subgroup A),
    catalogIs ↥L (onLie IsReeIndex) → CFSG.ABGLocalTools.IsSylowOf 3 E L →
      Group.IsSolvable ↥(normalizer (E : Set A) ⊓ L) ∧
      ∀ J : Subgroup A, normalizer (E : Set A) ⊓ L ≤ J → J ≤ L →
        J = normalizer (E : Set A) ⊓ L ∨ J = L

@[expose] def KFact2024 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L S : Subgroup A) (z : A) (n p : ℕ),
    Nonempty (↥L ≃* alternatingGroup (Fin n)) → 6 ≤ n → p.Prime → 5 ≤ p → orderOf z = p →
    z ∈ L → CFSG.Open.pRank p L ≤ 1 → S ≤ L → IsPGroup 2 S → S ≠ ⊥ →
    z ∈ normalizer (S : Set A) →
    ∃ T' : Subgroup A, T' ≤ S ∧ T' ≠ ⊥ ∧ z ∈ normalizer (T' : Set A) ∧
      KxSection z (normalizer (T' : Set A) ⊓ L) 3

@[expose] def KFact2025 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L S : Subgroup A) (z : A) (p : ℕ),
    catalogIs ↥L (onLie IsRankTwoOddIndex) → p.Prime → p ≠ 2 → orderOf z = p → z ∈ L →
    CFSG.Open.pRank p L ≤ 1 → S ≤ L → IsPGroup 2 S → S ≠ ⊥ → z ∈ normalizer (S : Set A) →
    ⁅S, zpowers z⁆ = S → KxSection z (normalizer (S : Set A) ⊓ L) 3

@[expose] def KFact2401Three : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L E : Subgroup A),
    ((∃ n : ℕ, 7 ≤ n ∧ Nonempty (↥L ≃* alternatingGroup (Fin n))) ∨
        catalogIs ↥L (onLie IsRankTwoOddIndex)) →
    CFSG.ABGLocalTools.IsSylowOf 3 E L →
    ∀ J : Subgroup A, (∀ S₀ : Subgroup A, S₀ ≤ E → S₀ ≠ ⊥ → normalizer (S₀ : Set A) ⊓ L ≤ J) →
      L ≤ J

@[expose] def KFact2314 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L F : Subgroup A) (f : ℕ),
    f.Prime → f ≠ 2 →
    catalogIs ↥L (onLie (fun d =>
      d.characteristic = f ∧ ¬ IsDihedralTypeIndex d ∧ ¬ IsReeIndex d)) →
    CFSG.ABGLocalTools.IsSylowOf f F L →
    ∀ J : Subgroup A, (∀ S₀ : Subgroup A, S₀ ≤ F → 2 ≤ CFSG.Open.pRank f S₀ →
        normalizer (S₀ : Set A) ⊓ L ≤ J) → L ≤ J

@[expose] def KFact1019 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A) (d : TauCeti.ValidLieTypeIndex),
    d.1.characteristic ≠ 2 → Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank d.1.characteristic (normalizer (U : Set A) ⊓ L) ≤ 3) →
    IsDihedralTypeIndex d.1 ∨ IsReeIndex d.1 ∨ IsRankTwoOddIndex d.1

@[expose] def KFactSporThree : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A) (s : TauCeti.SporadicName),
    Nontrivial ↥L → Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    CFSG.Open.pRank 3 L ≤ 1 → s = .J1

@[expose] def KFactJ1Sylow : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L T : Subgroup A), IsSimpleGroup ↥L →
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) →
    CFSG.ABGLocalTools.IsSylowOf 2 T L → IsElemAbelian 2 T ∧ Nat.card T = 8

@[expose] def KFactJ1L27 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L T : Subgroup A) (z : A),
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) →
    CFSG.ABGLocalTools.IsSylowOf 2 T L → z ∈ L → orderOf z = 7 → z ∈ normalizer (T : Set A) →
    ∀ J : Subgroup A, normalizer (zpowers z : Set A) ⊓ L ≤ J → normalizer (T : Set A) ⊓ L ≤ J →
      L ≤ J

@[expose] def KFact131 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K Q : Subgroup A),
    IsChevSimple 2 ↥K → Q ≤ K → IsPGroup 2 Q → Q ≠ ⊥ →
    ∃ P : Subgroup A, IsParabolicTwo A K P ∧ Q ≤ pCoreOf 2 P ∧ normalizer (Q : Set A) ⊓ K ≤ P

@[expose] def KFactParabolicGen : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K W : Subgroup A),
    IsChevSimple 2 ↥K → ¬ fusionIsBenderGroup ↥K → CFSG.ABGLocalTools.IsSylowOf 2 W K →
    ∀ J : Subgroup A, (∀ Q₂ : Subgroup A, Q₂ ≤ W → Q₂ ≠ ⊥ →
        normalizer (W : Set A) ⊓ K ≤ normalizer (Q₂ : Set A) → normalizer (Q₂ : Set A) ⊓ K ≤ J) →
      K ≤ J

@[expose] def KFact2715 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K T : Subgroup A) (z : A) (r : ℕ),
    fusionIsBenderGroup ↥K → CFSG.ABGLocalTools.IsSylowOf 2 T K → z ∈ K →
    z ∈ normalizer (T : Set A) → orderOf z = r → r.Prime → r ≠ 2 →
    ∀ J : Subgroup A, normalizer (zpowers z : Set A) ⊓ K ≤ J → T ≤ J → K ≤ J

@[expose] def KFactParabolicCover : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ : Subgroup A) (z : A) (p : ℕ),
    IsChevSimple 2 ↥K → p.Prime → 5 ≤ p → CFSG.Open.pRank p K ≤ 1 → orderOf z = p → z ∈ K₀ →
    IsParabolicTwo A K K₀ → K₀ ≠ K →
    (∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
      ¬ U ≤ rankThreePrimeCore p K₀) →
    ∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ KxSection z K₀ f ∧
      ∃ g ∈ K, g ∉ K₀ ∧ f ∣ Nat.card ↥(K₀ ⊓ GLBConj g K₀)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
