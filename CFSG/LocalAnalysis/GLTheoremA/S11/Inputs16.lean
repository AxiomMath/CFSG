module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def I161aAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ K : Subgroup G, IsChev2 K → NoSplit16 p K →
    ¬ p ∣ Nat.card (Subgroup.center ↥K) ∧
      ∀ B : Subgroup G, IsElemAbelian p B → InnerDiagMarking B K → ∀ b ∈ B, InducesInnerMod p K b

@[expose] def I161bAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ K : Subgroup G, IsChev2 K → HalfSplit16At p K → NoSplit16 p K →
    Odd (Nat.card (Subgroup.center ↥K))

@[expose] def I162At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (B K : Subgroup G) (k : ℕ), IsElemAbelian p B → InnerDiagMarking B K →
    3 ≤ k → evenRank ↥K ≤ k + 1 → p ^ k * Nat.card ↥(B ⊓ centModSubgroup p K) ≤ Nat.card B →
    HalfSplit16At p K

@[expose] def I163At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ K : Subgroup G, IsChev2 K → 3 ≤ GLATwoLocalRank p ↥K →
    GLATwoLocalRank p ↥K = evenRank ↥K →
    (Odd (Nat.card (Subgroup.center ↥K)) ∨
      ∃ B : Subgroup G, B ≤ K ∧ IsElemAbelian p B ∧ Nat.card B = p ^ GLATwoLocalRank p ↥K ∧
        (⁅B, nGen B K⁆ : Subgroup G) ≠ ⊥) →
    ∃ lab : GLALabel, LabelOf K lab ∧ GLASplit16 p lab

@[expose] def I164At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X K B : Subgroup G, IsComponentOf K X → IsChev2 K → B ≤ X →
    IsElemAbelian p B → InnerDiagMarking B K → 4 ≤ CFSG.Open.pRank p B →
    (∃ b ∈ B ⊓ Subgroup.centralizer (K : Set G), b ≠ 1) →
    GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → CFSG.Open.pRank p B < evenRank ↥K → NoSplit16 p K

@[expose] def I165At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p q : ℕ, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → ∀ K A : Subgroup G, IsChev2 K → NoSplit16 p K →
    ¬ p ∣ Nat.card (Subgroup.center ↥K) →
    IsSCIn p K A → GLATwoLocalRank p ↥K ≤ CFSG.Open.pRank p A → CFSG.Open.pRank p K ≤ CFSG.Open.pRank p A →
    ((⁅A, nGen A K⁆ : Subgroup G) ≠ ⊥ ∨ CFSG.Open.pRank p A + 2 ≤ evenRank ↥K) →
    evenRank ↥K = GLATwoLocalRank q ↥K → CFSG.Open.pRank p A + 1 ≤ evenRank ↥K →
    4 ≤ CFSG.Open.pRank p A + 1 →
    ∃ D E F J : Subgroup G, D ≤ E ∧ E ≤ A ∧ Nat.card D = p ∧ Nat.card E = p ^ 2 ∧
      GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set G)) J ∧ A ≤ Subgroup.normalizer (J : Set G) ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ ∧
      F ≤ K ⊓ Subgroup.centralizer (D : Set G) ∧ IsElemAbelian q F ∧
      F ≤ Subgroup.normalizer (J : Set G) ∧ 3 ≤ CFSG.Open.pRank q F

structure Concl166 (G : Type) [Group G] [Finite G] (p q : ℕ) (K B' : Subgroup G) (x' : G) (J : Subgroup G) : Prop where
  prime : q.Prime
  odd : q ≠ 2
  elem : IsElemAbelian q B'
  le : B' ≤ K
  mem : x' ∈ B'
  ne_one : x' ≠ 1
  rank_B : Nat.card B' = q ^ evenRank ↥K
  rank_K : GLATwoLocalRank q ↥K = evenRank ↥K
  comp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x'} : Set G)) ∧
    GLALayer (K ⊓ Subgroup.centralizer ({x'} : Set G)) = J
  chev2 : IsChev2 J
  shape : ∀ lab : GLALabel, LabelOf K lab →
    ∃ labJ : GLALabel, LabelOf J labJ ∧ JShape lab (3 ∣ Nat.card (Subgroup.center ↥K)) labJ
  m2 : evenRank ↥K + 2 ≤ twoRank ↥J
  odd_center : Odd (Nat.card (Subgroup.center ↥J))
  e3 : ∃ E : Subgroup G, E ≤ B' ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 3 ∧ x' ∈ E ∧
    GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥
  dvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)
  six : (Subgroup.center ↥J = ⊥ ∧ TrivialMultiplier J) ∨
    (evenRank ↥K = 4 ∧ ∃ labJ : GLALabel, LabelOf J labJ ∧ labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
    (J = K ∧ 3 ∣ Nat.card (Subgroup.center ↥K) ∧ ∃ lab : GLALabel, LabelOf K lab ∧ Odd lab.n ∧
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6))
  idiag : InnerDiagMarking B' J
  seven : B' ≤ J ⊔ Subgroup.zpowers x' ∨ LabelOf K ⟨.twA, 5, 2⟩
  rank_inf : evenRank ↥K ≤ CFSG.Open.pRank q (B' ⊓ J) + 2
  eight : ∃ S : Subgroup G, S ≤ J ∧ IsPGroup 2 S ∧ B' ≤ Subgroup.normalizer (S : Set G) ∧
    B' ⊓ Subgroup.centralizer (S : Set G) = Subgroup.zpowers x'
  su_case : 3 ∣ Nat.card (Subgroup.center ↥K) →
    (∃ lab : GLALabel, LabelOf K lab ∧ ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
    J = K ∧ q = 3 ∧ x' ∈ K ∧ ∀ k ∈ K, k * x' = x' * k

@[expose] def I166At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ K : Subgroup G, IsChev2 K → HalfSplit16At p K → NoSplit16 p K →
    4 ≤ evenRank ↥K → GLATwoLocalRank p ↥K + 1 = evenRank ↥K → (p = 7 → ¬ LabelOf K ⟨.E6, 0, 1⟩) →
    ∃ (q : ℕ) (B' : Subgroup G) (x' : G) (J : Subgroup G), Concl166 G p q K B' x' J

@[expose] def InnDiagIndepAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B K : Subgroup G) (P : GLAMarkProp K), InnerDiagMarking B K → GLAMarking K P →
    GLAMarking K fun lab R _ I F θ => P lab R I F θ ∧ B ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ

@[expose] def RankThreeLabelAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (B K : Subgroup G) (lab : GLALabel), IsElemAbelian p B → InnerDiagMarking B K →
    p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p K) ≤ Nat.card B → LabelOf K lab →
    lab.tag ≠ .triD4 ∧ lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4

end CFSG.LocalAnalysis.GLTheoremA
