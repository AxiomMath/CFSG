module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def IsSLThreeEps (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧
      Nonempty (Y ≃* ↥(StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧ q ≠ 8 ∧
      Nonempty (Y ≃* ↥(StatedSU 3 q K)))

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def pumpUp (L : Subgroup G) (x : G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
    GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)))

@[expose] def Lemma510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsUpsilonComponent B b L →
      (IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L)) ∧
      (∃ A : Subgroup G, IsEkIn 3 2 B A ∧ ∀ a ∈ A, InducesFieldAut 3 L a) ∧
      ∀ x ∈ B, x ≠ 1 → InducesFieldAut 3 L x →
        GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) (pumpUp L x) ∧
        InducesFieldAut 3 (pumpUp L x) b ∧
        B ⊓ oPrimePOf 3 L ≤ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G))

@[expose] def Lemma511 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    (¬ ∃ B : Subgroup G, IsExtremal B) →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsUpsilonComponent B b L →
      IsSLThreeEps (barOf 3 L)

@[expose] def Lemma512 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsUpsilonComponent B b L →
      b ∈ L → ∀ A : Subgroup G, IsEkIn 3 2 B A → b ∈ A → ∀ x : G,
        x ∈ Subgroup.centralizer ({b} : Set G) → orderOf x = 3 →
        x ∈ Subgroup.centralizer (A : Set G) →
        (∀ g ∈ A ⊔ Subgroup.zpowers x, InducesFieldAut 3 L g) →
          b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G))

@[expose] def Lemma513 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsUpsilonComponent B b L →
      b ∈ L →
      ∃ B' : Subgroup G, IsBZeroMax 3 B' ∧
        (b ∈ B' ∧ B' ≤ B ⊔ L ∧ ¬ B' ⊓ L ≤ oPrimePOf 3 L ∧ B ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L) ≤ B') ∧
        (∃ A' : Subgroup G, IsEkIn 3 3 B' A' ∧ ∀ a ∈ A', InducesFieldAut 3 L a) ∧
        ¬ IsUpsilonComponent B' b L ∧
        ∀ x ∈ B', x ≠ 1 →
          upsilonOf B' x ≤ upsilonOf B' b ⊔ GLAPPrimeCoreOf 3 (upsilonOf B' x)

@[expose] def IsExtremalWitness (B : Subgroup G) (b : G) (L A : Subgroup G) : Prop :=
  b ∈ B ∧ b ≠ 1 ∧
    GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L ∧
    ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
    IsExtremalType (barOf 3 L) ∧
    (Nat.card ↥(B ⊓ L) = 9 ∧ IsEkIn 3 2 B A ∧ b ∈ A ∧
      (∀ a ∈ A, InducesFieldAut 3 L a) ∧
      B ⊓ L ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ∧
      ∃ f : QuaternionGroup 2 →* autizer (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))
          (B ⊓ L), Function.Injective f) ∧
    (∀ x ∈ B, x ≠ 1 → InducesFieldAut 3 L x →
      GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) (pumpUp L x) ∧
      InducesFieldAut 3 (pumpUp L x) b ∧
      Nat.card (barOf 3 (pumpUp L x)) ≤ Nat.card (barOf 3 L))

@[expose] def Lemma514 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ b : G, ∀ L A : Subgroup G, IsExtremalWitness B b L A →
      ∀ a ∈ A, a ≠ 1 →
        ⁅Subgroup.zpowers b, ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)),
            GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))⁆ ≤
          GLAPPrimeCoreOf 3 (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)),
            GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))) ∧
        (a ∉ Subgroup.zpowers b →
          (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)),
              GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))) ≤
            GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ⊔
              GLAPPrimeCoreOf 3 (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)),
                GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))))

@[expose] def Lemma515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ b : G, ∀ L A : Subgroup G, IsExtremalWitness B b L A →
      ∀ x ∈ A, x ≠ 1 →
        Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤
          Subgroup.normalizer (((⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
            GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))) : Subgroup G) : Set G)

theorem IsExtremal.exists_witness {B : Subgroup G} (h : IsExtremal B) :
    IsBOneMax 3 B ∧ ∃ (b : G) (L A : Subgroup G), IsExtremalWitness B b L A := by
  obtain ⟨hB, b, hb, hb1, L, hL, hbal, hty, ⟨hF, A, hA, hbA, hfld, hJ, hq⟩, hx, -⟩ := h
  exact ⟨hB, b, L, A, hb, hb1, hL, hbal, hty, ⟨hF, hA, hbA, hfld, hJ, hq⟩, hx⟩


@[expose] def Lemma52One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∃ b ∈ B, b ≠ 1 ∧ upsilonOf B b ≠ ⊥

end CFSG.HardMathSupport.Solomon.LocalBalance
