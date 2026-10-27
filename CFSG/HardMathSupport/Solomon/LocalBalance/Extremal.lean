module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def IsEntrywiseAutPSL {K : Type} [Field K] (σ : K ≃+* K)
    (φ : MulAut (StatedProj (StatedSL 3 K))) : Prop :=
  ∀ A A' : ↥(StatedSL 3 K),
    ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ →
    φ (QuotientGroup.mk A) = QuotientGroup.mk A'

@[expose] def IsEntrywiseAutPSU {K : Type} [Field K] (q : ℕ) (σ : K ≃+* K)
    (φ : MulAut (StatedProj (StatedSU 3 q K))) : Prop :=
  ∀ A A' : ↥(StatedSU 3 q K),
    ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ →
    φ (QuotientGroup.mk A) = QuotientGroup.mk A'

@[expose] def IsFieldAutPSL3 {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 3 K))
    (σ : K ≃+* K) (φ γ : MulAut (StatedProj (StatedSL 3 K))),
    IsEntrywiseAutPSL σ φ ∧
      ∀ y : Y, θ (QuotientGroup.mk (α y)) = (γ * φ * γ⁻¹) (θ (QuotientGroup.mk y))

@[expose] def IsFieldAutPSU3 {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU 3 q K))
    (σ : K ≃+* K) (φ γ : MulAut (StatedProj (StatedSU 3 q K))),
    Nat.card K = q ^ 2 ∧ Odd (orderOf σ) ∧ IsEntrywiseAutPSU q σ φ ∧
      ∀ y : Y, θ (QuotientGroup.mk (α y)) = (γ * φ * γ⁻¹) (θ (QuotientGroup.mk y))

@[expose] def IsFieldAutThree {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  α = 1 ∨ IsFieldAutPSL3 α ∨ IsFieldAutPSU3 α

variable {G : Type*} [Group G]

@[expose] def InducesFieldAut (p : ℕ) (L : Subgroup G) (g : G) : Prop :=
  ∃ h : g ∈ Subgroup.normalizer (L : Set G), IsFieldAutThree (barAut p L ⟨g, h⟩)

variable [Finite G]

@[expose] def IsUpsilonComponent (B : Subgroup G) (b : G) (L : Subgroup G) : Prop :=
  GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L ∧
    ((L ≤ lambdaOf 3 B b ∧ ¬ L ≤ psiStarGroup 3 B) ∨
      ∃ D : Subgroup G, IsEkIn 3 2 B D ∧
        ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L)

@[expose] noncomputable def upsilonOf (B : Subgroup G) (b : G) : Subgroup G :=
  sSup {L | IsUpsilonComponent B b L}

instance normal_centralizer_in_normalizer (J F : Subgroup G) :
    ((J ⊓ Subgroup.centralizer (F : Set G)).subgroupOf (J ⊓ Subgroup.normalizer (F : Set G))).Normal :=
  ⟨fun c hc n => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    obtain ⟨hcJ, hcF⟩ := hc
    have hnJ : (n : G) ∈ J := n.2.1
    have hnF : (n : G) ∈ Subgroup.normalizer (F : Set G) := n.2.2
    refine ⟨?_, ?_⟩
    · simpa using J.mul_mem (J.mul_mem hnJ hcJ) (J.inv_mem hnJ)
    · show (↑n * ↑c * (↑n)⁻¹ : G) ∈ Subgroup.centralizer (F : Set G)
      have hcF' : (c : G) ∈ Subgroup.centralizer (F : Set G) := hcF
      rw [Subgroup.mem_centralizer_iff] at hcF' ⊢
      intro f hf
      have hn' : (n : G)⁻¹ * f * (n : G) ∈ F := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnF) f).1 hf
        simpa using this
      have h1 := hcF' _ hn'
      calc f * (↑n * ↑c * (↑n)⁻¹)
          = ↑n * ((↑n)⁻¹ * f * ↑n * ↑c) * (↑n)⁻¹ := by group
        _ = ↑n * (↑c * ((↑n)⁻¹ * f * ↑n)) * (↑n)⁻¹ := by rw [h1]
        _ = ↑n * ↑c * (↑n)⁻¹ * f := by group⟩

abbrev autizer (J F : Subgroup G) : Type _ :=
  ↥(J ⊓ Subgroup.normalizer (F : Set G)) ⧸
    (J ⊓ Subgroup.centralizer (F : Set G)).subgroupOf (J ⊓ Subgroup.normalizer (F : Set G))

@[expose] def IsExtremalType (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧
      Nonempty (Y ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧ q ≠ 8 ∧
      Nonempty (Y ≃* StatedProj (StatedSU 3 q K)))

@[expose] def IsExtremal (B : Subgroup G) : Prop :=
  IsBOneMax 3 B ∧ ∃ b ∈ B, b ≠ 1 ∧ ∃ L : Subgroup G,
    GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L ∧
    ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
    IsExtremalType (barOf 3 L) ∧
    (Nat.card ↥(B ⊓ L) = 9 ∧ ∃ A : Subgroup G, IsEkIn 3 2 B A ∧ b ∈ A ∧
      (∀ a ∈ A, InducesFieldAut 3 L a) ∧
      B ⊓ L ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ∧
      ∃ f : QuaternionGroup 2 →* autizer (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))
          (B ⊓ L), Function.Injective f) ∧
    (∀ x ∈ B, x ≠ 1 → InducesFieldAut 3 L x →
      GLAPComponent 3 (Subgroup.centralizer ({x} : Set G))
        (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
          GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)))) ∧
      InducesFieldAut 3
        (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
          GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)))) b ∧
      Nat.card (barOf 3 (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
          GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G))))) ≤
        Nat.card (barOf 3 L)) ∧
    ∃ E : Subgroup G, IsEkIn 3 3 B E ∧ Even (Nat.card (alphaE 3 2 E))

end CFSG.HardMathSupport.Solomon.LocalBalance
