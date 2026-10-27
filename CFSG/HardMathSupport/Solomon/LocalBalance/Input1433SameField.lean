module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def IsSL3EpsOver (Y : Type) [Group Y] (q : ℕ) : Prop :=
  ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (Y ≃* ↥(StatedSL 3 F))) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧
      Nonempty (Y ≃* ↥(StatedSU 3 q F))) ∧ 3 ∣ Nat.card (Subgroup.center Y)

@[expose] def IsD4Over (Y : Type) [Group Y] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (Y ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F)))

theorem isSL3Eps_exists_over {Y : Type} [Group Y] (hY : IsSL3Eps Y) :
    ∃ q : ℕ, IsSL3EpsOver Y q := by
  rcases hY with ⟨hSL | hSU, hcenter⟩
  · rcases hSL with ⟨F, fieldF, finiteF, hequiv⟩
    letI : Field F := fieldF
    letI : Finite F := finiteF
    exact ⟨Nat.card F, Or.inl ⟨F, fieldF, finiteF, rfl, hequiv⟩, hcenter⟩
  · rcases hSU with ⟨F, fieldF, finiteF, q, hcard, hequiv⟩
    letI : Field F := fieldF
    letI : Finite F := finiteF
    exact ⟨q, Or.inr ⟨F, fieldF, finiteF, hcard, hequiv⟩, hcenter⟩

structure Input14_33Setup {X : Type} [Group X] [Finite X]
    (K Q₁ Q : Subgroup X) (t : X) : Prop where
  generated : K ⊔ Q₁ ⊔ Subgroup.zpowers t = ⊤
  normal : K.Normal
  quasisimple : IsQuasisimple ↥K
  kGroup : IsKGroup ↥K
  coreFree : GLAPPrimeCore 3 X = ⊥
  centralizerRank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (K : Set X))
  localRank : GLATwoLocalRank 3 X ≤ 4
  threeGroup : IsPGroup 3 Q₁
  twoElement : ∃ k : ℕ, t ^ (2 ^ k) = 1
  normalizes : t ∈ Subgroup.normalizer (Q₁ : Set X)
  inverts : ∀ q ∈ Q₁, t * q * t⁻¹ * q ∈ (frattini ↥Q₁).map Q₁.subtype
  contained : Q ≤ Q₁
  normalQ : (Q.subgroupOf Q₁).Normal
  orderQ : Nat.card Q = 27
  nonabelianQ : ¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a
  exponentQ : ∀ a ∈ Q, a ^ 3 = 1
  noncentralZ : ¬ ((Subgroup.center ↥Q).map Q.subtype ≤
    (Subgroup.center ↥K).map K.subtype)
  containedZ : (Subgroup.center ↥Q).map Q.subtype ≤ K
  centralizes : Q ≤ Subgroup.centralizer (GLAPLayer 3 (K ⊓ Subgroup.centralizer
    (((Subgroup.center ↥Q).map Q.subtype : Subgroup X) : Set X)) : Set X)

@[expose] def Input14_33LiteralSameField : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q : ℕ),
    Input14_33Setup K Q₁ Q t →
    IsComponentOf J (GLAPLayer 3 (K ⊓ Subgroup.centralizer
      (((Subgroup.center ↥Q).map Q.subtype : Subgroup X) : Set X))) →
    IsSL3EpsOver ↥J q →
    (Subgroup.center ↥Q).map Q.subtype = (Subgroup.center ↥J).map J.subtype →
    (Nat.card J).factorization 3 = 3 → IsD4Over ↥K q

@[expose] def Input14_33SameField : Prop :=
  Input14_33LiteralSameField

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns
