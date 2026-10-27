module

public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

@[expose] def stage2E (M β : Subgroup X) (z : X) : Subgroup X := M ⊓ β ⊓ conjugate β z

@[expose] noncomputable def stage2NDExp (p : ℕ) (M β Q : Subgroup X) : ℕ :=
  (Nat.card ↥(M ⊓ β ⊓ normalizer (Q : Set X))).factorization p

structure Stage2Adm (Z : Set X) (M : Subgroup X) (z : X) (p : ℕ) (β Q : Subgroup X) : Prop where
  ne_bot : Q ≠ ⊥
  pgroup : IsPGroup p Q
  le_E : Q ≤ stage2E M β z
  z_norm : z ∈ normalizer (Q : Set X)
  exists_t : ∃ t ∈ Z, t ∈ normalizer (Q : Set X) ∧ conjugate M t = β ∧
    ∃ P₁ : Subgroup X, ABGLocalTools.IsSylowOf p P₁ (stage2E M β z) ∧
      P₁ ≤ normalizer (Q : Set X) ∧ t ∈ normalizer (P₁ : Set X)

structure Stage2Data (Z : Set X) (M : Subgroup X) (z : X) (p : ℕ) (W β Q : Subgroup X) (t : X)
    (R P₁ : Subgroup X) : Prop where
  tmax : T4Max Z M z p W
  beta_mem : β ∈ omegaFix M (W : Set X)
  beta_ne : β ≠ M
  theta : oPrimePrime p (M ⊓ β) = ⊥
  dt : DoublyTransitive M
  transS : TransitiveOnS Z M
  card_lt : Nat.card (CFSG.OddInversion.invertedSet W z) < zNumShare Z M p
  sevenD : ∀ S' : Subgroup X, ABGLocalTools.IsSylowOf p S' (stage2E M β z) →
    p ∣ Nat.card ↥⁅zpowers z, S'⁆
  adm : Stage2Adm Z M z p β Q
  maxQ : ∀ Q' : Subgroup X, Stage2Adm Z M z p β Q' → stage2NDExp p M β Q' ≤ stage2NDExp p M β Q
  t_mem : t ∈ Z
  t_norm_Q : t ∈ normalizer (Q : Set X)
  t_swap : conjugate M t = β
  P₁_syl : ABGLocalTools.IsSylowOf p P₁ (stage2E M β z)
  P₁_le_N : P₁ ≤ normalizer (Q : Set X)
  t_norm_P₁ : t ∈ normalizer (P₁ : Set X)
  R_syl : ABGLocalTools.IsSylowOf p R (M ⊓ β ⊓ normalizer (Q : Set X))
  P₁_le_R : P₁ ≤ R
  t_norm_R : t ∈ normalizer (R : Set X)
  card_P₁_lt : Nat.card P₁ < Nat.card R

@[expose] def SevenDStmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Cand Z M z p W → ∀ β ∈ omegaFix M (W : Set X), β ≠ M →
    ∀ S' : Subgroup X, ABGLocalTools.IsSylowOf p S' (stage2E M β z) →
      p ∣ Nat.card ↥⁅zpowers z, S'⁆

@[expose] def Stage2ExistsStmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Max Z M z p W →
    ∃ (β Q : Subgroup X) (t : X) (R P₁ : Subgroup X), Stage2Data Z M z p W β Q t R P₁

@[expose] def Lemma710Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W β Q t R P₁, Stage2Data Z M z p W β Q t R P₁ →
    2 ≤ Open.pRank 2 (zHull Z (normalizer (Q : Set X))) ∧
      pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) ≤ stage2E M β z

@[expose] def stage2M2 (Z : Set X) (M Q : Subgroup X) : Subgroup X :=
  pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) ⊔ zHull Z (M ⊓ zHull Z (normalizer (Q : Set X)))

@[expose] def Lemma711Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W β Q t R P₁, Stage2Data Z M z p W β Q t R P₁ →
    2 ≤ Open.pRank 2 (zHull Z (normalizer (Q : Set X))) →
    pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) ≤ stage2E M β z →
      ∀ m ∈ stage2M2 Z M Q, ∃ a ∈ oPrimePrime p (stage2M2 Z M Q),
        a ∈ pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) ∧
        ∃ n ∈ stage2M2 Z M Q ⊓ normalizer (zjSubgroup p R : Set X), m = a * n

end CFSG.GH74.Uniqueness
