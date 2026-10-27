module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.Open.FusionDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Case64i (p q : ℕ) (B : Subgroup G) (_x : G) (L : Subgroup G) : Prop :=
  Nat.card B = p ^ 4 ∧ ∃ Q : TauCeti.PrimePower, Q.p = q ∧
    ((pSimpleIsLie p L (.A 2 Q) ∧ p ∣ Q.card - 1) ∨
      (pSimpleIsLie p L (.twistedA 2 Q) ∧ p ∣ Q.card + 1))

@[expose] def Case64ii (p q : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  Nat.card B = p ^ 4 ∧ IsDirectZpowersInf B x L ∧ Subgroup.center (PQuot p L) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧
      ((pSimpleIsLie p L (.A 3 Q) ∧ p ∣ Q.card - 1) ∨
        (pSimpleIsLie p L (.twistedA 3 Q) ∧ p ∣ Q.card + 1))

@[expose] def Case64iii (p q : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  Nat.card B = p ^ 4 ∧ IsDirectZpowersInf B x L ∧ Subgroup.center (PQuot p L) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧
      (pSimpleIsLie p L (.B 3 Q) ∨ pSimpleIsLie p L (.twistedD 4 Q)) ∧ p ∣ Q.card ^ 2 - 1

@[expose] def Case64iv (p q : ℕ) (B : Subgroup G) (_x : G) (L : Subgroup G) : Prop :=
  (Nat.card B = p ^ 5 ∨ Nat.card B = p ^ 6) ∧ Nat.card (B ⊓ L : Subgroup G) = p ^ 4 ∧
    Subgroup.center (PQuot p L) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧ pSimpleIsLie p L (.D 4 Q) ∧ p ∣ Q.card ^ 2 - 1

@[expose] def Case34 (p q : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  Case64iii p q B x L ∨ Case64iv p q B x L

@[expose] def Case234 (p q : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  Case64ii p q B x L ∨ Case34 p q B x L

theorem lemma64Cases_iff (p q : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) :
    Lemma64Cases p q B x L ↔ Case64i p q B x L ∨ Case234 p q B x L := Iff.rfl

@[expose] def IsSL3Type (p q : ℕ) (J : Subgroup G) : Prop :=
  ∃ Q : TauCeti.PrimePower, Q.p = q ∧
    (pSimpleIsLie p J (.A 2 Q) ∨ pSimpleIsLie p J (.twistedA 2 Q)) ∧
    (p = 3 → Subgroup.center (PQuot p J) ≠ ⊥)

@[expose] def IsOmegaType (p q : ℕ) (J : Subgroup G) : Prop :=
  ∃ Q : TauCeti.PrimePower, Q.p = q ∧
    (pSimpleIsLie p J (.B 2 Q) ∨ pSimpleIsLie p J (.A 3 Q) ∨ pSimpleIsLie p J (.twistedA 3 Q))

@[expose] def JType (p q : ℕ) (J : Subgroup G) : Prop := IsSL3Type p q J ∨ IsOmegaType p q J

@[expose] def LieTypeNonIsoAt : Prop :=
  ∀ (S : Type) [Group S] (Q Q' : TauCeti.PrimePower),
    (catalogIs S (onLie fun d => d = .A 2 Q) ∨ catalogIs S (onLie fun d => d = .twistedA 2 Q)) →
    (catalogIs S (onLie fun d => d = .B 2 Q') ∨ catalogIs S (onLie fun d => d = .A 3 Q') ∨
      catalogIs S (onLie fun d => d = .twistedA 3 Q')) → False


@[expose] def I268At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L → GLAPLayer p X = L →
      (∃ Q : TauCeti.PrimePower, Q.p = q ∧
        (pSimpleIsLie p L (.A 2 Q) ∨ pSimpleIsLie p L (.twistedA 2 Q))) →
      CycModSylow p L →
      (∃ z ∈ X, z ≠ 1 ∧ z ^ p = 1 ∧ ∀ w ∈ X, w * z = z * w) →
      (∃ A : Subgroup G, A ≤ X ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 4) →
      ∃ B E D : Subgroup G, B ≤ X ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 4 ∧
        E ≤ B ∧ Nat.card E = p ^ 3 ∧ D ≤ E ∧ Nat.card D = p ^ 2 ∧
        (∃ U : Subgroup G, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)) ∧
        (∃ U : Subgroup G, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ D ≤ Subgroup.normalizer (U : Set G) ∧
          CoversMod p (Subgroup.normalizer (U : Set G))
            (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)))) ∧
        GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G))
          (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G))) ∧
        (∀ b ∈ B, CentMod p (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G))) b ↔ b ∈ D) ∧
        GLAPLayer p (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)) ⊓
          Subgroup.centralizer (E : Set G)) ≠ ⊥

@[expose] def I81At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), InTq q p B x L → Case234 p q B x L →
      ∃ y ∈ B ⊓ L, y ≠ 1 ∧ ∃ J E : Subgroup G,
        GLAPLayer p (L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) = J ∧
        GLAPComponent p (L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) J ∧
        (∀ b ∈ B, CentMod p J b ↔ b ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∧
        E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤ E ∧
        GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ ∧
        (Case64ii p q B x L → IsSL3Type p q J) ∧ (Case34 p q B x L → IsOmegaType p q J)

@[expose] def I112ChevAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (X B K L₁ J : Subgroup G) (x : G), CFSG.Open.IsKGroup ↥X → B ≤ X → IsElemAbelian p B →
      (∀ (B' U : Subgroup G), B' ≤ X → IsElemAbelian p B' → U ≤ X → U ≠ ⊥ → IsPGroup 2 U →
        B' ≤ Subgroup.normalizer (U : Set G) → Nat.card B' ≤ Nat.card B) →
      GLAPComponent p X L₁ → K = ⨆ b ∈ B, GLBConj b L₁ →
      x ∈ B → x ∉ Subgroup.normalizer (L₁ : Set G) →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J →
      IsChevSimple q (PSimple p J) →
      p = 3 ∧ Subgroup.center (PQuot p J) = ⊥ ∧
        ∃ Q : TauCeti.PrimePower,
          (pSimpleIsLie p J (.A 2 Q) ∨ pSimpleIsLie p J (.twistedA 2 Q))

@[expose] def I2020At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (B : Subgroup G) (a : G) (K J T S D : Subgroup G) (y : G),
      InTq q p B a K → Lemma64Cases p q B a K →
      D ≤ Subgroup.normalizer (K : Set G) → y ∈ D → ¬ CentMod p K y → y ^ p = 1 →
      D ≤ Subgroup.zpowers y ⊔ centModSubgroup p K →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J → JType p q J →
      CFSG.Open.fusionIsSylowIn 2 T J →
      IsPGroup 2 S → S ≤ Subgroup.normalizer (K : Set G) → ⁅T, S⁆ ≤ centModSubgroup p K →
      D ≤ Subgroup.normalizer (S : Set G) → ⁅S, D⁆ = S →
      ⁅J, S⁆ ≤ centModSubgroup p K ∨ (Case34 p q B a K ∧ IsSL3Type p q J)

end CFSG.LocalAnalysis.GLTheoremA
