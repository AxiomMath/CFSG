module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

@[expose] def S267FactZ1 : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → Q.p ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S A : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → Subgroup.center ↥S = ⊥ →
      (catalogIs ↥S (onLie fun d => d = .A 2 Q) ∨ catalogIs ↥S (onLie fun d => d = .twistedA 2 Q)) →
      IsElemAbelian p A → Nat.card A = p ^ 4 → CycModSylow p S →
      Nat.card ↥(A ⊓ Subgroup.centralizer (S : Set Ω)) = p ∧
      ∃ a ∈ A, a ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
        ∃ R : Subgroup Ω, R ≤ S ∧ IsElemAbelian p R ∧ Nat.card R = p ^ 2 ∧
          (∀ s ∈ R, a * s = s * a) ∧
          ∃ r ∈ R, r ≠ 1 ∧
            GLAPComponent p (S ⊓ Subgroup.centralizer ({r} : Set Ω))
              (GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω))) ∧
            Subgroup.zpowers a ⊔ R ≤
              Subgroup.normalizer
                ((GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω)) : Subgroup Ω) : Set Ω) ∧
            (∀ b ∈ Subgroup.zpowers a ⊔ R,
              CentMod p (GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω))) b →
                b ∈ Subgroup.zpowers r) ∧
            GLAPLayer p (GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω)) ⊓
              Subgroup.centralizer ({a} : Set Ω)) ≠ ⊥ ∧
            (∃ T : Subgroup Ω, T ≤ S ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
              Subgroup.zpowers a ⊔ R ≤ Subgroup.normalizer (T : Set Ω)) ∧
            ∃ u ∈ S, u ≠ 1 ∧ u ^ 2 = 1 ∧ u * r = r * u ∧
              ∀ j ∈ GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω)), j * u = u * j

@[expose] def S267FactZ3 : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → Q.p ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S A : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → Subgroup.center ↥S ≠ ⊥ →
      (catalogIs (↥S ⧸ Subgroup.center ↥S) (onLie fun d => d = .A 2 Q) ∨
        catalogIs (↥S ⧸ Subgroup.center ↥S) (onLie fun d => d = .twistedA 2 Q)) →
      IsElemAbelian p A → Nat.card A = p ^ 4 → CycModSylow p S →
      Nat.card ↥(A ⊓ Subgroup.centralizer (S : Set Ω)) = p ∧
      ∃ b ∈ A, b ∉ Subgroup.centralizer (S : Set Ω) ∧
        GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω))
          (GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω))) ∧
        A ≤ Subgroup.normalizer
          ((GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) : Subgroup Ω) : Set Ω) ∧
        (∀ x ∈ A, CentMod p (GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω))) x →
          x ∈ Subgroup.zpowers b ⊔ (A ⊓ Subgroup.centralizer (S : Set Ω))) ∧
        (∃ a ∈ A, a ∉ Subgroup.zpowers b ⊔ (A ⊓ Subgroup.centralizer (S : Set Ω)) ∧
          GLAPLayer p (GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) ⊓
            Subgroup.centralizer ({a} : Set Ω)) ≠ ⊥) ∧
        (∃ T : Subgroup Ω, T ≤ S ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set Ω)) ∧
        ∃ u ∈ S, u ≠ 1 ∧ u ^ 2 = 1 ∧ u * b = b * u ∧
          ∀ j ∈ GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)), j * u = u * j

@[expose] def S267ClassicalIdx : TauCeti.LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ => True
  | _ => False

@[expose] def S267ConcBCDE (p q : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B : Subgroup Ω) : Prop :=
  (Nat.card B = p ^ 4 ∧ p = 3 ∧ ∃ Q : TauCeti.PrimePower, Q.p = q ∧
    ((pSimpleIsLie p S (.A 2 Q) ∧ p ∣ Q.card - 1) ∨
      (pSimpleIsLie p S (.twistedA 2 Q) ∧ p ∣ Q.card + 1))) ∨
  (Nat.card B = p ^ 4 ∧ B = (B ⊓ centModSubgroup p S) ⊔ (B ⊓ S) ∧
    (B ⊓ centModSubgroup p S) ⊓ (B ⊓ S) = ⊥ ∧ Subgroup.center (PQuot p S) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧
      ((pSimpleIsLie p S (.A 3 Q) ∧ p ∣ Q.card - 1) ∨
        (pSimpleIsLie p S (.twistedA 3 Q) ∧ p ∣ Q.card + 1))) ∨
  (Nat.card B = p ^ 4 ∧ B = (B ⊓ centModSubgroup p S) ⊔ (B ⊓ S) ∧
    (B ⊓ centModSubgroup p S) ⊓ (B ⊓ S) = ⊥ ∧ Subgroup.center (PQuot p S) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧
      (pSimpleIsLie p S (.B 3 Q) ∨ pSimpleIsLie p S (.twistedD 4 Q)) ∧ p ∣ Q.card ^ 2 - 1) ∨
  ((Nat.card B = p ^ 5 ∨ Nat.card B = p ^ 6) ∧ Nat.card ↥(B ⊓ S) = p ^ 4 ∧
    Subgroup.center (PQuot p S) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧ pSimpleIsLie p S (.D 4 Q) ∧ p ∣ Q.card ^ 2 - 1)

@[expose] def S267ConcA12 (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B : Subgroup Ω) : Prop :=
  ∃ B' D J : Subgroup Ω, IsElemAbelian p B' ∧ InD p B' 1 S D J ∧
    (B' = B ∨ (Nat.card B ≤ Nat.card B' ∧ ∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      B' ≤ Subgroup.normalizer (T : Set Ω))) ∧
    Nat.card ↥(B' ⊓ centModSubgroup p S) = p

@[expose] def S267ConcA (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B : Subgroup Ω) : Prop :=
  ∃ B' D J : Subgroup Ω, IsElemAbelian p B' ∧ InD p B' 1 S D J ∧
    (B' = B ∨ (Nat.card B ≤ Nat.card B' ∧ ∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      B' ≤ Subgroup.normalizer (T : Set Ω))) ∧
    Nat.card ↥(B' ⊓ centModSubgroup p S) = p ∧
    ∃ t : Ω, t ≠ 1 ∧ t ^ 2 = 1 ∧ (∀ d ∈ D, d * t = t * d) ∧ ∀ j ∈ J, j * t = t * j

@[expose] def S267FactGen : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple q (PSimple p S) →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
        Nat.card ↥(B ⊓ centModSubgroup p S) = p → ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
        S267ConcA12 p S B

@[expose] def S267FactP3 : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple q (PSimple p S) →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
        Nat.card ↥(B ⊓ centModSubgroup p S) = p → p = 3 → Nat.card B = 3 ^ 4 →
        S267ConcA p S B ∨ S267ConcBCDE p q S B

@[expose] def S267FactBadCls : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple q (PSimple p S) →
        catalogIs (PSimple p S) (onLie S267ClassicalIdx) →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
        Nat.card ↥(B ⊓ centModSubgroup p S) = p → ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B

@[expose] def S267FactBadExc : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple q (PSimple p S) →
        ¬ catalogIs (PSimple p S) (onLie S267ClassicalIdx) →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
        Nat.card ↥(B ⊓ centModSubgroup p S) = p → ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B

end CFSG.LocalAnalysis.GLTheoremA.S267

end
