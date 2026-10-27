module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def lieIndexChar : TauCeti.LieTypeIndex → ℕ
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q | .E6 q | .E7 q | .E8 q
  | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.p
  | .suzuki _ | .reeF4 _ | .tits => 2
  | .reeG2 _ => 3

@[expose] def IsChevIndexOfChar (q : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A 1 r => r.p = q ∨ (q = 2 ∧ r.card = 9) ∨ (q = 3 ∧ r.card = 8)
  | .twistedA 2 r => r.p = q ∨ (q = 2 ∧ r.card = 3)
  | d => lieIndexChar d = q

@[expose] def IsChevOfChar (q : ℕ) (Q : Type*) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsChevIndexOfChar q d.1 ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def SL3EpsOfChar (p : ℕ) (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), CharP K p ∧ Nat.card K % 3 = 1 ∧
      Nonempty (Y ≃* ↥(StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), CharP K p ∧ Nat.card K = q ^ 2 ∧
      q % 3 = 2 ∧ q ≠ 2 ∧ Nonempty (Y ≃* ↥(StatedSU 3 q K)))

@[expose] def centerIn {Y : Type*} [Group Y] (K : Subgroup Y) : Subgroup Y :=
  (Subgroup.center ↥K).map K.subtype

@[expose] def IsMaxInvSub {Y : Type*} [Group Y] (A K : Subgroup Y) (q : ℕ) (Q : Subgroup Y) : Prop :=
  Q ≤ K ∧ IsPGroup q ↥Q ∧ A ≤ Subgroup.normalizer (Q : Set Y) ∧
    ∀ Q' : Subgroup Y, Q' ≤ K → IsPGroup q ↥Q' → A ≤ Subgroup.normalizer (Q' : Set Y) → Q ≤ Q' →
      Q' = Q

@[expose] def IsSU38 (Y : Type*) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ^ 2 ∧ Nonempty (Y ≃* ↥(StatedSU 3 8 K))

structure Input25_3FactsNo38 : Prop where
  chev : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K → ∀ b : Y, b ∈ Subgroup.normalizer (K : Set Y) →
    b ^ 3 ∈ Subgroup.centralizer (K : Set Y) → ∀ J : Subgroup Y,
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J → ∀ p : ℕ, p.Prime →
    SL3EpsOfChar p (↥J ⧸ GLAPPrimeCore 3 ↥J) → IsChevOfChar p (↥K ⧸ Subgroup.center ↥K)
  borelTits : ∀ (Y : Type) [Group Y] [Finite Y] (K A Q : Subgroup Y) (q : ℕ), q.Prime → q ≠ 3 →
    CFSG.Open.IsQuasisimple ↥K → IsChevOfChar q (↥K ⧸ Subgroup.center ↥K) →
    A ≤ Subgroup.normalizer (K : Set Y) → IsPGroup 3 ↥A → IsMaxInvSub A K q Q →
    ¬ Q ≤ centerIn K → ∀ y ∈ K, y ∈ Subgroup.centralizer (Q : Set Y) → y ∈ centerIn K ⊔ Q

structure Input25_3Facts : Prop extends Input25_3FactsNo38 where
  su38 : ∀ (Y : Type) [Group Y] [Finite Y] (K J A : Subgroup Y) (b : Y) (hbJ : b ∈ J),
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K → b ∈ K →
    orderOf b = 3 → CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({b} : Set Y)) →
    IsSU38 (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) =
      Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)) →
    A ≤ Subgroup.normalizer (K : Set Y) → CFSG.Open.IsElemAbelian 3 A → Nat.card A = 9 → b ∈ A →
    (∀ a ∈ A, a ≠ 1 → InducesFieldAut 3 J a) →
    (∃ a ∈ A, ∃ h : a ∈ Subgroup.normalizer (J : Set Y), barAut 3 J ⟨a, h⟩ ≠ 1) →
      J = K ∨ ∃ a ∈ A, a ≠ 1 ∧ b ∉ oPrimePOf 3 (K ⊓ Subgroup.centralizer ({a} : Set Y))

end CFSG.HardMathSupport.Solomon.Coordinator
