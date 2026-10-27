module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

@[expose] def FixThreeA : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixThreeHyp L J u →
    IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L) →
    ∃ e : ℕ, 2 ≤ e ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 3 (GaloisField 2 e))

@[expose] def FixThreeVoid (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixThreeHyp L J u →
    𝔉 (↥L ⧸ Subgroup.center ↥L) → False

@[expose] def FixCensusCenterA : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixCenterData L J u →
    IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L) →
    ∃ e : ℕ, Even e ∧ 2 ≤ e ∧
      Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 e))

@[expose] def FixCensusCenterVoid (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixCenterData L J u →
    𝔉 (↥L ⧸ Subgroup.center ↥L) → False

@[expose] def PrimeCensusConcl {Y : Type} [Group Y] (L : Subgroup Y) (p : ℕ) (u : Y) : Prop :=
  ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
    ((∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q →
        IsCyclic Q) ∨
      ∃ e : ℕ, p ∣ 2 ^ e - 1 ∧
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 3 (GaloisField 2 e)))

@[expose] def FixPrimeA : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
    IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L) → PrimeCensusConcl L p u

@[expose] def FixPrimeTwistedA : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
    IsLieOf IdxTwistedA (↥L ⧸ Subgroup.center ↥L) →
    ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
      ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q → IsCyclic Q

@[expose] def FixPrimeCyc (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
    𝔉 (↥L ⧸ Subgroup.center ↥L) →
      ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q → IsCyclic Q

@[expose] def OddCenterRest : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    Odd (Nat.card (Subgroup.center ↥L)) → IsRestTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    Nat.card (Subgroup.center ↥L) = 1 ∨
      (Nat.card (Subgroup.center ↥L) = 3 ∧
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)))

@[expose] def ParabRadicalSelfNorm : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParab L J →
    L ⊓ Subgroup.normalizer (pCoreOf 2 J : Set Y) ≤ J

@[expose] def GlueVhyp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParab L J →
    ∀ V : Subgroup Y, ⁅V, V⁆ = V → V ≤ Subgroup.normalizer (L : Set Y) →
      V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) →
      V ≤ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)

@[expose] def IsPerfThreeSurvivor {Y : Type} [Group Y] (L : Subgroup Y) : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))) ∨
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8))

structure FixPerfThreeHyp {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y) :
    Prop where
  parab : CompParab L J
  perf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)
  norm : u ∈ Subgroup.normalizer (L : Set Y)
  pow : u ^ 3 = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)
  fix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J

@[expose] def KFactFixCensusPerfThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixPerfThreeHyp L J u →
    u ∈ L ⊔ Subgroup.centralizer (L : Set Y) ∧ IsPerfThreeSurvivor L

@[expose] def FixPerfThreeVoid (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixPerfThreeHyp L J u →
    𝔉 (↥L ⧸ Subgroup.center ↥L) → False

@[expose] def FixPerfThreeSmall : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y), FixPerfThreeHyp L J u →
    IsSmallTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    u ∈ L ⊔ Subgroup.centralizer (L : Set Y) ∧ IsPerfThreeSurvivor L

@[expose] def CentPerfectNoncyc (p : ℕ) {Y : Type} [Group Y] (L : Subgroup Y) (u : Y) : Prop :=
  ∃ V : Subgroup Y, V ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) ∧ ⁅V, V⁆ = V ∧
    ∃ Q : Subgroup Y, Q ≤ V ∧ IsPGroup p Q ∧ ¬ IsCyclic Q

@[expose] def KFactCentNoncycThree (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    Odd (Nat.card (Subgroup.center ↥L)) → 𝔉 (↥L ⧸ Subgroup.center ↥L) →
    ∀ u ∈ L, u ^ 3 = 1 → u ∉ Subgroup.centralizer (L : Set Y) → CentPerfectNoncyc 3 L u

@[expose] def KFactL3RankTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Subgroup.center ↥L) →
    (∃ e : ℕ, Nonempty (↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 3 (GaloisField 2 e))) →
    ∀ E : Subgroup Y, E ≤ L → IsElemAbelian p E → Nat.card E ≠ p ^ 3

end CFSG.AGLEmbedding
