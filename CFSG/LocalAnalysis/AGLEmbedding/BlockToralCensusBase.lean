module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

@[expose] def CycPerfect (p : ℕ) {Y : Type*} [Group Y] (J : Subgroup Y) : Prop :=
  ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ Q : Subgroup Y, Q ≤ V → IsPGroup p Q → IsCyclic Q

structure CompParab {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) : Prop where
  comp : IsComponentOf L ⊤
  type : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)
  odd : Odd (Nat.card (Subgroup.center ↥L))
  parab : IsParabolicTwo L J
  ne_top : J ≠ L
  ne_borel : ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)

@[expose] def KFactFixCensusThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParab L J → CycPerfect 3 J →
    ∀ u ∈ L, u ^ 3 = 1 → u ∉ Subgroup.centralizer (L : Set Y) →
    (∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
      V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ u ∈ V) →
    (∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) →
    ∃ e : ℕ, 2 ≤ e ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 3 (GaloisField 2 e))

@[expose] def KFactFixCensusCenter : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParab L J → CycPerfect 3 J →
    3 ∣ Nat.card (Subgroup.center ↥L) →
    ¬ (Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))) →
    ∀ u ∈ L ⊔ Subgroup.centralizer (L : Set Y), u ^ 3 = 1 →
    u ∉ Subgroup.centralizer (L : Set Y) → (∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) →
    ∃ e : ℕ, Even e ∧ 2 ≤ e ∧
      Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 e))

@[expose] def KFactFixCensusPrime : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParab L J →
    ∀ p : ℕ, p.Prime → 5 ≤ p → CycPerfect p J →
    ∀ u ∈ L ⊔ Subgroup.centralizer (L : Set Y), u ^ p = 1 →
    u ∉ Subgroup.centralizer (L : Set Y) →
    (∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
      V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ u ∈ V) →
    (∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) →
    ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
      ((∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q →
          IsCyclic Q) ∨
        ∃ e : ℕ, p ∣ 2 ^ e - 1 ∧
          Nonempty (↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 3 (GaloisField 2 e)))

@[expose] def IdxA : TauCeti.LieTypeIndex → Prop
  | .A _ q => q.p = 2
  | _ => False

@[expose] def IdxTwistedA : TauCeti.LieTypeIndex → Prop
  | .twistedA _ q => q.p = 2
  | _ => False

@[expose] def IdxB : TauCeti.LieTypeIndex → Prop
  | .B _ q => q.p = 2
  | _ => False

@[expose] def IdxD : TauCeti.LieTypeIndex → Prop
  | .D _ q => q.p = 2
  | _ => False

@[expose] def IdxTwistedD : TauCeti.LieTypeIndex → Prop
  | .twistedD _ q => q.p = 2
  | _ => False

@[expose] def IdxG2 : TauCeti.LieTypeIndex → Prop
  | .G2 q => q.p = 2
  | _ => False

@[expose] def IsLieOf (P : TauCeti.LieTypeIndex → Prop) (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, P d.1 ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsSmallTwoOrG2 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))

@[expose] def IsRestTwoOrG2 (X : Type) [Group X] : Prop :=
  IsLieOf IdxB X ∨ IsLieOf IdxD X ∨ IsLieOf IdxTwistedD X ∨ IsLieOf IdxG2 X ∨ IsSmallTwoOrG2 X

structure FixThreeData {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y) : Prop where
  parab : CompParab L J
  cyc : CycPerfect 3 J
  mem : u ∈ L
  pow : u ^ 3 = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)
  perfect : ∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
    V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ u ∈ V
  fix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J

structure FixCenterData {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y) : Prop where
  parab : CompParab L J
  cyc : CycPerfect 3 J
  three_dvd : 3 ∣ Nat.card (Subgroup.center ↥L)
  not_threeASix : ¬ (Nat.card (Subgroup.center ↥L) = 3 ∧
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)))
  mem : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)
  pow : u ^ 3 = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)
  fix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J

structure FixPrimeData {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y) :
    Prop where
  parab : CompParab L J
  prime : p.Prime
  five_le : 5 ≤ p
  cyc : CycPerfect p J
  mem : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)
  pow : u ^ p = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)
  perfect : ∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
    V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ u ∈ V
  fix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J

structure FixThreeHyp {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) (u : Y) : Prop where
  parab : CompParab L J
  cyc : CycPerfect 3 J
  mem : u ∈ L
  pow : u ^ 3 = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)
  join : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)
  fix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J

structure FixPrimeHyp {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y) :
    Prop where
  parab : CompParab L J
  prime : p.Prime
  five_le : 5 ≤ p
  cyc : CycPerfect p J
  mem : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)
  pow : u ^ p = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)
  join : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)
  fix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J

end CFSG.AGLEmbedding
