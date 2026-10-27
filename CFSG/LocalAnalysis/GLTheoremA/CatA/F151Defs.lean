module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeWSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.I171

structure Shape15Cfg {G : Type} [Group G] [Finite G] (p : ℕ) (L J E : Subgroup G) (d : G) :
    Prop where
  prime : p.Prime
  odd : p ≠ 2
  qs : CFSG.IsQuasisimple ↥L
  chev2 : IsChevSimple 2 (PSimple p L)
  elem : CFSG.Open.IsElemAbelian p E
  card : Nat.card E = p ^ 2
  normalizes : E ≤ Subgroup.normalizer (L : Set G)
  idiag : InnDiagOn p E L
  faithful : E ⊓ Subgroup.centralizer (L : Set G) = ⊥
  d_mem : d ∈ E
  d_ne : d ≠ 1
  pcomp : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J

@[expose] def CharTwoOf (F : TauCeti.LieTypeIndex → Prop) : TauCeti.LieTypeIndex → Prop :=
  fun i => F i ∧ i.characteristic = 2

@[expose] def isSympIdx : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | .C _ _ => True
  | _ => False

@[expose] def isOrthIdx : TauCeti.LieTypeIndex → Prop
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

@[expose] def OutHalf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J E : Subgroup G) (d b : G),
    Shape15Cfg p L J E d → b ∈ E → InducesInnerMod p L b ∨ I171LieShapeAt p L

@[expose] def NormHalf (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J E : Subgroup G) (d b : G),
    Shape15Cfg p L J E d → b ∈ E → catalogIs (PSimple p L) (onLie F) → ¬ I171LieShapeAt p L →
      InducesInnerMod p L b → b ∈ Subgroup.normalizer (J : Set G)

@[expose] def DiagHalf (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    T171Sh.WSetup p L J A d b → catalogIs (PSimple p L) (onLie F) → ¬ I171LieShapeAt p L →
      InducesInnerMod p L b → InnDiagOn p (Subgroup.zpowers b) J

@[expose] def CompHalf (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J E : Subgroup G) (d b : G),
    Shape15Cfg p L J E d → b ∈ E → catalogIs (PSimple p L) (onLie F) → ¬ I171LieShapeAt p L →
      InducesInnerMod p L b →
        b ∈ Subgroup.normalizer (J : Set G) ∧ InnDiagOn p (Subgroup.zpowers b) J

@[expose] def AmbigHalf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J E : Subgroup G) (d b : G),
    Shape15Cfg p L J E d → b ∈ E → catalogIs (PSimple p L) (ambiguousChev 2) →
      ¬ I171LieShapeAt p L → InducesInnerMod p L b →
        b ∈ Subgroup.normalizer (J : Set G) ∧ InnDiagOn p (Subgroup.zpowers b) J

@[expose] def ShapeModelAt (R : Type) [Group R] [Finite R] (p : ℕ) : Prop :=
  ∀ x y : R, x ≠ 1 → x ^ p = 1 → y ^ p = 1 → Commute x y →
    ∀ J : Subgroup R, GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J →
      y ∈ Subgroup.normalizer (J : Set R) ∧ InnDiagOn p (Subgroup.zpowers y) J

@[expose] def ShapeModelNormAt (R : Type) [Group R] [Finite R] (p : ℕ) : Prop :=
  ∀ x y : R, x ≠ 1 → x ^ p = 1 → y ^ p = 1 → Commute x y →
    ∀ J : Subgroup R, GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J →
      y ∈ Subgroup.normalizer (J : Set R)

@[expose] def ShapeModelDiagAt (R : Type) [Group R] [Finite R] (p : ℕ) : Prop :=
  ∀ x y : R, x ≠ 1 → x ^ p = 1 → y ^ p = 1 → Commute x y →
    ∀ J : Subgroup R, GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J →
      y ∈ Subgroup.normalizer (J : Set R) → InnDiagOn p (Subgroup.zpowers y) J

@[expose] def SimpleModel (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 →
    catalogIs S (onLie F) → ¬ catalogIs S (onLie (I171LieShape p)) → ShapeModelAt S p

@[expose] def isTwE6Idx : TauCeti.LieTypeIndex → Prop
  | .twistedE6 _ => True
  | _ => False

@[expose] def isReeF4Idx : TauCeti.LieTypeIndex → Prop
  | .reeF4 _ => True
  | _ => False

@[expose] def isSuzTitsIdx : TauCeti.LieTypeIndex → Prop
  | .suzuki _ => True
  | .tits => True
  | _ => False

@[expose] def SympModel : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ n → ¬ (n = 2 ∧ Nat.card K = 2) →
    Nat.card K = 2 ^ m → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ShapeModelAt ↥(CFSG.Assembly.LargeEvenSpGroup K n) p

@[expose] def OrthPlusModel : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → Nat.card K = 2 ^ m →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ShapeModelAt (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
        (CFSG.Assembly.LargeEvenQPlus K n))) p

@[expose] def OrthMinusModel : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → Nat.card K = 2 ^ m →
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ShapeModelAt (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
          (CFSG.Assembly.LargeEvenQMinus (n - 1) b c))) p

@[expose] def SympNorm : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ n → ¬ (n = 2 ∧ Nat.card K = 2) →
    Nat.card K = 2 ^ m → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ShapeModelNormAt ↥(CFSG.Assembly.LargeEvenSpGroup K n) p

@[expose] def SympDiag : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ n → ¬ (n = 2 ∧ Nat.card K = 2) →
    Nat.card K = 2 ^ m → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ShapeModelDiagAt ↥(CFSG.Assembly.LargeEvenSpGroup K n) p

@[expose] def OrthPlusNorm : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → Nat.card K = 2 ^ m →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ShapeModelNormAt (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
        (CFSG.Assembly.LargeEvenQPlus K n))) p

@[expose] def OrthPlusDiag : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → Nat.card K = 2 ^ m →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ShapeModelDiagAt (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
        (CFSG.Assembly.LargeEvenQPlus K n))) p

@[expose] def OrthMinusNorm : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → Nat.card K = 2 ^ m →
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ShapeModelNormAt (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
          (CFSG.Assembly.LargeEvenQMinus (n - 1) b c))) p

@[expose] def OrthMinusDiag : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → Nat.card K = 2 ^ m →
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ShapeModelDiagAt (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
          (CFSG.Assembly.LargeEvenQMinus (n - 1) b c))) p

@[expose] def LinNormModel : Prop :=
  ∀ (N m : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ N → Nat.card K = 2 ^ m →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.gcd N (2 ^ m - 1) →
      ShapeModelNormAt
        (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin N) K)) p

@[expose] def UniNormModel : Prop :=
  ∀ (N n : ℕ) (K : Type) [Field K] [Finite K],
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K → 3 ≤ N →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.gcd N (2 ^ n + 1) →
      ShapeModelNormAt
        (CFSG.Assembly.LargeEvenProj (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K N)) p

@[expose] def ShapeModelNormIso : Prop :=
  ∀ (R R' : Type) [Group R] [Finite R] [Group R'] [Finite R'] (_ : R ≃* R') (p : ℕ),
    ShapeModelNormAt R p → ShapeModelNormAt R' p

@[expose] def SimpleNormModel (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 →
    catalogIs S (onLie F) → ¬ catalogIs S (onLie (I171LieShape p)) → ShapeModelNormAt S p

@[expose] def SimpleDiagModel (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 →
    catalogIs S (onLie F) → ¬ catalogIs S (onLie (I171LieShape p)) → ShapeModelDiagAt S p

@[expose] def LinNormTrans : Prop :=
  ShapeModelNormIso → LinNormModel → SimpleNormModel (CharTwoOf KD264Lie.isLinearIdx)

@[expose] def UniNormTrans : Prop :=
  ShapeModelNormIso → UniNormModel → SimpleNormModel (CharTwoOf KD264Lie.isUnitaryIdx)

@[expose] def MarkTransport : Prop :=
  ∀ (G G' : Type) [Group G] [Finite G] [Group G'] [Finite G'] (p : ℕ) (J : Subgroup G)
    (J' : Subgroup G') (b : G) (b' : G') (e : PSimple p J ≃* PSimple p J'),
    commutator (PQuot p J) = ⊤ → b ∈ Subgroup.normalizer (J : Set G) →
      (∀ s s' : PSimple p J, indRelS p J b s s' → indRelS p J' b' (e s) (e s')) →
      InnDiagOn p (Subgroup.zpowers b') J' → InnDiagOn p (Subgroup.zpowers b) J

@[expose] def ShapeModelIso : Prop :=
  MarkTransport → ∀ (R R' : Type) [Group R] [Finite R] [Group R'] [Finite R'] (_ : R ≃* R')
    (p : ℕ), ShapeModelAt R p → ShapeModelAt R' p

@[expose] def ShapeModelDiagIso : Prop :=
  MarkTransport → ∀ (R R' : Type) [Group R] [Finite R] [Group R'] [Finite R'] (_ : R ≃* R')
    (p : ℕ), ShapeModelDiagAt R p → ShapeModelDiagAt R' p

@[expose] def RedSimple : Prop :=
  MarkTransport → ∀ F : TauCeti.LieTypeIndex → Prop, OutHalf → SimpleModel F → CompHalf F

@[expose] def RedSimpleNorm : Prop :=
  ∀ F : TauCeti.LieTypeIndex → Prop, OutHalf → SimpleNormModel F → NormHalf F

@[expose] def SympTrans : Prop :=
  ShapeModelIso → SympModel → SimpleModel (CharTwoOf isSympIdx)

@[expose] def OrthModelTrans : Prop :=
  ShapeModelIso → OrthPlusModel → OrthMinusModel → SimpleModel (CharTwoOf isOrthIdx)

structure ShapePieces : Prop where
  out : OutHalf
  amb : AmbigHalf
  lin : CompHalf (CharTwoOf KD264Lie.isLinearIdx)
  uni : CompHalf (CharTwoOf KD264Lie.isUnitaryIdx)
  symp : CompHalf (CharTwoOf isSympIdx)
  orth : CompHalf (CharTwoOf isOrthIdx)
  tri : CompHalf (CharTwoOf KD264Lie.isTrialityIdx)
  excU : CompHalf (CharTwoOf KD264Lie.isExcUntwistedIdx)
  excT : CompHalf (CharTwoOf KD264Lie.isExcTwistedIdx)

end CFSG.LocalAnalysis.GLTheoremA.F151

end
