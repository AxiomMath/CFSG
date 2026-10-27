module

public import CFSG.GH74.Generic.S3.Conf
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.Generic.Lifting
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

@[expose] def NoCommInv {G : Type} [Group G] (S : Subgroup G) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a * a = 1 → b * b = 1 → a * b = b * a → a = 1 ∨ b = 1 ∨ a = b

structure Nbhd3 (G : Type) [Group G] [Finite G] (t t' : StatedLieTag) (p f : ℕ) (x y : G)
    (Iw Iv Ivw T : Subgroup G) : Prop where
  tag : t = .PSL ∨ t = .PSU
  tag' : t' = .PSL ∨ t' = .PSU
  prime : p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f
  x_inv : orderOf x = 2
  y_inv : orderOf y = 2
  comm : y * x = x * y
  ne : y ≠ x
  comp_w : IsNormCompC Iw x
  odd_w : Odd (Nat.card ↥(center ↥Iw))
  model_w : LieModel (↥Iw ⧸ center ↥Iw) t 3 p f
  T_sylow : IsSylowOf 2 T (centralizer ({x} : Set G))
  x_T : x ∈ T
  Q_rank : NoCommInv (T ⊓ centralizer (Iw : Set G))
  y_R : y ∈ T ⊓ Iw
  y_central : ∀ r ∈ T ⊓ Iw, r * y = y * r
  y_unique : ∀ z ∈ T ⊓ Iw, (∀ r ∈ T ⊓ Iw, r * z = z * r) → z * z = 1 → z = 1 ∨ z = y
  Iv_le : Iv ≤ Iw
  y_Iv : y ∈ Iv
  Iv_iso : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ Nonempty (SL(2, F) ≃* Iv)
  comp_v : IsCompC Iv y
  Iv_le_vw : Iv ≤ Ivw
  comp_vw : IsNormCompC Ivw (y * x)
  odd_vw : Odd (Nat.card ↥(center ↥Ivw))
  model_vw : LieModel (↥Ivw ⧸ center ↥Ivw) t' 3 p f
  rank_vw : NoCommInv (centralizer ({y * x} : Set G) ⊓ centralizer (Ivw : Set G))

@[expose] def B_L3_class : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime →
    p ≠ 2 → 5 ≤ p ^ f → ∀ L : Subgroup G, IsQuasisimple ↥L → Odd (Nat.card ↥(center ↥L)) →
      LieModel (↥L ⧸ center ↥L) t 3 p f →
      ∀ a ∈ L, ∀ b ∈ L, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → ∃ g ∈ L, g * a * g⁻¹ = b

@[expose] def B_L3_sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime →
    p ≠ 2 → 5 ≤ p ^ f → ∀ L : Subgroup G, IsQuasisimple ↥L → Odd (Nat.card ↥(center ↥L)) →
      LieModel (↥L ⧸ center ↥L) t 3 p f → ∀ R : Subgroup G, IsSylowOf 2 R L →
        IsCyclic ↥(R ⊓ centralizer (R : Set G)) ∧
        (t = .PSL → ∀ z ∈ R ⊓ centralizer (R : Set G), orderOf z ∣ p ^ f - 1) ∧
        (t = .PSU → ∀ z ∈ R ⊓ centralizer (R : Set G), orderOf z ∣ p ^ f + 1) ∧
        ∀ A : Subgroup G, A ≤ normalizer (L : Set G) → IsPGroup 2 ↥A → (∀ a ∈ A, ∀ r ∈ R, a * r = r * a) →
          ∀ a ∈ A, ∃ z ∈ R ⊓ centralizer (R : Set G), a * z⁻¹ ∈ centralizer (L : Set G)

@[expose] def B_L3_noNormalMinus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t t' : StatedLieTag) (p f : ℕ),
    (t = .PSL ∧ t' = .PSU) → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ L : Subgroup G, IsQuasisimple ↥L → Odd (Nat.card ↥(center ↥L)) →
      LieModel (↥L ⧸ center ↥L) t 3 p f → ∀ H S : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) →
        IsSylowOf 2 S H → ∀ M : Subgroup G, M ≤ S → (M.subgroupOf S).Normal →
          M ⊓ centralizer (L : Set G) = ⊥ →
          ∀ (G' : Type) [Group G'] [Finite G'] (L' R' : Subgroup G'), IsQuasisimple ↥L' →
            Odd (Nat.card ↥(center ↥L')) → LieModel (↥L' ⧸ center ↥L') t' 3 p f →
            IsSylowOf 2 R' L' → ¬ Nonempty (↥M ≃* ↥R')

end CFSG.GH74.Generic.S3
