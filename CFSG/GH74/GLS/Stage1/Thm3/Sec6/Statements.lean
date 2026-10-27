module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section Notation

variable {G : Type} [Group G]

@[expose] def Cond6a (S K : Subgroup G) : Prop :=
  ∀ s ∈ S, InducesFAut s K → s ∈ cSec K

@[expose] def Cond6b (S K : Subgroup G) : Prop := pRank 2 ↥(Qof S K) = 1

@[expose] def Is4_7b (z : G) (S F : Subgroup G) (y : G) : Prop :=
  y ∈ S ∧ orderOf y = 2 ∧ y ∉ Pz S z ⊔ F ∧ S = Pz S z ⊔ F ⊔ zpowers y

@[expose] def Is4_7U (S R : Subgroup G) (y : G) (U : Subgroup G) : Prop :=
  U ≤ R ∧ IVK.IsFourSubgroup U ∧ (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) ∧ ∀ v ∈ U, y * v = v * y

@[expose] def PGLQuot (z y : G) (K : Subgroup G) (Fq : Type) [Field Fq] : Prop :=
  ∃ _ : ((pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf (K ⊔ zpowers y)).Normal,
    Nonempty ((↥(K ⊔ zpowers y) ⧸ (pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf (K ⊔ zpowers y)) ≃*
      CFSG.GorensteinWalter.PGL2 Fq)

end Notation

structure Std6 (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop where
  simple : IsKProperSimple G
  rank : 3 ≤ pRank 2 G
  rank_le : pRank 2 G ≤ 4
  gen4 : Gen4 G
  classical : IsStronglyClassicalInvolution G z
  thm2 : ∃ t ∈ centralizer ({z} : Set G), IsConj z t ∧ t ∉ zStar (rigidProduct z)
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))
  kgh : KGH G

structure Std6r1 (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G) : Prop
    extends Std6 G z S where
  comps : {K' : Subgroup G | IsRigidRankOneComp z K'} = {K}

structure Std4r1 (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G) : Prop
    extends Std6r1 G z S K where
  F_le : F ≤ S
  Q_eq : Qz S z = F ⊓ Rz S z
  index_le : (Pz S z ⊔ F).relIndex S ≤ 2
  eq_of_2A7 : IsDoubleCoverOfAlt (HatT K) 7 → S = Pz S z ⊔ F
  inv_fAut : ∀ s ∈ S, orderOf s = 2 → InducesFAut s K → s ∈ Pz S z ⊔ F
  F_fAut : ∀ f ∈ F, InducesFAut f K

@[expose] def G2Data (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) : Prop :=
  (∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ p ^ f = q ∧
      LieModel Gs .G2 0 p f ∧ ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))) ∧
    (∀ v : G, orderOf v = 2 → IsConj z v) ∧
    HasSL2ProductOfIndexTwoStage1 (oPrimeResidual 2 (CentralizerBar z)) 3

@[expose] def G2Concl (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G) : Prop :=
  ∃ q : ℕ, (q % 8 = 3 ∨ q % 8 = 5) ∧ 5 ≤ q ∧
    (∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Nat.card Fq = q ∧
      Nonempty (HatT K ≃* IVK.SL2 Fq)) ∧
    IVK.IsQuaternionTwoGroup ↥(Pz S z) 3 ∧ IVK.IsQuaternionTwoGroup ↥(Qz S z) 3 ∧ G2Data G z S q

@[expose] def II4_4_quat : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (z : G), orderOf z = 2 →
    ∀ (S K : Subgroup G), CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)) →
      IsPCompIn 2 (centralizer ({z} : Set G)) K → pRank 2 ↥K = 1 →
        ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n

@[expose] def II4_ord4_lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (z : G), orderOf z = 2 →
    ∀ K : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) K → pRank 2 ↥K = 1 → z ∈ zStar K →
      ∀ a ∈ K, ∀ b ∈ K, a * a = z → b * b = z → ∃ k ∈ K, k * a * k⁻¹ = b

@[expose] def IVK_diag_unique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    ∀ s ∈ S, ∀ y ∈ S, s * s = 1 → y * y = 1 → s ∉ Rz S z → y ∉ Rz S z →
      ¬ InducesFAut s K → ¬ InducesFAut y K → s * y⁻¹ ∈ Rz S z

@[expose] def IVK_1_9_outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    ∀ y ∈ S, orderOf y = 2 → y ∉ Rz S z → ¬ InducesFAut y K →
      (∃ n, IVK.IsSemidihedralTwoGroup ↥(Pz S z ⊔ zpowers y) n) ∧
      ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Odd (Nat.card Fq) ∧
        Nonempty (HatT K ≃* IVK.SL2 Fq) ∧ PGLQuot z y K Fq

@[expose] def SD_facts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (z y : G),
    (∃ n, IVK.IsQuaternionTwoGroup ↥P n) → z ∈ P → z * z = 1 → z ≠ 1 → y * y = 1 → y ∉ P →
    (∀ p ∈ P, y * p * y⁻¹ ∈ P) → (∃ n, IVK.IsSemidihedralTwoGroup ↥(P ⊔ zpowers y) n) →
      (∀ p ∈ P, y * p = p * y → p = 1 ∨ p = z) ∧
      (∀ v ∈ P, (v * y) * (v * y) = 1 → ∃ p ∈ P, p⁻¹ * y * p = v * y)

@[expose] def Rnormal4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    Qz S z ≠ zpowers z →
      ∃ U : Subgroup G, U ≤ Rz S z ∧ IVK.IsFourSubgroup U ∧ ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U

@[expose] def IVK_1_19_V : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    IsCyclic ↥F → HasSL2Model (HatT K) Odd →
      ∀ s ∈ Pz S z ⊔ F, s ∉ Rz S z → ∀ V : Subgroup G, V ≤ Pz S z → IsCyclic ↥V →
        V.relIndex (Pz S z) = 2 → ∃ v ∈ V, s * v ≠ v * s

@[expose] def Z_not_sq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    Qz S z = F → ∀ y ∈ S, IsConj z y → y ∉ Rz S z → ∀ w : G, w * y = y * w → w * w ≠ z

@[expose] def IA_4_5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    Qz S z = F → (∃ n, IVK.IsQuaternionTwoGroup ↥F n) →
      ∀ y ∈ S, orderOf y = 2 → y ∉ Rz S z → S = Rz S z ⊔ zpowers y →
        (∃ n, IVK.IsSemidihedralTwoGroup ↥(Pz S z ⊔ zpowers y) n) →
        (∃ n, IVK.IsSemidihedralTwoGroup ↥(Qz S z ⊔ zpowers y) n) →
        Nat.card ↥(Pz S z) = Nat.card ↥(Qz S z) →
        ∀ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Nonempty (HatT K ≃* IVK.SL2 Fq) →
          ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧
            p ^ f = Nat.card Fq ∧ LieModel Gs .G2 0 p f ∧
            ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))

@[expose] def Prop4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F → ¬ IsCyclic ↥F

@[expose] def Lemma4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F → IsCyclic ↥F →
    HasSL2Model (HatT K) Odd ∧ (∃ y, Is4_7b z S F y) ∧
    ∀ y, Is4_7b z S F y →
      ((∃ n, IVK.IsSemidihedralTwoGroup ↥(Pz S z ⊔ zpowers y) n) ∧
        ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Odd (Nat.card Fq) ∧
          Nonempty (HatT K ≃* IVK.SL2 Fq) ∧ PGLQuot z y K Fq) ∧
      IsNonabelianMaximalClassTwoGroup ↥(Qz S z ⊔ zpowers y) ∧
      (∀ s ∈ S, s * s = 1 → s ∈ Rz S z ⊔ zpowers y) ∧
      ∃ U : Subgroup G, Is4_7U S (Rz S z) y U

@[expose] def Lemma4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F → IsCyclic ↥F →
    ∀ y, Is4_7b z S F y → ∀ U : Subgroup G, Is4_7U S (Rz S z) y U →
      ∀ u ∈ U, u ∉ zpowers z → ¬ IsConj z u

@[expose] def Prop4_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    Qz S z = F → (∃ n, IVK.IsQuaternionTwoGroup ↥F n) → G2Concl G z S K

@[expose] def IVK_1_19_lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ t ∈ S, orderOf t = 2 →
      ∀ W : Subgroup G, W ≤ S ⊓ K → (∃ n, IVK.IsQuaternionTwoGroup ↥W n) →
        (∀ w ∈ W, t * w = w * t) → InducesFAut t K

@[expose] def IVK_1_4a_quat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ a ∈ S, orderOf a = 2 → InducesFAut a K →
      CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K ⊓ centralizer ({a} : Set G))
        (K ⊓ centralizer ({a} : Set G)) →
        ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K ⊓ centralizer ({a} : Set G)) n

@[expose] def IVK_1_4hij_outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a (S1 S K) K →
      (Pof S K ⊔ Qof S K).relIndex (S1 S K) ≤ 2 ∧
      (IsDoubleCoverOfAlt (HatT K) 7 → S1 S K = Pof S K ⊔ Qof S K) ∧
      ∃ _ : ((Qof S K).subgroupOf (S1 S K)).Normal,
        (∃ n, IVK.IsDihedralTwoGroup (↥(S1 S K) ⧸ (Qof S K).subgroupOf (S1 S K)) n) ∨
        ∃ n, IVK.IsSemidihedralTwoGroup (↥(S1 S K) ⧸ (Qof S K).subgroupOf (S1 S K)) n

@[expose] def Quat_normal_index : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Y : Subgroup G), Y ≤ X → (∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) →
    (∃ n, IVK.IsQuaternionTwoGroup ↥X n) → (∃ n, IVK.IsQuaternionTwoGroup ↥Y n) → Y.relIndex X ≤ 2

@[expose] def Lemma6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    ∀ a ∈ S, orderOf a = 2 →
      CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({a} : Set G)) (Cz z ⊓ centralizer ({a} : Set G)) →
      (∃ K : Subgroup G, IsRigidRankOneComp z K ∧ InducesFAut a K) →
        ∀ t ∈ S, t * a = a * t → (∀ s ∈ S, s * a = a * s → s * t = t * s) → IsConj z t → t = z

@[expose] def Lemma6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    ∀ a ∈ S, orderOf a = 2 →
      CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({a} : Set G)) (Cz z ⊓ centralizer ({a} : Set G)) →
      (∃ K : Subgroup G, IsRigidRankOneComp z K ∧ InducesFAut a K) →
        CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({a} : Set G)) (centralizer ({a} : Set G)) ∧
        ∀ g : G, g⁻¹ * a * g ∈ S →
          CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({g⁻¹ * a * g} : Set G))
            (centralizer ({g⁻¹ * a * g} : Set G)) →
          conjugate (S ⊓ centralizer ({a} : Set G)) g = S ⊓ centralizer ({g⁻¹ * a * g} : Set G) →
            g ∈ Cz z

@[expose] def Lemma6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    Cond6a S K → Cond6b S K → G2Concl G z S K

@[expose] def Lemma6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Cond6a S K₁ → Cond6a S K₂ → ¬ IsDoubleCoverOfAlt (HatT K₁) 7 ∧ ¬ IsDoubleCoverOfAlt (HatT K₂) 7

@[expose] def Prop6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    (∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K) ∧
    (∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6b S K) ∧
    (∀ K : Subgroup G, {K' : Subgroup G | IsRigidRankOneComp z K'} = {K} → G2Concl G z S K) ∧
    (∀ K : Subgroup G, IsRigidRankOneComp z K → ¬ IsDoubleCoverOfAlt (HatT K) 7)

@[expose] def Prop6_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Cond6a S K₁ → Cond6a S K₂ → Cond6b S K₁ → Cond6b S K₂ →
      ((∃ n, IVK.IsQuaternionTwoGroup ↥(Qof S K₁) n) ∧ (∃ n, IVK.IsQuaternionTwoGroup ↥(Qof S K₂) n) ∧
        (Pof S K₂).relIndex (Qof S K₁) ≤ 2 ∧ (Pof S K₁).relIndex (Qof S K₂) ≤ 2) ∧
      ((S1 S K₁).relIndex S ≤ 2 ∧ (Pz S z).relIndex (S1 S K₁) ≤ 4) ∧
      (∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∃ _ : ((Qof S K).subgroupOf (S1 S K₁)).Normal,
        (∃ n, IVK.IsDihedralTwoGroup (↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁)) n) ∨
        ∃ n, IVK.IsSemidihedralTwoGroup (↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁)) n) ∧
      ((Pz S z).relIndex (S1 S K₁) = 4 →
        (∃ _ : ((Pz S z).subgroupOf (S1 S K₁)).Normal,
          Nonempty ((↥(S1 S K₁) ⧸ (Pz S z).subgroupOf (S1 S K₁)) ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
        S1 S K₁ = Qof S K₁ ⊔ Qof S K₂)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
