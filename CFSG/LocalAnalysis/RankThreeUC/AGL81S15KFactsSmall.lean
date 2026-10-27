module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
open scoped Pointwise

namespace KFactsSmall

@[expose] def innAut (S : Type) [Group S] : Subgroup (MulAut S) :=
  (MulAut.conj : S →* MulAut S).range

@[expose] def autInduced {G : Type} [Group G] (T E : Subgroup G) : Subgroup (MulAut ↥E) :=
  (T.subgroupOf (Subgroup.normalizer (E : Set G))).map E.normalizerMonoidHom

@[expose] def Permutable {G : Type} [Group G] (A B : Subgroup G) : Prop :=
  (A : Set G) * (B : Set G) = (B : Set G) * (A : Set G)

@[expose] def HasQ8 {H : Type} [Group H] (A : Subgroup H) : Prop :=
  ∃ Q : Subgroup H, Q ≤ A ∧ Nonempty (↥Q ≃* QuaternionGroup 2)

@[expose] def IsLThreeTwoPower (S : Type) [Group S] : Prop :=
  IsLThreeTwo S ∨ ∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧
    d.1 = .A 2 Q ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsLThreeTwoProd (k : ℕ) (J : Type) [Group J] : Prop :=
  ∃ (S : Type) (_ : Group S), IsLThreeTwo S ∧ Nonempty (J ≃* (Fin k → S))

@[expose] def IsL3FourCover (Kb : Type) [Group Kb] : Prop :=
  ∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.card = 4 ∧ d.1 = .A 2 Q ∧
    Nonempty ((Kb ⧸ Subgroup.center Kb) ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsTripleCoverA6 (L : Type) [Group L] : Prop :=
  CFSG.Open.IsQuasisimple L ∧ Nat.card (Subgroup.center L) = 3 ∧
    Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6))

@[expose] def commOn (V : Type) [Group V] (Z : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {x : V | ∃ g ∈ Z, ∃ v : V, x = v⁻¹ * g v}

@[expose] def IsK21dGroup (S : Type) [Group S] : Prop :=
  (∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower),
      ((Q.p = 2 ∧ (d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q ∨ d.1 = .twistedA 3 Q)) ∨
        (Q.card = 4 ∧ d.1 = .twistedA 4 Q)) ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    IsL5Two S ∨ IsUThreeThree S ∨
      ∃ n : ℕ, (n = 6 ∨ n = 8) ∧ Nonempty (S ≃* alternatingGroup (Fin n))

@[expose] def IsL3TwoModO2 {H : Type} [Group H] (A : Subgroup H) : Prop :=
  IsLThreeTwo (↥A ⧸ CFSG.pCore 2 ↥A)

end KFactsSmall

open KFactsSmall

@[expose] def K21a : Prop :=
  ∀ (Jh : Type) [Group Jh] [Finite Jh], CFSG.Open.IsQuasisimple Jh →
    (Nonempty ((Jh ⧸ Subgroup.center Jh) ≃* alternatingGroup (Fin 6)) ∨
      IsLThreeTwo (Jh ⧸ Subgroup.center Jh)) →
    ∀ E T' : Subgroup (MulAut Jh), Nat.card E = 9 →
      CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ innAut Jh) (innAut Jh) →
      Permutable E T' →
      False

@[expose] def K21b : Prop :=
  ∀ (Jh : Type) [Group Jh] [Finite Jh], CFSG.Open.IsQuasisimple Jh →
    IsLThreeTwoPower (Jh ⧸ Subgroup.center Jh) →
    ∀ E T' : Subgroup (MulAut Jh), CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      IsPGroup 2 T' → CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ innAut Jh) (innAut Jh) →
      Permutable E T' →
      HasQ8 (autInduced T' E) → False

@[expose] def K21c : Prop :=
  ∀ (J : Type) [Group J] [Finite J],
    (Nonempty (J ≃* alternatingGroup (Fin 7)) ∨ IsLThreeTwoProd 2 J ∨ IsLThreeTwoProd 3 J) →
    ∀ E : Subgroup (MulAut J), CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      ∃ x ∈ E, ∃ y ∈ E, orderOf x = 3 ∧ orderOf y = 3 ∧ ¬ IsConj x y

@[expose] def K21d : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsK21dGroup S →
    ∀ N T' R E : Subgroup (MulAut S),
      innAut S ≤ N → T' ≤ N → IsPGroup 2 T' →
      CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ innAut S) (innAut S) →
      R ≤ T' → T' ≤ Subgroup.normalizer (R : Set (MulAut S)) →
      R = CFSG.Open.pCoreOf 2 (N ⊓ Subgroup.normalizer (R : Set (MulAut S))) →
      Group.IsSolvable ↥(N ⊓ Subgroup.normalizer (R : Set (MulAut S))) →
      E ≤ N ⊓ Subgroup.normalizer (R : Set (MulAut S)) →
      CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 → HasQ8 (autInduced T' E) → False

@[expose] def KA6Z3 : Prop :=
  ∀ (V : Type) [Group V] [Finite V], (∀ a b : V, a * b = b * a) → (∀ v : V, v ^ 2 = 1) →
    ∀ L₁ L₂ : Subgroup (MulAut V), IsTripleCoverA6 ↥L₁ → IsTripleCoverA6 ↥L₂ →
      (∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) → L₁ ⊓ L₂ ≠ ⊥ →
      Nat.card (commOn V (L₁ ⊓ L₂)) ≤ 2 ^ 6 → False

@[expose] def K1525d : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
    CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → GNParabolic T T₁ T₂ →
    ∀ L : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf L ⊤ →
      gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) →
      (Nonempty (↥L ≃* alternatingGroup (Fin 8)) ∨ IsL5Two ↥L) →
      CFSG.Open.pRank 3 (gnA T T₁ L) ≤ 1 → CFSG.Open.pRank 3 (gnA T T₂ L) ≤ 1 →
      IsL3TwoModO2 (gnA T T₁ L) ∨ IsL3TwoModO2 (gnA T T₂ L)

@[expose] def K1528 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K D : Subgroup Y), K.Normal →
    ∀ (Kb : Type) [Group Kb] (π : ↥K →* Kb), Function.Surjective π →
      CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D →
      ((IsL3FourCover Kb ∧
          ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥((D.subgroupOf K).map π) → p = 2 ∨ p = 3) ∨
        (Nonempty (Kb ≃* alternatingGroup (Fin 11)) ∧
          Nonempty (↥((D.subgroupOf K).map π) ≃* Equiv.Perm (Fin 9)))) →
      False

end CFSG.LocalAnalysis.RankThreeUC.S15
