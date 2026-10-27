module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding KFactsPair

@[expose] def IsLieIdx (S : Type) [Group S] (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, P d.1 ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsLieIdxOver (S : Type) [Group S] (f : TauCeti.PrimePower → TauCeti.LieTypeIndex)
    (c : ℕ → Prop) : Prop :=
  ∃ Q : TauCeti.PrimePower, Q.p = 2 ∧ c Q.card ∧ IsLieIdx S (fun d => d = f Q)

@[expose] def IsGTwo (c : ℕ → Prop) (S : Type) [Group S] : Prop :=
  IsLieIdxOver S TauCeti.LieTypeIndex.G2 c ∨ (c 2 ∧ IsUThreeThree S)

@[expose] def IsSpFour (c : ℕ → Prop) (S : Type) [Group S] : Prop :=
  IsLieIdxOver S (TauCeti.LieTypeIndex.B 2) c ∨
    (c 2 ∧ Nonempty (S ≃* alternatingGroup (Fin 6)))

@[expose] def IsLFour (c : ℕ → Prop) (S : Type) [Group S] : Prop :=
  IsLieIdxOver S (TauCeti.LieTypeIndex.A 3) c ∨
    (c 2 ∧ Nonempty (S ≃* alternatingGroup (Fin 8)))

@[expose] def IsUFour (c : ℕ → Prop) (S : Type) [Group S] : Prop :=
  IsLieIdxOver S (TauCeti.LieTypeIndex.twistedA 3) c

@[expose] def IsSpSix (c : ℕ → Prop) (S : Type) [Group S] : Prop :=
  IsLieIdxOver S (TauCeti.LieTypeIndex.B 3) c

@[expose] def IsOmegaEightMinus (c : ℕ → Prop) (S : Type) [Group S] : Prop :=
  IsLieIdxOver S (TauCeti.LieTypeIndex.twistedD 4) c

@[expose] def IsSLThreeOver (c : ℕ → Prop) (S : Type) [Group S] : Prop :=
  ∃ n : ℕ, 0 < n ∧ c (2 ^ n) ∧
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))

@[expose] def IsLinTwo (m : ℕ) (S : Type) [Group S] : Prop :=
  IsLieIdxOver S (TauCeti.LieTypeIndex.A (m - 1)) (fun Q => Q = 2)

@[expose] def IsUFiveFour (S : Type) [Group S] : Prop :=
  IsLieIdxOver S (TauCeti.LieTypeIndex.twistedA 4) (fun Q => Q = 4)

@[expose] def IsGroupOf1512 (S : Type) [Group S] : Prop :=
  IsAltSixCoverThree S ∨ Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (S ≃* alternatingGroup (Fin 10)) ∨ IsGTwo (fun _ => True) S ∨
    IsSLThreeOver (fun _ => True) S ∨ IsLFour (fun _ => True) S ∨ IsUFour (fun _ => True) S ∨
    IsSpFour (fun _ => True) S ∨ IsSpSix (fun _ => True) S ∨
    IsOmegaEightMinus (fun _ => True) S ∨
    IsLinTwo 5 S ∨ IsLinTwo 6 S ∨ IsLinTwo 7 S ∨ IsUFiveFour S

@[expose] def Row1511 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  3 ∉ sigmaM G M

@[expose] def RowLifts (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M)), GNYComponent (T.subgroupOf M) T₁ T₂ Ls →
    ∃ L : Subgroup ↥M, LiftOf (T.subgroupOf M) L Ls

@[expose] def Row1512 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      IsGroupOf1512 ↥Ls ∧ (IsUFiveFour ↥Ls → 5 ∉ sigmaM G M)

@[expose] def Row1513 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      2 < CFSG.Open.pRank p L →
        IsSpSix (fun Q => p ∣ Q + 1) ↥Ls ∨ IsOmegaEightMinus (fun Q => p ∣ Q + 1) ↥Ls

@[expose] def Row1514 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      CFSG.Open.pRank p L = 2 →
        (IsGTwo (fun Q => p ∣ Q + 1) ↥Ls ∨ IsSpFour (fun Q => p ∣ Q + 1) ↥Ls ∨
            IsLFour (fun Q => p ∣ Q + 1) ↥Ls) ∨
          ((IsLinTwo 6 ↥Ls ∨ IsLinTwo 7 ↥Ls) ∧ p = 7) ∨
          (Nonempty (↥Ls ≃* alternatingGroup (Fin 10)) ∧ p = 5)

@[expose] def IsCentralProdA6Z3 (S : Type) [Group S] : Prop :=
  ∃ K₁ K₂ : Subgroup S, IsAltSixCoverThree ↥K₁ ∧ IsAltSixCoverThree ↥K₂ ∧ K₁ ⊔ K₂ = ⊤ ∧
    K₁ ≤ Subgroup.centralizer (K₂ : Set S) ∧ K₁ ⊓ K₂ = centerIn K₁ ∧ K₁ ⊓ K₂ = centerIn K₂

@[expose] def Row1515 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      ∀ J : Subgroup ↥M, J = Subgroup.normalClosure (L : Set ↥M) →
        L = J ∨ IsCentralProdA6Z3 ↥(barO2 J) ∨
          (IsLThreeOfExp 1 ↥(barO2 L) ∧ Set.ncard {L' : Subgroup ↥M | IsC2 L' ∧ L' ≤ J} ≤ 3)

@[expose] def Row1516 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      Nonempty (↥Ls ≃* alternatingGroup (Fin 10)) → 5 ∉ sigmaM G M

@[expose] def cMBar {X : Type} [Group X] [Finite X] (L : Subgroup X) :
    Subgroup (X ⧸ CFSG.pCore 2 X) :=
  Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X))

@[expose] def cMHat {X : Type} [Group X] [Finite X] (L : Subgroup X) : Subgroup X :=
  (cMBar L).comap (QuotientGroup.mk' (CFSG.pCore 2 X))

@[expose] def Row1517 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      ((IsLinTwo 6 ↥Ls ∨ IsLinTwo 7 ↥Ls) → p ≠ 7) ∧
        ¬ (IsSpSix (fun Q => p ∣ Q + 1) ↥Ls ∨ IsOmegaEightMinus (fun Q => p ∣ Q + 1) ↥Ls)

@[expose] def Row1518 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      CFSG.Open.pRank p L < 3

@[expose] def Row1519 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      CFSG.Open.pRank p L ≤ 1

@[expose] def Row1520 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      (∃ I : Subgroup ↥M, I ≤ cMHat L ∧ CFSG.IsPComponent p (I.subgroupOf (cMHat L)) ∧
          CFSG.Open.pRank p I = 1 ∧ 1 ≤ CFSG.Open.pRank 3 I) ∧
        1 < CFSG.Open.pRank p (cMBar L) ∧ CFSG.Open.pRank 3 L < 3 ∧
        ¬ (IsSpSix (fun _ => True) ↥Ls ∨ IsOmegaEightMinus (fun _ => True) ↥Ls ∨
            IsLinTwo 6 ↥Ls ∨ IsLinTwo 7 ↥Ls ∨ Nonempty (↥Ls ≃* alternatingGroup (Fin 10))) ∧
        ¬ IsLFour (fun Q => ¬ 3 ∣ Q + 1) ↥Ls ∧ ¬ IsUFour (fun Q => ¬ 3 ∣ Q - 1) ↥Ls

@[expose] def IsLThreeTwoSq (S : Type) [Group S] : Prop :=
  ∃ (P : Type) (_ : Group P), IsLThreeOfExp 1 P ∧ Nonempty (S ≃* P × P)

@[expose] def IsLThreeTwoCube (S : Type) [Group S] : Prop :=
  ∃ (P : Type) (_ : Group P), IsLThreeOfExp 1 P ∧ Nonempty (S ≃* P × P × P)

@[expose] def Row1521 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ A R H' : Subgroup G, L34Config M A T R H' →
    ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
        L.Normal ∧ IsLThreeOdd ↥Ls ∧ ⁅Ls, gnImg (T.subgroupOf M) (A.subgroupOf M)⁆ = ⊥

@[expose] def Row1522 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      ∀ J : Subgroup ↥M, J = Subgroup.normalClosure (L : Set ↥M) →
        ∀ Js : Subgroup (↥M ⧸ gnC (T.subgroupOf M)), Js = gnImg (T.subgroupOf M) J →
          IsLThreeOfExp 1 ↥Js ∨
            ((IsLThreeTwoSq ↥Js ∨ IsLThreeTwoCube ↥Js) ∧ sigmaM G M = {7}) ∨
            (Nonempty (↥Js ≃* alternatingGroup (Fin 6)) ∨
              Nonempty (↥Js ≃* alternatingGroup (Fin 8)) ∨ IsLinTwo 5 ↥Js ∨
              IsUThreeThree ↥Js) ∨
            (IsCentralProdA6Z3 ↥Js ∧ sigmaM G M = {5})

@[expose] def Row1523Chev (G : Type) [Group G] [Finite G] (M T : Subgroup G)
    (T₁ T₂ : Subgroup ↥M) : Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) → ¬ IsLTwoTwoPow (↥Ls ⧸ Subgroup.center ↥Ls) →
        ∃ S₀ P : Subgroup (↥M ⧸ gnC (T.subgroupOf M)),
          CFSG.QuasithinUnique.IsSylowTwoOf S₀ Ls ∧ IsMinOverBorel Ls S₀ P ∧
            pElementSubgroup 2 (P.comap (toStar (T.subgroupOf M))) ≤
              Subgroup.centralizer ((gnV (T.subgroupOf M) ⊓ Subgroup.centralizer
                ((T.subgroupOf M ⊓ Subgroup.normalizer (L : Set ↥M) : Subgroup ↥M) : Set ↥M) :
                  Subgroup ↥M) : Set ↥M)

@[expose] def Row1523 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) → ¬ IsLTwoTwoPow (↥Ls ⧸ Subgroup.center ↥Ls) →
      (Nonempty (↥Ls ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree ↥Ls) →
        ∃ S₀ P : Subgroup (↥M ⧸ gnC (T.subgroupOf M)),
          CFSG.QuasithinUnique.IsSylowTwoOf S₀ Ls ∧ IsMinOverBorel Ls S₀ P ∧
            pElementSubgroup 2 (P.comap (toStar (T.subgroupOf M))) ≤
              Subgroup.centralizer ((gnV (T.subgroupOf M) ⊓ Subgroup.centralizer
                ((T.subgroupOf M ⊓ Subgroup.normalizer (L : Set ↥M) : Subgroup ↥M) : Set ↥M) :
                  Subgroup ↥M) : Set ↥M)

@[expose] def Row1524 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      ¬ IsAltSixCoverThree ↥Ls

@[expose] def Row1525 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  sigmaM G M = {7} ∧
    ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
        IsLThreeOfExp 1 ↥Ls

@[expose] def cMLStar {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (Ls : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  (Subgroup.centralizer (Ls : Set (X ⧸ gnC T))).comap (toStar T)

@[expose] def yLifts {X : Type} [Group X] [Finite X] (T T₁ T₂ : Subgroup X) : Subgroup X :=
  ⨆ L ∈ CY T T₁ T₂, L

@[expose] def Row1527 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  IsLThreeOfExp 1 ↥(Ystar (T.subgroupOf M) T₁ T₂)

@[expose] def Row1528 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      ∀ I : Subgroup ↥M, I ≤ cMHat L → CFSG.IsPComponent p (I.subgroupOf (cMHat L)) →
        CFSG.Open.pRank p I = 1 → 1 ≤ CFSG.Open.pRank 3 I →
          ∀ Q A : Subgroup ↥M, CFSG.ABGLocalTools.IsSylowOf 3 Q I →
            CFSG.ABGLocalTools.IsSylowOf 3 A (yLifts (T.subgroupOf M) T₁ T₂) →
              CFSG.Open.rankThreeGamma 1 3 (Q.map M.subtype) ≤ M ∧ CFSG.Open.pRank 3 Q ≤ 2 ∧
                A.map M.subtype ∈ uniqueSet M

@[expose] def RowFinal (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  Subgroup.normalizer (T : Set G) ≤ M

end CFSG.LocalAnalysis.RankThreeUC.S15
