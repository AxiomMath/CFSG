module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt13_3_4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      (V ⊓ Subgroup.centralizer (L : Set G) ≤ fsuV1 T V ∧
        Nat.card ↥(fsuV1 T V) = 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) ∧
        ∀ W : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ V →
          T ≤ Subgroup.normalizer (W : Set G) →
          Nat.card W = 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) → W = fsuV1 T V) ∧
      conjClosure (fsuV1 T V) L = V ∧
      ∀ X : Subgroup G, T ≤ X → X < L ⊔ T → IsTwoThreeGroup X

@[expose] def Stmt13_3_5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      ((Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel ↥(autOn L V) .PSU 3 3 1) →
        ∀ v ∈ V, v ≠ 1 →
          ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) →
        (∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
          H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
        ∀ z : G, Subgroup.zpowers z = fsuV1 T V →
          ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (IsA6On L V → ∃ v ∈ fsuV1 T V, v ∉ Subgroup.centralizer (L : Set G) ∧
        ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G))

@[expose] def Stmt13_3_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      ¬ g1 T V ≤ Subgroup.normalizer (L : Set G) ∨
        (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧ IsA6On L V ∧
          ∃ _ : IsMulCommutative ↥V, Nat.card V = 2 ^ 5 ∧
            FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn L V) ⊤ ⊥)

@[expose] def Stmt13_3_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V →
      ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) ∨
        (IsHatA6 L ∧ pRank 3 (Subgroup.centralizer (V : Set G)) = 1 ∧
          l0 L = orderThreeSubgroup (Subgroup.centralizer (V : Set G)))

@[expose] def Stmt13_3_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L K H Y : Subgroup G), QTH13 G T L →
    quasithinIsFaithfulLocal T K → InH T H → ¬ H ≤ Subgroup.normalizer (K : Set G) →
    oTwoRes Y = Y → Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ Subgroup.normalizer (K : Set G) →
      ¬ K ≤ Y ⊔ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K ∧
        IsTwoThreeGroup Y

@[expose] def Stmt13_3_9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H Y : Subgroup G) (v : G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V →
    InH T H → ¬ H ≤ Subgroup.normalizer (L : Set G) →
    oTwoRes Y = Y → Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
    v ∈ fsuV1 T V → v ∉ Subgroup.centralizer (L : Set G) →
    Y ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G) →
      Y = ⊥ ∨
        (autOn Y V = autOn (L₁Of L (fsuV1 T V)) V ∧
          (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
            Y = L₁Of L (fsuV1 T V)) ∧
          (IsHatA6 L → Y = l1plus T L V))

@[expose] def Stmt13_3_14_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ → IsV2 T V V₂ →
    IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) →
      ¬ pCoreOf 2 (g1 T V) ≤ Subgroup.centralizer (V₂ : Set G)

@[expose] def Stmt13_3_15_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ X I₂ : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ → IsV2 T V V₂ →
    IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) →
    (IsHatA6 L → X = oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆) → (¬ IsHatA6 L → X = L₁Of L V₂) →
    I₂ = conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (V₂ : Set G)) →
    Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (g1 T V) ∧
      I₂ ⊓ Subgroup.centralizer (V₂ : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pCoreOf 2 (g1 T V) ⊓ Subgroup.centralizer (V₂ : Set G) ≤ pCoreOf 2 I₂ ∧
      pCoreOf 2 I₂ ≤ pCoreOf 2 (Subgroup.normalizer (V₂ : Set G)) ∧
      pRank 3 (Subgroup.centralizer (V₂ : Set G)) ≤ 1 ∧
      ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ Subgroup.normalizer (V₃ : Set G) →
        Nat.card V₃ = 8 →
          Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
            (¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
              ⁅V, Subgroup.centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V)

end CFSG.Quasithin.H13.A6
