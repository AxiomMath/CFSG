module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Stmt5_1_7_two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → IsHStar T M H → ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ →
      L = ⁅L, thompsonJ T⁆ ∧ oTwoUpper H = ⁅oTwoUpper H, thompsonJ T⁆ ∧
      (pCoreOf 2 (borelL T L ⊔ H) ≠ ⊥ ∨
        (IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆ ∧ centerOf H = ⊥))

@[expose] def Stmt5_1_14_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → Concl5_1_14 T L V H B D n

@[expose] def Stmt5_2_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      IsWeakBNPair (sec52G1 M L H B L₂) (sec52G2 M H D L₂) ∧
      L₂ = oTwoUpper H ∧ oTwoUpper H = perfectCore (sec52G2 M H D L₂) ∧
      pCoreOf 2 (sec52G1 M L H B L₂) = pCoreOf 2 L ∧
      pCoreOf 2 (sec52G2 M H D L₂) = pCoreOf 2 (oTwoUpper H) ∧
      Cases5_2_6 (sec52Alpha M L H B D L₂) L (oTwoUpper H) n ∧
      pCoreOf 2 (oTwoUpper H ⊔ T) = pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) ∧
      ((sec52S M H ≤ L ∧ sec52S M H ≤ oTwoUpper H ∧
          pCoreOf 2 (L ⊔ sec52S M H) = pCoreOf 2 L ∧
          pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) = pCoreOf 2 (oTwoUpper H)) ∨
        (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧ IsU4ExtTwo m (sec52Alpha M L H B D L₂) ∧
          ∃ t : G, orderOf t = 2 ∧ t ∉ pCoreOf 2 (oTwoUpper H) ∧
            pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) =
              pCoreOf 2 (oTwoUpper H) ⊔ Subgroup.zpowers t ∧
            ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
              ∃ P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F),
                IsMaxParabolic2 ⊤ P ∧
                Nonempty (↥(oTwoUpper H ⊓ Subgroup.centralizer ({t} : Set G)) ≃*
                  ↥(perfectCore P))))

@[expose] def Stmt5_2_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      ((IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSL 3 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSp 2 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .G2 0 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .trialityD4 0 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .twistedF4 0 n)) ∨
        (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSU 4 m)) ∨
        (n = 4 ∧ IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSU 5 2))) ∧
      (L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) = L ⊔ B ⊔ D ∧
        D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H = oTwoUpper H ⊔ B ⊔ D ∧
        (L ⊔ B ⊔ D) ⊓ (oTwoUpper H ⊔ B ⊔ D) = (sec52S M H ⊓ L) ⊔ B ⊔ D ∧
        sec52S M H ⊓ L = T ⊓ L ∧ sec52S M H ⊓ L = T ⊓ oTwoUpper H ∧
        sec52S M H ⊓ L = pCoreOf 2 ((L ⊔ B ⊔ D) ⊓ (oTwoUpper H ⊔ B ⊔ D))) ∧
      (pCoreOf 2 L = pCoreOf 2 (L ⊔ B ⊔ D ⊔ T) ∧
        pCoreOf 2 (oTwoUpper H) = pCoreOf 2 (oTwoUpper H ⊔ B ⊔ D ⊔ T))

@[expose] def Stmt5_2_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      quasithinIsMaximalLocal T (oTwoUpper H) ∨
      (IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSL 3 2) ∧
        ∃ K' : Subgroup G, oTwoUpper H < K' ∧ quasithinIsMaximalLocal T K' ∧
          CFSG.Quasithin.IsExcA7Block K')

@[expose] def Stmt5_2_9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      (∃ f : ℕ, 2 ≤ f ∧
        (IsOfLieType52 M L H B D T .PSL 3 f ∨ IsOfLieType52 M L H B D T .PSp 2 f ∨
          IsOfLieType52 M L H B D T .G2 0 f ∨ IsOfLieType52 M L H B D T .trialityD4 0 f ∨
          IsOfLieType52 M L H B D T .twistedF4 0 f)) ∨
      (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧ IsOfLieType52 M L H B D T .PSU 4 m) ∨
      IsOfLieType52 M L H B D T .PSU 5 2 ∨
      IsOfTypeM23 M L H B D T

end CFSG.Quasithin.H13
