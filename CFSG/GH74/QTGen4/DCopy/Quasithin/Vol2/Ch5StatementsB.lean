module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

@[expose] def Stmt5_1_12_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D K₁ : Subgroup G) (n k : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsFieldParam510 T H k →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T →
    ∀ X : Subgroup G, InH H X →
      ∃ Kh₁ : Subgroup G, IsHatComp X K₁ Kh₁ ∧ oTwoUpper H ≤ conjClosure Kh₁ T ∧
        (oTwoUpper H = conjClosure Kh₁ T ∨
          (K₁ < oTwoUpper H ∧ LieModel (O2Q K₁) .PSL 2 2 2 ∧
            (IsSporadic .J1 (O2Q Kh₁) ∨
              ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
                IsPSL 2 p 1 (O2Q Kh₁))) ∨
          (SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
          (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧
            IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))) ∨
          (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ oTwoUpper H < conjClosure Kh₁ T ∧
            ¬ IsLieTypeChar2 (O2Q (conjClosure Kh₁ T)) ∧
            A314Statement (o2Img X T) (o2Img X (oTwoUpper H)) (o2Img X (conjClosure Kh₁ T))))

@[expose] def Stmt5_1_14_first_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      (quasithinIsMaximalLocal T (oTwoUpper H) ∧
          IsUniqueM H (Subgroup.normalizer (oTwoUpper H : Set G)) ∧
          ¬ quasithinIsFaithfulLocal T (oTwoUpper H)) ∧
        (⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
          ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 →
            Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G)) ∧
        quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥

@[expose] def Stmt5_1_15_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      D ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∨
      (n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n)) ∨
      ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n) ∨
      ((n = 4 ∨ n = 8) ∧ IsOrthCh5 L V n ∧
        ∀ Dm : Subgroup G, Dm ≤ D → Nat.card Dm = 2 ^ (n / 2) + 1 →
          Dm ≤ Subgroup.normalizer (oTwoUpper H : Set G))

@[expose] def Stmt5_1_16_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      ¬ 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)) ∧
      (¬ Group.IsSolvable ↥(centralizerModO2 (oTwoUpper H)) →
        (∃ k : ℕ, SuzukiModel (O2Q (perfectCore (centralizerModO2 (oTwoUpper H)))) 2 k) ∧
        ¬ perfectCore (centralizerModO2 (oTwoUpper H)) ≤ M ∧
        ¬ D ≤ Subgroup.normalizer (oTwoUpper H : Set G))

@[expose] def Stmt5_1_17_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → Even n

@[expose] def Stmt5_1_18_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
          D₃ = B ∧ ⁅quasithinOmegaOneCenter T, D₃⁆ = ⊥

@[expose] def Stmt5_1_19_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        (¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧
            ((n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n)) ∨
              ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n))) ∨
          ((n = 4 ∨ n = 8) ∧ IsOrthCh5 L V n ∧
            ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G)) ∨
          (n % 4 = 2 ∧ 2 < n ∧ ¬ 3 ∣ n ∧ D₃ = B ∧
            D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧ IsOrthCh5 L V n)

@[expose] def Stmt5_1_20_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧ pCoreOf 2 (H ⊔ D₃) = ⊥

@[expose] def Stmt5_1_21_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D D₃ Z₁ H₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
    H ≤ H₁ → H₁ ≤ Subgroup.centralizer (Z₁ : Set G) →
      ⁅conjClosure (conjClosure Z₁ D₃) H₁, pCoreOf 2 H₁⁆ ≤ Z₁ ∧
        frattiniOf (conjClosure (conjClosure Z₁ D₃) H₁) ≤ Z₁

@[expose] def Stmt5_1_22_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) =
          (T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) ⊔ B ∧
        Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤ M) ∧
      ((n = 2 ∨ n = 4) ∧
        (IsNatModCh5 L ⁅V, L⁆ n ∨ IsSumOfTwo L ⁅V, L⁆ (fun W => IsNatModCh5 L W n))) ∧
      (⁅conjClosure Z₁ D₃, pCoreOf 2 (oTwoUpper H)⁆ = Z₁ ∧
        Subgroup.normalizer (conjClosure Z₁ D₃ : Set G) ≤ Subgroup.normalizer
          ((D₃ ⊔ pCoreOf 2 (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) : Subgroup G) :
            Set G))

@[expose] def Stmt5_1_23_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))

@[expose] def StmtF11_5_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → Hyp111 L L₂ (sec52S M H)

end CFSG.Quasithin.H13
