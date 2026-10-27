module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Statements

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Stmt5_1_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V →
      T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) ∧
      (∀ H : Subgroup G, IsHStar T M H →
        MinParabolic H T (H ⊓ M) ∧ (1 < E1.nParam H → ¬ Group.IsSolvable ↥H ∧ SQTKGroup ↥H)) ∧
      (∀ H : Subgroup G, IsHStar T M H →
        Hyp315Base T M (L ⊔ T) H V ∧ Hyp315.CaseI M (L ⊔ T) H) ∧
      ∃ N : Subgroup G, MinParabolic (L ⊔ T) T N

@[expose] def Stmt5_1_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V →
      (thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
          L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
          L ⊔ T ≤ Subgroup.normalizer (baum T : Set G) ∧
          IsUniqueM (Subgroup.normalizer (thompsonJ T : Set G)) M ∧
          IsUniqueM (Subgroup.normalizer (baum T : Set G)) M) ∨
      (⁅V, thompsonJ T⁆ ≠ ⊥ ∧ IsNatQuotCh5 L V n) ∨
      (⁅V, thompsonJ T⁆ ≠ ⊥ ∧ n = 2 ∧ IsCommCentralSplit L T V ∧ IsBarS5 L T V ∧
        IsS5ModCh5 L T ⁅V, L⁆)

@[expose] def Stmt5_1_3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V →
      IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨
      (n = 2 ∧ IsBarS5 L T V ∧ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T)) ∨
      IsNatQuotCh5 L ⁅V, L⁆ n ∨
      IsOrthCh5 L V n ∨
      (IsCommCentralSplit L T V ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆)

@[expose] def Stmt5_1_5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H D : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsHStar T M H → Lin2.IsHallTwoPrimeOf D (borelL T L) →
      H ⊓ M ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
      H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (D ⊔ T) : Set G) ∧
      ((∃ K ∈ cComp H, E2.HasE22LieQuot K) → Group.IsSolvable ↥(H ⊓ M) ∧
        ∃ B : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ M) ∧
          B ≤ Subgroup.normalizer (D : Set G))

@[expose] def Stmt5_1_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H D : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → IsHStar T M H → Lin2.IsHallTwoPrimeOf D (borelL T L) →
    pCoreOf 2 (D ⊔ H) = ⊥ →
      Even n ∧
      ((n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∧
          ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) ∨
        ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) ∨
        (n = 2 ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆ ∧ centerOf H = ⊥) ∨
        (n % 4 = 0 ∧ IsOrthCh5 L V n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
          ∀ Dp Dm : Subgroup G, Dp ≤ D → Dm ≤ D → Nat.card Dp = 2 ^ (n / 2) - 1 →
            Nat.card Dm = 2 ^ (n / 2) + 1 →
              quasithinOmegaOneCenter T ≤ centerOf (Dm ⊔ H) ∧
                (pCoreOf 2 (Dp ⊔ H) ≠ ⊥ ∨ n = 4 ∨ n = 8)))

@[expose] def Stmt5_1_10_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D : Subgroup G) (n : ℕ), Hyp5_1_8 G T M L H n →
    IsNotation5_1_9 T M L H B D →
      ∃ k : ℕ, (2 ≤ k ∧ E1.nParam H ≤ k) ∧
        E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H) ∧
        Lin2.IsHallTwoPrimeOf B (M ⊓ oTwoUpper H) ∧
        ∃ K₁ : Subgroup G, quasithinIsCComponent K₁ H ∧ oTwoUpper H = conjClosure K₁ T ∧
          ((K₁ < oTwoUpper H ∧ (LieModel (O2Q K₁) .PSL 2 2 k ∨ SuzukiModel (O2Q K₁) 2 k)) ∨
            (K₁ = oTwoUpper H ∧ IsBenderCh5 k (O2Q (oTwoUpper H))) ∨
            (K₁ = oTwoUpper H ∧
              (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
              E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H)))

theorem Stmt5_1_10_F4.exists_fieldParam_F4 (h510 : Stmt5_1_10_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T M L H B D : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hN : IsNotation5_1_9 T M L H B D) : ∃ k : ℕ, IsFieldParam510 T H k := by
  obtain ⟨k, hk, -, -, K₁, hK₁, hKeq, hc⟩ := h510 G T M L H B D n hyp hN
  exact ⟨k, hk, K₁, hK₁, hKeq, hc⟩

@[expose] def Stmt5_1_11_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D : Subgroup G) (n : ℕ), Hyp5_1_8 G T M L H n →
    IsNotation5_1_9 T M L H B D →
      IsSylowTwoOf (pCoreOf 2 (M ⊓ H) ⊓ oTwoUpper H) (oTwoUpper H) ∧
      IsSylowTwoOf (pCoreOf 2 (M ⊓ H) ⊓ L) L ∧
      (IsLieRankTwoK T H →
        (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
            pCoreOf 2 (M ⊓ H) ≤ Subgroup.normalizer (P : Set G)) ∨
          (LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 ∧
            (oTwoUpper H ⊔ pCoreOf 2 H).relIndex (oTwoUpper H ⊔ pCoreOf 2 (M ⊓ H)) = 2 ∧
            E2.IsDiagramNontrivial (pCoreOf 2 (M ⊓ H)) (oTwoUpper H) (T ⊓ oTwoUpper H)))

end CFSG.Quasithin.H13
