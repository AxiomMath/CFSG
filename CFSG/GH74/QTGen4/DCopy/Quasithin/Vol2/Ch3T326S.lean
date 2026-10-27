module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch3T326S

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

@[expose] def Stmt3_2_6C_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    L ≠ conjClosure L T →
      (∃ _ : IsMulCommutative ↥(conjClosure V₀ T),
        qhatOf (V := ↥(conjClosure V₀ T)) (autOn (conjClosure L T ⊔ T) (conjClosure V₀ T)) ≤ 2) ∧
      ∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        qhatOf (V := ↥(conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))))
          (autOn (Subgroup.normalizer (conjClosure L T : Set G))
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) ≤ 2 ∧
        ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
            LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 2 2 n ∧
            V₀ = conjClosure V₀ T ∧
            conjClosure V₀ T =
              conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
            (tensorNatModel 2 K).Realizes
              (V := ↥(conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G))))
              (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) ∨
          (LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 3 2 1 ∧
            V₀ = conjClosure V₀ T ∧
            conjClosure V₀ T =
              conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
            (tensorNatModel 3 (ZMod 2)).Realizes
              (V := ↥(conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G))))
              (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) ∨
          Concl326C3 T L V₀)

end CFSG.Quasithin.H13
