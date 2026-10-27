module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.D2Params
public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.H13.StatementsFSU

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped IsMulCommutative Pointwise

@[expose] def Stmt3_2_5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    L = conjClosure L T →
      (∃ _ : IsMulCommutative ↥(conjClosure V₀ T),
        qhatOf (V := ↥(conjClosure V₀ T)) (autOn (L ⊔ T) (conjClosure V₀ T)) ≤ 2) ∧
      (∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))),
        qhatOf (V := ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
          (autOn (Subgroup.normalizer (L : Set G))
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) ≤ 2) ∧
      ((V₀ = conjClosure V₀ T ∧
          conjClosure V₀ T = conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) ∨
        (V₀ = conjClosure V₀ T ∧ V₀ ≤ T ∧ T ≤ Subgroup.normalizer (V₀ : Set G) ∧
          V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
          ∀ g ∈ Subgroup.normalizer (L : Set G), g ∉ Subgroup.normalizer (V₀ : Set G) →
            V₀ ⊓ CFSG.conjugate V₀ g = ⊥) ∨
        (V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
          ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
              Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 3 n) ∨
            (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
              Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* ↥(StatedSp 2 K)) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSp4 (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* alternatingGroup (Fin 6)) ∧
              ∃ _ : IsMulCommutative ↥V₀, AlternatingNatural (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 6) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃*
                Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 4 1) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃*
                Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 5 1) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* alternatingGroup (Fin 7)) ∧
              Nat.card V₀ = 2 ^ 4)) ∧
          (∃ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G)) ∧
          ∀ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G) →
            conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) =
                conjClosure V₀ T ∧
              conjClosure V₀ T = V₀ ⊔ CFSG.conjugate V₀ t ∧ V₀ ⊓ CFSG.conjugate V₀ t = ⊥ ∧
              ¬ IsXSectionIso₂ L V₀ ⊥ (CFSG.conjugate V₀ t) ⊥))

end CFSG.Quasithin.H13
