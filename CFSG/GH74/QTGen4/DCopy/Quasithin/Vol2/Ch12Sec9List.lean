module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec9List

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma12_9_3K1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ∃ K₁ : Subgroup G, lOne L V₁ ≤ K₁ ∧
        quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) ∧
        Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) ∧
        (lOne L V₁ = K₁ ∨ IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
          (n = 4 ∧ IsList1293Three (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)))

end CFSG.Quasithin.H13
