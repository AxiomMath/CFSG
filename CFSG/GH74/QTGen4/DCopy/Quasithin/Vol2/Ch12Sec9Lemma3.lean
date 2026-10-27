module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma12_9_3One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ∃ K₁ : Subgroup G, lOne L V₁ ≤ K₁ ∧
        quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) ∧
        Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G)

theorem lemma12_9_3_one_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Lemma12_9_3One_F4 := by
  intro G _ _ T L V n hcx V₁ hV₁
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  exact exists_cComp_normalizer_ge_lOne_F4 h1222 h37 h38 h39 hcx.hyp hn hV₁

end CFSG.Quasithin.H13
