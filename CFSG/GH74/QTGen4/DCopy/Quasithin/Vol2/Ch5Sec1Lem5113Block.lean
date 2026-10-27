module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Block
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_1_13_four_be_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      2 < n ∧ D ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) ∧
        ∃ V' : Subgroup G, IsCh5Module T L V' ∧ IsNatQuotCh5 L V' n

theorem stmt5_1_13_four_star_of_F4 (hbe : Stmt5_1_13_four_be_F4) : Stmt5_1_13_four_star_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax
  by_contra hZ
  obtain ⟨hn, hDK, V', hV', hnat⟩ := hbe G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  exact m.false_of_block ty hn hDK hV' hnat

end CFSG.Quasithin.H13
