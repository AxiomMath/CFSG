module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem517S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem exists_isHStar_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) :
    ∃ H : Subgroup G, IsHStar T M H := by
  obtain ⟨⟨-, -, huniq⟩, -, hH, -, -⟩ :=
    (h331 G T h.simple h.nonabelian h.qtke h.sylow).2 L h.maximal h.isQuasisimple
  rw [h.conjClosure_eq] at huniq hH
  have hM : M = Subgroup.normalizer (L : Set G) := huniq M h.maxTwoLocal h.sup_le_M
  rw [← hM] at hH
  exact hH

theorem lemma_5_1_3_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58)
    (h316 : Theorem316Statement) (h317 : AS317Sylow) (h512 : Stmt5_1_2_F4) (hq : Stmt5_1_3_qhat)
    (hV : IsCh5Module T L V) :
    IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨
      (n = 2 ∧ IsBarS5 L T V ∧ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T)) ∨
      IsNatQuotCh5 L ⁅V, L⁆ n ∨
      IsOrthCh5 L V n ∨
      (IsCommCentralSplit L T V ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆) := by
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  ·
    obtain ⟨H, hH⟩ := h.exists_isHStar_F4 h331
    have h318 := h.hyp318_F4 h331 hV hH
    have hZ : centerOf (L ⊔ T) = ⊥ := by
      rcases theorem318_three hC58 h317 h.simple h.nonabelian h.qtke h.sylow h318 with
        ⟨hJ', -⟩ | ⟨-, -, hZ⟩
      · exact absurd (le_inf (thompsonJ_le_self T) hJ) hJ'
      · exact hZ
    have hq2 := theorem318_one_of_316 h316 h.simple h.nonabelian h.qtke h.sylow h318
    rcases hq G T M L V n h hV hJ (h.module_inf_centralizer_eq_bot hV hZ) hq2 with
      h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  ·
    rcases h512 G T M L V n h hV with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, -, h3⟩
    · exact absurd (h1.trans inf_le_right) hJ
    · exact Or.inr (Or.inr (Or.inl h2.commutator))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))

end Hyp5_0_1

theorem stmt5_1_3_of_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow) (h512 : Stmt5_1_2_F4) (hq : Stmt5_1_3_qhat) : Stmt5_1_3_F4 :=
  fun _ _ _ _ _ _ _ _ h hV => h.lemma_5_1_3_F4 h331 hC58 h316 h317 h512 hq hV

end CFSG.Quasithin.H13
