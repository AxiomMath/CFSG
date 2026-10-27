module

public import CFSG.Quasithin.Vol2.Ch12Sec2ChainStmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Stmt12_2_24_config_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
      ∃ (H P U I : Subgroup G) (h : G) (n p : ℕ), Config12_2_24 T L V H P U I h n p

@[expose] def Stmt12_2_25_26_of_config_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p →
      (Subgroup.normalizer (L : Set G) = L ∧ V = pCoreOf 2 L ∧ (n = 3 ∨ n = 4) ∧
        Nat.card (quasithinOmegaOneCenter T) = 2) ∧
      ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L

theorem stmt12_2_24_of_config_F4 (hc : Stmt12_2_24_config_F4) : Stmt12_2_24_F4 := by
  intro G _ _ T L V hH hE
  obtain ⟨H, P, U, I, h, n, p, hC⟩ := hc G T L V hH hE
  obtain ⟨-, -, hn, hV, -, hB, -⟩ := hC
  exact ⟨n, hn, hV, hB⟩

theorem stmt12_2_25_of_config_F4 (hc : Stmt12_2_24_config_F4) (h2526 : Stmt12_2_25_26_of_config_F4) :
    Stmt12_2_25_F4 := by
  intro G _ _ T L V hH hE
  obtain ⟨H, P, U, I, h, n, p, hC⟩ := hc G T L V hH hE
  obtain ⟨⟨hML, hVO, hn, hZ⟩, -⟩ := h2526 G T L V H P U I h n p hH hE hC
  obtain ⟨-, -, -, hV, -⟩ := hC
  refine ⟨hML, hVO, ?_, hZ⟩
  rcases hn with rfl | rfl
  · exact Or.inl hV
  · exact Or.inr hV

theorem stmt12_2_26_of_config_F4 (hc : Stmt12_2_24_config_F4) (h2526 : Stmt12_2_25_26_of_config_F4) :
    Stmt12_2_26_F4 := by
  intro G _ _ T L V hH hE
  obtain ⟨H, P, U, I, h, n, p, hC⟩ := hc G T L V hH hE
  exact (h2526 G T L V H P U I h n p hH hE hC).2

theorem stmt12_2_13_of_config_F4 (hc : Stmt12_2_24_config_F4) (h2526 : Stmt12_2_25_26_of_config_F4)
    (h27 : Stmt12_2_27_F4) : Stmt12_2_13_F4 :=
  stmt12_2_13_of_chain_F4 (stmt12_2_24_of_config_F4 hc) (stmt12_2_25_of_config_F4 hc h2526)
    (stmt12_2_26_of_config_F4 hc h2526) h27

end CFSG.Quasithin.H13
