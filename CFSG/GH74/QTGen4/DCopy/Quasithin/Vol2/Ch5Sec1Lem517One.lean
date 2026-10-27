module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517One
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SL2Model
open scoped MatrixGroups IsMulCommutative

@[expose] def Stmt5_1_7_one_A5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → ⁅V, thompsonJ T⁆ ≠ ⊥ → n = 2 → IsCommCentralSplit L T V →
    IsBarS5 L T V → IsS5ModCh5 L T ⁅V, L⁆ →
      Subgroup.normalizer (baum T : Set G) ≤ M

theorem stmt5_1_7_one_of_F4 (h512 : Stmt5_1_2_F4) (h432 : Stmt4_3_2_F4) (hnat : Stmt5_1_7_one_nat)
    (hA5 : Stmt5_1_7_one_A5_F4) : A5.Stmt5_1_7_one_F4 := by
  intro G _ _ T L M hs hnab hK hT hLmax hLf hlie hM hTM hLM hMN
  obtain ⟨n, hn2, hL2⟩ := hlie
  have h : Hyp5_0_1 G T M L n :=
    { simple := hs
      nonabelian := hnab
      qtke := hK
      sylow := hT
      maxTwoLocal := hM
      T_le := hTM
      maximal := hLmax
      faithful := hLf
      L_le := hLM
      normal := hMN
      two_le := hn2
      lie := hL2 }
  obtain ⟨V, hV⟩ := h.exists_isCh5Module
  rcases h512 G T M L V n h hV with ⟨-, -, -, -, hU⟩ | ⟨hJ, hnq⟩ |
      ⟨hJ, hn, hsplit, hbar, hS5⟩
  · exact hU.1.2
  · exact (h432 G T M L hs hnab hK hT hM hTM hLmax hLf hLM hMN ⟨n, hn2, hL2⟩).2 (baum T)
      inf_le_left (hnat G T M L V n h hV hJ hnq)
  · exact hA5 G T M L V n h hV hJ hn hsplit hbar hS5

end CFSG.Quasithin.H13
