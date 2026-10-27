module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Statements
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch6Skeleton

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem stmt6_1_27_of'_F4
    (h616 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ),
      Hyp611 G T M L V n →
        T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ IsNatModCh5 L ⁅V, L⁆ n)
    (h6115 : Stmt6_1_15_F4)
    (hno : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ),
      Hyp6116 G T M L V n → False) : Stmt6_1_27_F4 := by
  intro G _ _ T M L V n h
  obtain ⟨hCT, hnat⟩ := h616 G T M L V n h
  have hN := h.toNat hnat
  have hZS : Subgroup.centralizer (ch6ZS T L ⁅V, L⁆ : Set G) ≤ M := by
    by_contra hcon
    exact hno G T M L ⁅V, L⁆ n ⟨hN, hcon⟩
  rcases h6115 G T M L ⁅V, L⁆ n hN with hcon | ⟨rfl, h4⟩
  · exact absurd hZS hcon
  · exact ⟨rfl, ⟨hnat, hCT⟩, hZS, h4⟩

end CFSG.Quasithin.H13
