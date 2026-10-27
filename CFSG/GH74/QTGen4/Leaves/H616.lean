module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem6

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public section

namespace CFSG.GH74.QTGen4.Leaves.H616

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open

theorem h616_F4_of (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ),
      Hyp611 G T M L V n →
        T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ IsNatModCh5 L ⁅V, L⁆ n :=
  fun _ _ _ _ _ _ _ _ h =>
    ⟨(Hyp611.lemma_6_1_6_one_two_F4 h331 h432 h512 h614 h615 h).1.2,
      (Hyp611.lemma_6_1_6_one_two_F4 h331 h432 h512 h614 h615 h).2.1⟩

end CFSG.GH74.QTGen4.Leaves.H616

end
