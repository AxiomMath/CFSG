module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.Gap6S1520
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152NBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Input15209Lift_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Concl319 T M (V154 T Mc M) H True →
      Nonempty (OTwoQuot H ≃* S152N.W3) → (deltaSet H (V154 T Mc M)).Nonempty →
      ∃ A : Subgroup G, IsMaxElemAbelian H A ∧ ¬ A ≤ pCoreOf 2 H ∧
        (A ⊓ pCoreOf 2 H).relIndex A = 2

theorem input15209Exists_of_lift_F4 (h15112 : StageLemma15112) (h15208 : StageLemma15208_F4)
    (hl : Input15209Lift_F4) : Input15209Exists_F4 := by
  intro G _ _ T Mc M hs H hH
  have hc : Concl319 T M (V154 T Mc M) H True :=
    (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have hsyl : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hne : (deltaSet H (V154 T Mc M)).Nonempty :=
    S152N.exists_mem_deltaSet hsyl hc.exists_A
  exact hl G T Mc M hs H hH hc (h15208 G T Mc M hs H hH) hne

end CFSG.Quasithin
