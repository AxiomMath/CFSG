module

public import CFSG.Quasithin.EmptyFaithful.S152NPairD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152N9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

open CFSG.Quasithin.S152N in

theorem stagePair152_of_F4
    (h15112 : StageLemma15112) (h15208 : StageLemma15208_F4)
    (hord : Input15209Order_F4) : StagePair152_F4 := by
  intro G _ _ T Mc M hs H hH
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hc := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have hTsyl := isSylowTwoOf_hStar hs hH
  obtain ⟨L, N, hs', hnc, -⟩ := S152Fin.exists_noncentral_of_series hc.chief (by norm_num : 1 ≤ 2)
  have hshape := hc.shape trivial L N hs' hnc
  obtain ⟨B, F₁, F₂, X₁, X₂, P⟩ := S152Fin.pairStep_of_shape hc.elemAbelian hs' ⟨φ⟩ hshape
  refine ⟨F₁ ⊔ pCoreOf 2 H, F₂ ⊔ pCoreOf 2 H, ?_⟩
  exact
    { le₁ := ⟨le_sup_right, sup_le P.F₁_le (pCoreOf_le 2 H)⟩
      le₂ := ⟨le_sup_right, sup_le P.F₂_le (pCoreOf_le 2 H)⟩
      iso₁ := P.iso₁
      iso₂ := P.iso₂
      comm := fun a ha b hb => P.comm_H ha hb
      inf_eq := P.inf_H
      swap := P.swap
      delta_le := S152Fin.delta_le_of P hnc hc hTsyl (hord G T Mc M hs H hH) }

end CFSG.Quasithin
