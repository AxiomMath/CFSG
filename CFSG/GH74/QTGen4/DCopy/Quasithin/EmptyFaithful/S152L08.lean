module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152L08A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152L08

@[expose] def Input15208F112_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      ¬ Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)) ∧
        ¬ Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))

theorem stageLemma15208_of_F4 (h1519 : StageLemma1519) (h15112 : StageLemma15112)
    (h15204 : StageLemma15204_F4) (h15206 : StageLemma15206_F4) (h15207 : StageLemma15207_F4)
    (hF : Input15208F112_F4) : StageLemma15208_F4 := by
  intro G _ _ T Mc M hs H hH
  have hc := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  obtain ⟨Y₁, hY₁⟩ := h15206 G T Mc M hs
  have c1519 := h1519 G T Mc M hs.qtfe hs.mf hs.ce
  have c15207 := h15207 G T Mc M hs Y₁ hY₁
  obtain ⟨L, N, hst, hnc, -⟩ :=
    S152Fin.exists_noncentral_of_series hc.chief (by norm_num : 1 ≤ 2)
  have hshape := hc.shape trivial L N hst hnc
  have hC := cSecIn_eq_pCoreOf hs hH c1519 c15207 hc.elemAbelian hst hshape
  obtain ⟨hNorm, h | h | h | h⟩ := hshape
  · have h1 := h.1
    rw [hC] at h1
    exact absurd (nonempty_oTwoQuot_equiv h1) (hF G T Mc M hs H hH).1
  · have h1 := h.1
    rw [hC] at h1
    exact absurd (nonempty_oTwoQuot_equiv h1) (hF G T Mc M hs H hH).2
  · have h1 := h.1
    rw [hC] at h1
    exact nonempty_oTwoQuot_equiv h1
  · have h1 := h.1
    rw [hC] at h1
    exact absurd (nonempty_oTwoQuot_equiv h1) (h15204 G T Mc M hs H hH)

end CFSG.Quasithin
