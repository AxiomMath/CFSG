module

public import CFSG.Quasithin.EmptyFaithful.S152XD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152UF112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152X

theorem input15208F112At_S5_D10_F4 (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207_F4) (hF204 : He9.Input15204F112) :
    Input15208F112At_F4 (Equiv.Perm (Fin 5)) (DihedralGroup 5) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hφ hq
  obtain ⟨φ⟩ := hφ
  exact (S5Ctx.mk hs hH (h1515 G T Mc M hs.qtfe hs.mf hs.ce) (h1519 G T Mc M hs.qtfe hs.mf hs.ce)
    hY₁ (h15207 G T Mc M hs Y₁ hY₁) : S5Ctx T Mc M H Y₁ φ).false_of_S5_small hF204 (Or.inl hq)

theorem input15208F112At_S5_Sz0_F4 (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207_F4) (hF204 : He9.Input15204F112) :
    Input15208F112At_F4 (Equiv.Perm (Fin 5)) ↥(CFSG.Open.Sz 0) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hφ hq
  obtain ⟨φ⟩ := hφ
  exact (S5Ctx.mk hs hH (h1515 G T Mc M hs.qtfe hs.mf hs.ce) (h1519 G T Mc M hs.qtfe hs.mf hs.ce)
    hY₁ (h15207 G T Mc M hs Y₁ hY₁) : S5Ctx T Mc M H Y₁ φ).false_of_S5_small hF204 (Or.inr hq)

@[expose] def Input15208F112Rest_F4 : Prop :=
  Input15208F112At_F4 (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)) ∧
  Input15208F112At_F4 (Equiv.Perm (Fin 3)) (DihedralGroup 5) ∧
  Input15208F112At_F4 (Equiv.Perm (Fin 3)) ↥(CFSG.Open.Sz 0) ∧
  Input15208F112At_F4 (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3))

theorem input15208F112_of_rest_F4 (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15206 : StageLemma15206_F4) (h15207 : StageLemma15207_F4) (hF204 : He9.Input15204F112)
    (hR : Input15208F112Rest_F4) : Input15208F112_F4 :=
  input15208F112_of_cases_F4 h15206 hR.1 hR.2.1 hR.2.2.1 hR.2.2.2
    (input15208F112At_S5_D10_F4 h1515 h1519 h15207 hF204) (input15208F112At_S5_Sz0_F4 h1515 h1519 h15207 hF204)

end CFSG.Quasithin
