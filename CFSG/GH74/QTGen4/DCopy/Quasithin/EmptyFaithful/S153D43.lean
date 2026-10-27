module

public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D44

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def StageComponentOne_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 1 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) → ¬ CharTwo I → False

theorem stageComponentOne_of_inputs_F4 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h25 : Stage15325_F4) (h8 : Input15311Eight) (h5 : Input15311FiveII)
    (h33 : Stage15325_F4 → ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G]
      (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
      CtxComp T Mc M V₁ V₂ Yp I t → ∃ L : Subgroup G, Concl15333 T M V₁ Yp I L)
    (h34 : Input15334) (ho : Input15343Open) (hr : Input15343Reduce) (he : Input15343Elim) :
    StageComponentOne_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hrk I hI hmin hnc
  have c0 : CtxComp T Mc M V₁ V₂ Yp I t := ctxComp_of_inputs h8 h11 h113 h hI hnc
  obtain ⟨L, hL⟩ := h33 h25 G T Mc M V₁ V₂ Yp I t c0
  have c1 : CtxComp1 T Mc M V₁ V₂ Yp I L t :=
    { c0 with
      rank := hrk
      facts25 := S153D.facts15325_of_inputs h5 h11 h113 h hrk hI
      c33 := hL
      c34 := h34 G T Mc M V₁ V₂ Yp I L t c0 hL }
  have copen := ho G T Mc M V₁ V₂ Yp I L t c1
  obtain ⟨hYL, hSN⟩ := hr G T Mc M V₁ V₂ Yp I L t c1 copen
  obtain ⟨hN, hIeq⟩ := S153D.lemma_comp_I_eq_LS' c0 hL.mem hL.not_le hmin hSN hYL
  exact he G T Mc M V₁ V₂ Yp I L t c1 copen hmin hN hIeq hYL

end CFSG.Quasithin
