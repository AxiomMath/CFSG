module

public import CFSG.Quasithin.EmptyFaithful.S153D35
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D44

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input15338_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → Concl15337 T V₁ Yp L → CFSG.Open.pRank 3 L = 2 → Yp ≤ L

@[expose] def StageComponentTwo_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) → ¬ CharTwo I → False

theorem stageComponentTwo_of_inputs_F4 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h25 : Stage15325_F4) (h8 : Input15311Eight)
    (h33 : Stage15325_F4 → ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G]
      (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
      CtxComp T Mc M V₁ V₂ Yp I t → ∃ L : Subgroup G, Concl15333 T M V₁ Yp I L)
    (h34 : Input15334)
    (h36 : Input15336One) (h37 : Input15337) (h38 : Input15338_F4) (h39 : Input15339)
    (h40 : Input15340) (hcl : Input15335Close) : StageComponentTwo_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr I hI hmin hnc
  have c0 : CtxComp T Mc M V₁ V₂ Yp I t := ctxComp_of_inputs h8 h11 h113 h hI hnc
  obtain ⟨L, hL⟩ := h33 h25 G T Mc M V₁ V₂ Yp I t c0
  have c1 : CtxComp2 T Mc M V₁ V₂ Yp I L t :=
    { c0 with
      rank := hr
      facts11 := S153D.facts15311_of_stages h11 h113 h hr hI
      s3s3 := h36 G T Mc M V₁ V₂ Yp t h hr I hI
      c33 := hL
      c34 := h34 G T Mc M V₁ V₂ Yp I L t c0 hL }
  have c37 := h37 G T Mc M V₁ V₂ Yp I L t c1
  have c38 := h38 G T Mc M V₁ V₂ Yp I L t c1 c37
  have c39 := h39 G T Mc M V₁ V₂ Yp I L t c1 c37 c38
  have c40 := h40 G T Mc M V₁ V₂ Yp I L t c1 c37 c38 c39
  obtain ⟨hN, hIeq⟩ := S153D.lemma_comp_I_eq_LS c0 hL.mem hL.not_le hmin c39 c40
  exact hcl G T Mc M V₁ V₂ Yp I L t c1 hmin hN hIeq c40

end CFSG.Quasithin
