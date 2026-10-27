module

public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D31
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D44

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

theorem stage15325One_of_inputs_F4 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h5 : Input15311FiveII) (h26 : Input15326Two)
    (h27 : Input15327) (h28 : Input15328) (h30 : Input15330) (h31 : Input15331_F4)
    (h32 : Input15332) (hc : Input15325Count) : Stage15325One_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr I hI hchar
  have c0 : Ctx15325 T Mc M V₁ V₂ Yp I t := ⟨h, hI, hr, hchar⟩
  have hF0 : Facts153 T M V₁ Yp I := S153D.facts153_of_stages h11 h113 h hI
  obtain ⟨J, -, cJ, hmin⟩ := S153D.exists_minimal_counterexample c0 hF0
  have hFall : ∀ H : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M H →
      Facts15325 T Mc M V₁ V₂ Yp H := fun H hH =>
    S153D.facts15325_of_inputs h5 h11 h113 h hr hH
  have hFJ : Facts15325 T Mc M V₁ V₂ Yp J := hFall J cJ.inH
  obtain ⟨L, hL⟩ := S153D.lemma_15_3_26_two h26 h37 h38 cJ hFJ
  have c25L : Ctx15325L T Mc M V₁ V₂ Yp J L t := ⟨cJ, hFJ, hL⟩
  have hsolv : ∀ X : Subgroup G, X ≤ J → Group.IsSolvable ↥X →
      Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (X : Set G) → X ≤ M ⊓ J :=
    fun X hXI hXs hXn => S153D.lemma_15_3_26_three h113 h26 cJ hFJ hFall hXI hXs hXn
  have c27ctx : Ctx15327 T Mc M V₁ V₂ Yp J L t := ⟨c25L, hsolv⟩
  have c27 := h27 G T Mc M V₁ V₂ Yp J L t c27ctx
  obtain ⟨hIeq, hunique⟩ := S153D.lemma_15_3_27_four c25L c27 hmin
  have c28ctx : Ctx15328 T Mc M V₁ V₂ Yp J L t := ⟨c27ctx, c27, hmin, hIeq, hunique⟩
  have c28 := h28 G T Mc M V₁ V₂ Yp J L t c28ctx
  have c29 := S153D.lemma_15_3_29 h113 c28ctx
  have c30ctx : Ctx15330 T Mc M V₁ V₂ Yp J L t := ⟨c28ctx, c28, c29⟩
  have c30 := h30 G T Mc M V₁ V₂ Yp J L t c30ctx
  have c31ctx : Ctx15331 T Mc M V₁ V₂ Yp J L t := ⟨c30ctx, c30⟩
  have c31 := h31 G T Mc M V₁ V₂ Yp J L t c31ctx
  have c32ctx : Ctx15332 T Mc M V₁ V₂ Yp J L t := ⟨c31ctx, c31⟩
  exact hc G T Mc M V₁ V₂ Yp J L t c32ctx (h32 G T Mc M V₁ V₂ Yp J L t c32ctx)

end CFSG.Quasithin
