module

public import CFSG.LocalAnalysis.OddStandard.ThmCSylowSL2
public import CFSG.GH74.Generic.ExceptionalRank
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.OddStandard.ThmC.Sylow

open CFSG.GH74.Generic CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.OddStandard.ThmC.T

theorem false_of_lieModel_g2
    {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : LieModel K .G2 0 p f) (T : Sylow 2 K) (hT : IsT (T : Subgroup K)) :
    False := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
    have hch : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
    have hπ : Function.Injective
        (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .G2 F))) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_adjointGroup_eq_bot]
    let π : ↥(adjointGroup .G2 F) →* AdjointQuotient .G2 F := QuotientGroup.mk' _
    let φL : SL2 F →* ↥(adjointGroup .G2 F) :=
      (rootSL2 .G2 F g2Long).codRestrict _ (rootSL2_mem_adjoint g2Long)
    let φS : SL2 F →* ↥(adjointGroup .G2 F) :=
      (rootSL2 .G2 F g2Short).codRestrict _ (rootSL2_mem_adjoint g2Short)
    have hL : Function.Injective φL := fun x y hxy =>
      rootSL2_injective' hch g2Long (congrArg Subtype.val hxy)
    have hS : Function.Injective φS := fun x y hxy =>
      rootSL2_injective' hch g2Short (congrArg Subtype.val hxy)
    refine not_isT_of_commuting_sl2 T hT hch hch ((e.symm.toMonoidHom.comp π).comp φL)
      ((e.symm.toMonoidHom.comp π).comp φS)
      (e.symm.injective.comp (hπ.comp hL)) (e.symm.injective.comp (hπ.comp hS)) fun A B => ?_
    have hc : Commute (φL A) (φS B) := Subtype.ext (g2_commute_rootSL2 A B)
    exact (hc.map π).map e.symm.toMonoidHom
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.OddStandard.ThmC.Sylow
