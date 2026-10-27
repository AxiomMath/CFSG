module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

theorem ConclK.of_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K] (e : K ≃* K')
    {L V MK : Subgroup K} (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set K))
    (hc : ConclK K' (L.map e.toMonoidHom) (V.map e.toMonoidHom) (MK.map e.toMonoidHom)) :
    ConclK K L V MK := by
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  refine conclK_of_map e.toMonoidHom e.surjective (by rw [hker]; exact bot_le) ?_ hV hLV
    (by rw [hker, inf_bot_eq]) (fun _ => hker) hc
  rw [hker, Subgroup.card_bot]
  exact odd_one

theorem KConfig.conclK_of_eq_map {K : Type} [Group K] [Finite K] {L V MK L₀ V₀ : Subgroup K}
    (h : KConfig K L V MK) (σ : K ≃* K) (hV : V = V₀.map σ.toMonoidHom)
    (hL : L = L₀.map σ.toMonoidHom) (hc : ∀ MK' : Subgroup K, ConclK K L₀ V₀ MK') :
    ConclK K L V MK := by
  have hback : ∀ H : Subgroup K, (H.map σ.toMonoidHom).map σ.symm.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    convert Subgroup.map_id H
    ext x
    simp
  refine ConclK.of_map_mulEquiv σ.symm h.elemAbelian h.le_normalizer ?_
  rw [hV, hL, hback, hback]
  exact hc _

end CFSG.SectionRank.QTK.Insp443

end
