module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

variable {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']

noncomputable def quotEquivMap (e : K ≃* K') (L : Subgroup K) :
    ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(L.map e.toMonoidHom) ⧸ CFSG.pCore 2 ↥(L.map e.toMonoidHom) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥(L.map e.toMonoidHom))
    (L.equivMapOfInjective e.toMonoidHom e.injective)
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 _)

theorem KConf.map_mulEquiv {L V MK : Subgroup K} (h : KConf K L V MK) (e : K ≃* K') :
    KConf K' (L.map e.toMonoidHom) (V.map e.toMonoidHom) (MK.map e.toMonoidHom) := by
  have hc := h.kConfig.map_mulEquiv e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h.quasisimple, ?_, hc.ne_bot,
    hc.elemAbelian, hc.perfect, hc.le_normalizer, hc.le_pCoreOf, hc.pCoreOf_le, hc.eq_commutator,
    hc.le_MK, hc.MK_le_normalizer, hc.MK_ne_top, hc.normalizer_le, ?_, ?_⟩
  ·
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
    exact h.odd_card_center
  ·
    intro X Y hX hY hqX hqY
    let ψ := quotEquivMap e L
    have h1 := h.card_eq (X.map ψ.symm.toMonoidHom) (Y.map ψ.symm.toMonoidHom)
      (hX.map _ ψ.symm.surjective) (hY.map _ ψ.symm.surjective)
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (X.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective) hqX)
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Y.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective) hqY)
    rwa [← Nat.card_congr (X.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).toEquiv,
      ← Nat.card_congr (Y.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).toEquiv] at h1
  ·
    intro Q hQ hQ2 p hp hp2 E hEN hE
    have h1 := h.card_le (Q.map e.symm.toMonoidHom)
      (fun hb => hQ ((Subgroup.map_eq_bot_iff_of_injective Q e.symm.injective).mp hb))
      (hQ2.map _) p hp hp2 (E.map e.symm.toMonoidHom) (by
        rw [← Subgroup.map_normalizer_eq_of_bijective Q e.symm.bijective]
        exact Subgroup.map_mono hEN) (hE.map _)
    rwa [Subgroup.card_map_of_injective e.symm.injective] at h1

end CFSG.SectionRank.QTK.Insp443
