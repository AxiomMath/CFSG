module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DFinal

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaD CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}
  {t : G}

theorem setting_ofMulEquivT46 [Finite G] (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hQ : LieModel (L ⧸ center L) .PSU 6 2 1) (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (e : L ≃* T46) :
    Yamada.Setting G L (ToddParabolic.ofMulEquivT46 e) t := by
  have hL : LieModel L .PSU 6 2 1 := by
    have e' : (L ⧸ center L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact LieType.CurtisTits.lieModel_of_mulEquiv e' hQ
  exact ⟨hset, hZ, Yamada.yamadaFacts_ofMulEquivT46 hL e, htL, ht⟩



theorem hypC₂_sec3DData [Finite G] (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hQ : LieModel (L ⧸ center L) .PSU 6 2 1) (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (e : L ≃* T46) : HypC₂ (sec3DData e t) :=
  HypC₂.of_setting (setting_ofMulEquivT46 hset hZ hQ htL ht e) rfl (toddA_eq_sA₂ e).symm rfl


theorem hyp_sec3DData' [Finite G] (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hQ : LieModel (L ⧸ center L) .PSU 6 2 1) (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (e : L ≃* T46) (hA : HypAut (sec3DData e t)) :
    Hyp (sec3DData e t) :=
  hyp_sec3DData hset hZ hQ htL ht (hypC₂_sec3DData hset hZ hQ htL ht e) hA

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
