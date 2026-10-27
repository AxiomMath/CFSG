module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInner
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNative
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaAut
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverAction

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Sporadic.Schreier CFSG.Blueprint

theorem yamadaFacts_ofMulEquivT46
    {Q : Type} [Group Q] (hQ : LieModel Q .PSU 6 2 1)
    (e : Q ≃* CFSG.Fischer.T46) : YamadaFacts (ToddParabolic.ofMulEquivT46 e) where
  card_outer := card_outer_of_lieModel hQ
  rank := fun _ hα hout _ hfix hsq => card_le_of_fixed hQ hα hout hfix hsq
  fusion := fusion_of_lieModel hQ
  centralizer_A := centralizer_A_of_lieModel hQ _
  comm_a₁ := comm_a₁_ofMulEquivT46 e
  comm_a₂ := comm_a₂_ofMulEquivT46 e
  two_trans := two_trans_ofMulEquivT46 e

theorem exists_yamadaFacts
    {Q : Type} [Group Q] (hQ : LieModel Q .PSU 6 2 1) :
    ∃ D : ToddParabolic Q, YamadaFacts D := by
  obtain ⟨e⟩ := LieType.Multipliers.U62.nonempty_mulEquiv_T46 hQ
  exact ⟨_, yamadaFacts_ofMulEquivT46 hQ e⟩

theorem exists_setting
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hQ : LieModel (L ⧸ center L) .PSU 6 2 1) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) : ∃ D : ToddParabolic L, Setting G L D t := by
  have hL : LieModel L .PSU 6 2 1 := by
    have e : (L ⧸ center L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact LieType.CurtisTits.lieModel_of_mulEquiv e hQ
  obtain ⟨D, hD⟩ := exists_yamadaFacts hL
  exact ⟨D, hset, hZ, hD, htL, ht⟩

end CFSG.EvenSmallLie.UnitarySix.Yamada
