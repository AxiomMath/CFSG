module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.McL
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

theorem center_eq_bot_mcl : center NativeSporadic.McL = ⊥ := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.McL.fam_mcl_simplicity
  refine HypOne.center_eq_bot_of_isSimpleGroup fun hp => ?_
  have h2 := hp.eq_one_or_self_of_dvd 2 (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  rw [CFSG.Sporadic.McL.card_McL] at h2
  omega

theorem center_eq_bot_of_isSporadic_mcl {Y : Type} [Group Y]
    (h : IsSporadic Y .McL) : center Y = ⊥ := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.McL := e₀
  have hc := center_eq_bot_mcl
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ center NativeSporadic.McL := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hc, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem index_dvd_two_of_isSporadic_mcl
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .McL) :
    (innAut Y).index ∣ 2 := by
  have hZ := center_eq_bot_of_isSporadic_mcl h
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.McL := e₀
  obtain ⟨-, -, -, -, hcard⟩ := CFSG.Sporadic.SmallOddCore.mcl_full_automorphism_model
  have eP : Y ≃* CFSG.Sporadic.Schreier.mclP := e.trans CFSG.Sporadic.Schreier.mclPermEquiv
  have h1 : Nat.card (MulAut Y) = 1796256000 := by
    rw [Nat.card_congr (MulAut.congr eP).toEquiv, hcard]
  have h2 : Nat.card Y = 898128000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  exact HypOne.index_dvd_two_of_card_le (HypOne.conj_injective_of_center_eq_bot hZ)
    (by rw [h1, h2])

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_eq_two_mcl
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .McL)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_mcl hL
  have hLq : IsSporadic (L ⧸ center L) .McL := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact h.card_sylow_eq_two_of_fours
    (HypOne.McL.fullRowData_of_isSporadic hLq).rowData.hypothesisOne
    (HypOne.McL.fullRowData_of_isSporadic hL).fours S

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.relIndex_dvd_two_mcl
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .McL)
    {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_mcl hL
  have hLq : IsSporadic (L ⧸ center L) .McL := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact (h.relIndex_sup_zpowers_dvd (h.card_sylow_eq_two_mcl hL) ht ht2).trans
    (index_dvd_two_of_isSporadic_mcl hLq)

end CFSG.EvenSporadicStandard.McLStd
