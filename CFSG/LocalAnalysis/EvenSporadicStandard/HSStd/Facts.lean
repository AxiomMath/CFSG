module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FusionSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Fours
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHS

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

theorem center_eq_bot_hs : center NativeSporadic.HS = ⊥ := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.HS.fam_hs_simplicity
  refine HypOne.center_eq_bot_of_isSimpleGroup fun hp => ?_
  have h2 := hp.eq_one_or_self_of_dvd 2 (by rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  rw [CFSG.Sporadic.HS.card_HS] at h2
  omega

theorem center_eq_bot_of_isSporadic_hs {Y : Type} [Group Y]
    (h : IsSporadic Y .HS) : center Y = ⊥ := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.HS := e₀
  have hc := center_eq_bot_hs
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ center NativeSporadic.HS := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hc, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem index_dvd_two_of_isSporadic_hs
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .HS) :
    (innAut Y).index ∣ 2 := by
  have hZ := center_eq_bot_of_isSporadic_hs h
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.HS := e₀
  obtain ⟨-, -, -, -, hcard⟩ := CFSG.Sporadic.SmallOddCore.hs_full_automorphism_model
  have eP : Y ≃* CFSG.Sporadic.Schreier.hsP := e.trans CFSG.Sporadic.Schreier.hsPermEquiv
  have h1 : Nat.card (MulAut Y) = 88704000 := by
    rw [Nat.card_congr (MulAut.congr eP).toEquiv, hcard]
  have h2 : Nat.card Y = 44352000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  exact HypOne.index_dvd_two_of_card_le (HypOne.conj_injective_of_center_eq_bot hZ)
    (by rw [h1, h2])

structure HSFacts : Prop where
  invol : ∀ (Y : Type) [Group Y], IsSporadic Y .HS → ∀ z : Y, orderOf z = 2 →
    LayerZeroInvolution Y z
  sylow_centralizer : ∀ (Y : Type) [Group Y] [Finite Y], IsSporadic Y .HS → ∀ R : Sylow 2 Y,
    ∃ z : Y, orderOf z = 2 ∧ centralizer ((R : Subgroup Y) : Set Y) = zpowers z ∧
      ∃ P : Subgroup Y, P ≤ centralizer ({z} : Set Y) ∧ ⁅P, P⁆ = P ∧ z ∈ P

theorem HSFacts.layerZeroData
    (F : HSFacts) {Y : Type}
    [Group Y] [Finite Y]
    (h : IsSporadic Y .HS) : LayerZeroData Y := by
  have hZ := center_eq_bot_of_isSporadic_hs h
  have hq : IsSporadic (Y ⧸ center Y) .HS := by
    obtain ⟨e⟩ := h
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact ⟨foursGroupCondition_of_isSporadic_hs h, index_dvd_two_of_isSporadic_hs hq, F.invol Y h⟩

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_eq_two_hs
    (F : HSFacts) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L)
    (hL : IsSporadic L .HS) (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 :=
  h.card_sylow_eq_two_of_layerZeroData (center_eq_bot_of_isSporadic_hs hL)
    (F.layerZeroData hL) S

theorem HSFacts.fusionData
    (F : HSFacts) {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .HS) : FusionData Y := by
  refine ⟨fun β hβ => ?_, F.sylow_centralizer Y h⟩
  obtain ⟨l, hl⟩ := CFSG.QuasithinUnique.Ch1.hsAutInner Y h β hβ
  refine ⟨l⁻¹, ?_⟩
  ext x
  rw [hl x, MulAut.conj_apply]
  simp

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.sylowFusion_hs
    (F : HSFacts) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .HS) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) : SylowFusion L t := by
  have hZ := center_eq_bot_of_isSporadic_hs hL
  have hq : IsSporadic (L ⧸ center L) .HS := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact h.exists_normalizer_conj_of_fusionData hZ (h.card_sylow_eq_two_hs F hL)
    (index_dvd_two_of_isSporadic_hs hq) (F.fusionData hL) ht ht2

end CFSG.EvenSporadicStandard.HSStd
