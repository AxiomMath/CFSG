module

public import CFSG.Sporadic.Recognition.HSMultiplierCert
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Aut

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Recognition.HSMultiplier CFSG.Sporadic.Recognition.CoverRecipe

theorem card_mulAut_of_isSporadic_hs
    {Y : Type} [Group Y] (h : IsSporadic Y .HS) :
    Nat.card (MulAut Y) = 88704000 := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.HS := e₀
  obtain ⟨-, -, -, -, hcard⟩ := CFSG.Sporadic.SmallOddCore.hs_full_automorphism_model
  have eP : Y ≃* CFSG.Sporadic.Schreier.hsP := e.trans CFSG.Sporadic.Schreier.hsPermEquiv
  rw [Nat.card_congr (MulAut.congr eP).toEquiv, hcard]

theorem center_eq_bot_of_isSporadic_hs {Y : Type} [Group Y]
    (h : IsSporadic Y .HS) : center Y = ⊥ := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.HS := e₀
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.HS.fam_hs_simplicity
  have hc : center NativeSporadic.HS = ⊥ :=
    HypOne.center_eq_bot_of_isSimpleGroup fun hp => by
      have h2 := hp.eq_one_or_self_of_dvd 2 (by rw [CFSG.Sporadic.HS.card_HS]; norm_num)
      rw [CFSG.Sporadic.HS.card_HS] at h2
      omega
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ center NativeSporadic.HS := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hc, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem index_dvd_two_of_isSporadic_hs
    {Y : Type} [Group Y] (h : IsSporadic Y .HS) :
    (MulAut.conj : Y →* MulAut Y).range.index ∣ 2 := by
  have hZ := center_eq_bot_of_isSporadic_hs h
  have hcardY : Nat.card Y = 44352000 := by
    obtain ⟨e₀⟩ := h
    have e : Y ≃* NativeSporadic.HS := e₀
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by rw [hcardY]; norm_num)
  exact HypOne.index_dvd_two_of_card_le (HypOne.conj_injective_of_center_eq_bot hZ)
    (by rw [card_mulAut_of_isSporadic_hs h, hcardY])

theorem nonempty_mulEquiv_presentedCover {X : Type} [Group X] {ι : Type} {g : ι → X}
    {R : Set (FreeGroup ι)} {w : ι → FreeGroup ι} (hP : CFSG.LieType.Multipliers.IsPresentation g R)
    (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) (hwg : ∀ i, FreeGroup.lift g (w i) = g i)
    [Finite (CFSG.LieType.Multipliers.PresentedCover R w)] {E : Type} [Group E]
    (hE : Group.IsPerfect E) (e : E ⧸ center E ≃* X)
    (hcard : Nat.card (CFSG.LieType.Multipliers.PresentedCover R w) ≤ Nat.card E) :
    Nonempty (CFSG.LieType.Multipliers.PresentedCover R w ≃* E) := by
  have := hE
  obtain ⟨φ, hφ, -⟩ := CFSG.Sporadic.Recognition.CoverTransfer.exists_bijective_of_card_le hP hw hwg
    (centerQuotMap e) (centerQuotMap_surjective e) (le_of_eq (ker_centerQuotMap e)) hcard
  exact ⟨MulEquiv.ofBijective φ hφ⟩

theorem nonempty_mulEquiv_cover_of_doubleCover_hs
    {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E)
    (hc : Nat.card (center E) = 2) (hq : IsSporadic (E ⧸ center E) .HS) :
    Nonempty (HSCover ≃* E) := by
  obtain ⟨e₀⟩ := hq
  have e : E ⧸ center E ≃* NativeSporadic.HS := e₀
  obtain ⟨hfin, hle⟩ := cover_card_le
  have := hE
  have hcard : Nat.card E = 88704000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center E)
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS, hc] at h1
    omega
  have := hfin
  exact nonempty_mulEquiv_presentedCover
    isPresentation_hsGen_of_certificate
    hsCommW_mem_commutator (lift_hsCommW hsTabCheck_eq_true) hE
    (e.trans CFSG.Sporadic.Bridge.HS.nativeEquiv) (by rw [hcard]; exact hle)

theorem nonempty_mulEquiv_of_doubleCover_hs
    {E₁ E₂ : Type} [Group E₁] [Group E₂] [Finite E₁] [Finite E₂]
    (h₁ : Group.IsPerfect E₁) (h₂ : Group.IsPerfect E₂) (c₁ : Nat.card (center E₁) = 2)
    (c₂ : Nat.card (center E₂) = 2) (q₁ : IsSporadic (E₁ ⧸ center E₁) .HS)
    (q₂ : IsSporadic (E₂ ⧸ center E₂) .HS) : Nonempty (E₁ ≃* E₂) := by
  obtain ⟨f₁⟩ := nonempty_mulEquiv_cover_of_doubleCover_hs h₁ c₁ q₁
  obtain ⟨f₂⟩ := nonempty_mulEquiv_cover_of_doubleCover_hs h₂ c₂ q₂
  exact ⟨f₁.symm.trans f₂⟩

end CFSG.EvenSporadicStandard.TwoHS
