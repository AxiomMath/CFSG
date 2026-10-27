module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankSL2
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Levi
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Simplicity CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

variable {k : Type} [Field k] [Finite k] {θ : k →+* k}

set_option linter.unusedSectionVars false


theorem ker_central_twistedE6 (hθ : ∀ c, θ (θ c) = c) (hK4 : 4 ≤ Nat.card k)
    {Y : Type} [Group Y] (e : Y ≃* DerivedCentralQuotient (twistedFixedGroup .E6 k θ))
    {z : fixedGroup k θ}
    (hz : (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (twistedIsogeny θ hθ hK4))) z = 1) :
    z ∈ Subgroup.center (fixedGroup k θ) := by
  have hquasi := fixedGroup_isQuasisimple_of_four_le_card θ hθ hK4
  have hsurj := twistedIsogeny_surjective θ hθ hK4
  have hker := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.ker_twistedIsogeny_eq_center
    hθ hK4
  have hZ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hquasi hsurj hker.le
  have h1 : (QuotientGroup.mk' (Subgroup.center ↥⁅twistedFixedGroup .E6 k θ,
      twistedFixedGroup .E6 k θ⁆)) (twistedIsogeny θ hθ hK4 z) = 1 := by
    apply e.symm.injective
    simpa using hz
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  rw [hZ] at h2
  obtain ⟨z', hz', hzz'⟩ := h2
  have h3 : z'⁻¹ * z ∈ (twistedIsogeny θ hθ hK4).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hzz', inv_mul_cancel]
  rw [hker] at h3
  have := Subgroup.mul_mem _ hz' h3
  simpa using this

theorem two_le_pRank_three_twistedE6 (hθ : ∀ c, θ (θ c) = c) (hK4 : 4 ≤ Nat.card k)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* DerivedCentralQuotient (twistedFixedGroup .E6 k θ)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
  two_le_pRank_three_of_sl2_pair
    (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (twistedIsogeny θ hθ hK4)))
    (fun z hz => ker_central_twistedE6 hθ hK4 e hz)
    (nodeHom0 θ) (nodeHom2 θ hθ) (rFixed_injective θ _ _)
    (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.slOrbitHom_injective θ hθ _)
    (fun A B => commute_rFixed_slOrbitHom θ hθ rfl (Or.inl ⟨rfl, rfl⟩) (by decide) (by decide)
      (by decide) (by decide) A B)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
