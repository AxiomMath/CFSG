module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalance
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreBalB
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Sporadic.Schreier.J1QT

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_of_sporadic_outer {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) {a : K} (ha : orderOf a = 2) {Y : Subgroup K}
    (hY : IsPComponent 2 Y) (θ : Y ⧸ Open.fusionZStar Y ≃* Blueprint.NativeSporadic.Carrier s)
    (hout : Nat.card (OuterAutomorphisms.Outer (Y ⧸ Open.fusionZStar Y)) ≤ 8) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K := by
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have : Finite (MulAut (Y ⧸ Open.fusionZStar Y)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (Y ⧸ Open.fusionZStar Y)))
  exact core_commutator_le_of_outer_comm footeLBalanceInput_holds ha hY
    (hbal_of_coreFree hna (coreFree_of_sporadicOddCoreFree hs θ))
    (oddSubgroup_comm_of_card_le_eight hout)

theorem card_outer_le_of_mulEquiv {S T : Type*} [Group S] [Group T] (θ : S ≃* T) {k : ℕ}
    (h : Nat.card (OuterAutomorphisms.Outer T) ≤ k) :
    Nat.card (OuterAutomorphisms.Outer S) ≤ k := by
  rw [Nat.card_congr (OuterAutomorphisms.equivalence θ).toEquiv]
  exact h

theorem card_fusionZStar_eq (L : Type*) [Group L] [Finite L] :
    Nat.card (Open.fusionZStar L) = Nat.card (Open.fusionOddCore L) *
      Nat.card (center (L ⧸ Open.fusionOddCore L)) := by
  set N := Open.fusionOddCore L
  set H := center (L ⧸ N)
  have hdef : Open.fusionZStar L = H.comap (QuotientGroup.mk' N) := rfl
  rw [hdef]
  have hidx : (H.comap (QuotientGroup.mk' N)).index = H.index :=
    index_comap_of_surjective H (QuotientGroup.mk'_surjective N)
  have h1 := card_mul_index (H.comap (QuotientGroup.mk' N))
  have h2 := card_mul_index H
  have h3 := card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < H.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  rw [hidx] at h1
  have : Nat.card ↥(H.comap (QuotientGroup.mk' N)) * H.index =
      Nat.card N * Nat.card H * H.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [this])

theorem odd_card_fusionZStar_of_oddMultiplier {Y : Subgroup K} (hY : IsPComponent 2 Y)
    {S₀ : Type*} [Group S₀] (hM : RankTwoSporadic.OddMultiplier S₀)
    (θ : Y ⧸ Open.fusionZStar Y ≃* S₀) : Odd (Nat.card (Open.fusionZStar Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 Y hY
  set O := Open.fusionOddCore ↥Y with hO
  have hq₁ : IsQuasisimple (↥Y ⧸ O) := LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (UnbalancingLocal.fusionOddCore_eq_pPrimeCore ↥Y)).symm hq
  have hmap : (Open.fusionZStar ↥Y).map (QuotientGroup.mk' O) = center (↥Y ⧸ O) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
  let e : (↥Y ⧸ O) ⧸ center (↥Y ⧸ O) ≃* ↥Y ⧸ Open.fusionZStar ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (Open.fusionZStar ↥Y)
        fusionOddCore_le_fusionZStar)
  have hperf : commutator (↥Y ⧸ O) = ⊤ := Group.isPerfect_def.mp hq₁.1
  have hZ := hM (↥Y ⧸ O) hperf ⟨e.trans θ⟩
  have hOodd : Odd (Nat.card O) := by
    rw [hO, UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [card_fusionZStar_eq]
  exact Nat.odd_mul.mpr ⟨hOodd, hZ⟩

theorem coreCondition_of_sporadic_lift {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s)
    (hM : RankTwoSporadic.OddMultiplier (Blueprint.NativeSporadic.Carrier s))
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* Blueprint.NativeSporadic.Carrier s) :
    ⁅oddCoreOfCentralizer a, Y⁆ ≤ pPrimeCore 2 K := by
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  exact core_commutator_le_of_lift footeLBalanceInput_holds ha hY
    (odd_card_fusionZStar_of_oddMultiplier hY hM θ)
    (hloc_of_coreFree hna (coreFree_of_sporadicOddCoreFree hs θ))

end CFSG.ComponentClassification.Foote5
