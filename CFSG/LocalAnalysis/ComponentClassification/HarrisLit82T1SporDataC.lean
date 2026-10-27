module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie
public import CFSG.Monster.SteinbergBQInvolutionComponentsTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SimpleSocleComponent
public import CFSG.Monster.Existence.TwoPoint.ShapeSixCover
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.B.CTIB.ComponentsSeventeen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint CFSG.Monster.Generated CFSG.Monster.Existence
open CFSG.Monster.B CFSG.Monster.B.TwoA

theorem sporT1Data_B
    : SporT1Data .B where
  oddCore := oddCore_of_free BMCase.sporadicOddCoreFree_B
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    obtain ⟨-, hiso, -⟩ :=
      Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht
        B hB
    rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
      exact fun h => not_oddLieOrder_E62 h.oddLieOrder
    · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
      rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
        Monster.B.E6.FieldInvF4.card_groupJ]
      exact fun h => not_oddLieOrder_F42 h.oddLieOrder

theorem card_component_Cfull
    (B : Subgroup Cfull) (hB : IsComponent B) :
    Nat.card (↥B ⧸ center ↥B) = 4154781481226426191177580544000000 := by
  obtain ⟨-, -, ⟨A, hAn, -, -, -, hAs, hAab, hSA, hAcen, -, -, -⟩, -⟩ :=
    full_short_centralizer_almost_simple.{0}
  obtain ⟨-, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.central_extension_simple_socle_component_quotients
      ZstarF_le_center hAn hAs hAab hAcen hB
  have hAtop : A = ⊤ := by
    rw [Shat_eq_top] at hSA
    exact top_le_iff.1 hSA
  have h1 : Nat.card ↥A = Nat.card ↥Shat := by rw [hAtop, Shat_eq_top]
  have h2 : Nat.card ↥Shat = Nat.card Cbar :=
    (Nat.card_congr (MonoidHom.ofInjective iotaD_injective).toEquiv).symm
  rw [Nat.card_congr eA.toEquiv, h1, h2, CFSG.Monster.AxisCount.Baby.natCard_Cbar]

theorem card_component_Gmat
    (t : Gmat) (ht : orderOf t = 2) (B : Subgroup (centralizer ({t} : Set Gmat)))
    (hB : IsComponent B) : Nat.card (↥B ⧸ center ↥B) = 4154781481226426191177580544000000 := by
  rcases Census.generated_group_two_involution_classes t ht with hx | hs
  · have h2B := isTwoBCentralizer_Gmat t hx
    exact (SteinbergBQ.not_isComponent_of_selfCentralizing h2B.2.2.1 B hB).elim
  · have h1 := isConj_iff.1 hs
    obtain ⟨c, rfl⟩ := h1
    let ε : centralizer ({c * tGmat * c⁻¹} : Set Gmat) ≃* Cfull :=
      (SteinbergBQ.conjCentEquiv c tGmat).symm.trans
        (((cent tGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
          (MulEquiv.subgroupCongr (SteinbergBQ.map_subtype_centralizer_eq tGmat)))
    exact (Nat.card_congr (QuotientGroup.congr _ _
      (B.equivMapOfInjective ε.toMonoidHom ε.injective) (Subgroup.map_center_eq _)).toEquiv).trans
      (card_component_Cfull _ (LocalCores.isComponent_map_mulEquiv ε hB))

theorem card_component_M
    {Y : Type} [Group Y] [IsSimpleGroup Y] (e : Y ≃* NativeSporadic.Carrier .M) (t : Y)
    (ht : orderOf t = 2) (B : Subgroup (centralizer ({t} : Set Y))) (hB : IsComponent B) :
    Nat.card (↥B ⧸ center ↥B) = 4154781481226426191177580544000000 := by
  let ψ : Y ≃* Gmat := MulEquiv.ofBijective _ (BMCase.catalog_fM_comp_mulEquiv_bijective e)
  let ε := BMCase.gmatCentralizerEquiv ψ t
  have hψt : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  exact (Nat.card_congr (QuotientGroup.congr _ _
    (B.equivMapOfInjective ε.toMonoidHom ε.injective) (Subgroup.map_center_eq _)).toEquiv).trans
    (card_component_Gmat (ψ t) hψt _ (LocalCores.isComponent_map_mulEquiv ε hB))

theorem sporT1Data_M
    : SporT1Data .M where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_M
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    rw [card_component_M e t ht B hB]
    exact fun h => not_oddLieOrder_B h.oddLieOrder

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
