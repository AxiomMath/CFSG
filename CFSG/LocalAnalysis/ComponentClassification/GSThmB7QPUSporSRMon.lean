module

public import CFSG.Monster.SteinbergBQInvolutionComponentsTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SimpleSocleComponent
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.Monster.SteinbergMCatalogNativeIso
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatFittingTransfer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.GSThmB.QPUSpor

open CFSG Subgroup CFSG.Blueprint CFSG.Monster.Generated CFSG.Monster.Existence
open CFSG.Monster.B CFSG.Monster.B.TwoA
open scoped MatrixGroups

theorem not_dvd_card_psl2_of_centralizer {q : ℕ}
    (h : q - 1 = 354883595661213696000 ∨ q + 1 = 354883595661213696000) :
    ¬ 4154781481226426191177580544000000 ∣ q * ((q ^ 2 - 1) / 2) := by
  rcases h with h | h
  · obtain rfl : q = 354883595661213696001 := by omega
    norm_num
  · obtain rfl : q = 354883595661213695999 := by omega
    norm_num

theorem not_psl2_component_Cfull
    {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f)
    (hF : Nat.card F = p ^ f) (B : Subgroup Cfull) (hB : IsComponent B) :
    IsEmpty (B ⧸ center B ≃* PSL(2, F)) := by
  refine ⟨fun eB => ?_⟩
  obtain ⟨-, -, ⟨A, hAn, -, -, -, hAs, hAab, hSA, hAcen, -, -, -⟩, -⟩ :=
    full_short_centralizer_almost_simple.{0}
  obtain ⟨-, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.central_extension_simple_socle_component_quotients
      ZstarF_le_center hAn hAs hAab hAcen hB
  let e : A ≃* PSL(2, F) := eA.symm.trans eB
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hxA : xhat ∈ A := hSA ⟨xbar, iotaD_xbar⟩
  have hmap : (centralizer {(⟨xhat, hxA⟩ : A)}).map A.subtype = Jhat := by
    rw [show (centralizer {(⟨xhat, hxA⟩ : A)}).map A.subtype = A ⊓ centralizer {xhat} from
      SteinbergBQ.map_subtype_centralizer_eq _, centralizer_xhat]
    exact inf_eq_right.2 (Jhat_le_Shat.trans hSA)
  have hCa : Nat.card (centralizer {(⟨xhat, hxA⟩ : A)}) = 2 ^ 41 * 161382375 := by
    rw [← Subgroup.card_subtype A (centralizer {(⟨xhat, hxA⟩ : A)}), hmap, natCard_Jhat]
  have hC : Nat.card (centralizer ({e ⟨xhat, hxA⟩} : Set PSL(2, F))) = 2 ^ 41 * 161382375 := by
    rw [← hCa]
    exact (Nat.card_congr (BMCase.gmatCentralizerEquiv e _).toEquiv).symm
  have ht : orderOf (e ⟨xhat, hxA⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, orderOf_xhat]
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution F hF hpo hf ht
  have hS : Nat.card Shat ∣ Nat.card A := Subgroup.card_dvd_of_le hSA
  have hSc : Nat.card Shat = 4154781481226426191177580544000000 := by
    rw [← CFSG.Monster.AxisCount.Baby.natCard_Cbar]
    exact (Nat.card_congr (MonoidHom.ofInjective iotaD_injective).toEquiv).symm
  have hA : Nat.card A = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
    rw [Nat.card_congr e.toEquiv]
    exact SectionRank.OddCover.card_psl_two Fact.out hp2 hF
  rw [hSc, hA] at hS
  refine not_dvd_card_psl2_of_centralizer ?_ hS
  have hq : p ^ f % 2 = 1 := Nat.odd_iff.1 hpo.pow
  rcases (show p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 by omega) with h | h
  · have h' := (h1 h).1
    rw [hC] at h'
    norm_num at h'
    omega
  · have h' := (h3 h).1
    rw [hC] at h'
    norm_num at h'
    omega

theorem not_psl2_component_Gmat
    {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f)
    (hF : Nat.card F = p ^ f) (t : Gmat) (ht : orderOf t = 2)
    (B : Subgroup (centralizer ({t} : Set Gmat))) (hB : IsComponent B) :
    IsEmpty (B ⧸ center B ≃* PSL(2, F)) := by
  rcases Census.generated_group_two_involution_classes t ht with hx | hs
  · have h2B := isTwoBCentralizer_Gmat t hx
    exact (SteinbergBQ.not_isComponent_of_selfCentralizing h2B.2.2.1 B hB).elim
  · have h1 := isConj_iff.1 hs
    obtain ⟨c, rfl⟩ := h1
    let ε : centralizer ({c * tGmat * c⁻¹} : Set Gmat) ≃* Cfull :=
      (SteinbergBQ.conjCentEquiv c tGmat).symm.trans
        (((cent tGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
          (MulEquiv.subgroupCongr (SteinbergBQ.map_subtype_centralizer_eq tGmat)))
    exact ⟨fun eB => (not_psl2_component_Cfull hp2 hf hF _
      (LocalCores.isComponent_map_mulEquiv ε hB)).false
      ((QuotientGroup.congr _ _ (B.equivMapOfInjective ε.toMonoidHom ε.injective)
        (Subgroup.map_center_eq _)).symm.trans eB)⟩

theorem not_psl2_component_M
    {Y : Type} [Group Y] [IsSimpleGroup Y] (e : Y ≃* NativeSporadic.Carrier .M) {F : Type}
    [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f)
    (hF : Nat.card F = p ^ f) (t : Y) (ht : orderOf t = 2)
    (B : Subgroup (centralizer ({t} : Set Y))) (hB : IsComponent B) :
    IsEmpty (B ⧸ center B ≃* PSL(2, F)) := by
  let ψ : Y ≃* Gmat := MulEquiv.ofBijective _ (BMCase.catalog_fM_comp_mulEquiv_bijective e)
  let ε := BMCase.gmatCentralizerEquiv ψ t
  have hψt : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  exact ⟨fun eB => (not_psl2_component_Gmat hp2 hf hF (ψ t) hψt _
    (LocalCores.isComponent_map_mulEquiv ε hB)).false
    ((QuotientGroup.congr _ _ (B.equivMapOfInjective ε.toMonoidHom ε.injective)
      (Subgroup.map_center_eq _)).symm.trans eB)⟩

end CFSG.ComponentClassification.GSThmB.QPUSpor
