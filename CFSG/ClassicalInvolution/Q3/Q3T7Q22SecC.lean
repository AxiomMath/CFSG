module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Sect
public import CFSG.ClassicalInvolution.Q3.Q3T7ExNbr
public import CFSG.ClassicalInvolution.Q3.Q3T7M02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def SectionConnected (Ω : Set (Subgroup G)) (c : G) : Prop :=
  CFSG.ClassicalInvolution.Asc77.T3.DStarConnected (quotFamily (ExactLayer.exactPair Ω c)
    (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)))

theorem oddCoreOf_exactLayer_le (hΩ : ConjInvariant Ω) (c : G) :
    oddCoreOf (ExactLayer.exactLayer Ω c) ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G)) := by
  set Y := ExactLayer.exactLayer Ω c with hY
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hYC : Y ≤ C := ExactLayer.exactLayer_le_centralizer Ω c
  have hCN : ∀ g ∈ C, conjSub g Y = Y := fun g hg => ExactLayer.conjSub_exactLayer hΩ hg
  have hPC : oddCoreOf Y ≤ C := (oddCoreOf_le_self Y).trans hYC
  have hinv : ∀ g ∈ C, conjSub g (oddCoreOf Y) = oddCoreOf Y := fun g hg => by
    rw [← AscE184Sect.oddCoreOf_conjSub, hCN g hg]
  have hnorm : ((oddCoreOf Y).subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 : (g : G) * x * (g : G)⁻¹ ∈ conjSub (g : G) (oddCoreOf Y) := conj_mem_conjSub hx
    rwa [hinv g g.2] at h1
  have hodd : Odd (Nat.card ↥((oddCoreOf Y).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv]
    have h1 : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥Y
    have h2 : Nat.card ↥(oddCoreOf Y) = Nat.card (classicalInvolutionOddCore ↥Y) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).symm.toEquiv
    rw [h2]
    exact h1
  have hle : (oddCoreOf Y).subgroupOf C ≤ classicalInvolutionOddCore ↥C :=
    le_sSup ⟨hnorm, hodd⟩
  intro x hx
  exact ⟨⟨x, hPC hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩


theorem exists_conj_tqMembers_of_connected (hΩ : Q3T7M.HM Ω) {c : G} (hc2 : c * c = 1)
    {B : Subgroup G} (hB : B ∈ ExactLayer.tqMembers Ω c) (hconn : SectionConnected Ω c) :
    ∀ M ∈ ExactLayer.tqMembers Ω c, ∃ n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)),
      ∃ J' ∈ ExactLayer.tqMembers Ω c, J' ∈ dstarComp Ω B ∧ M = conjSub n J' := by
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have hΩg : HypOmegaGen Ω := Q3T7.modU_toGen3 hΩ
  set Y := ExactLayer.exactLayer Ω c with hYdef
  set Λ : Set (Subgroup ↥Y) := ExactLayer.exactPair Ω c with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM Λ := ExactLayer.hypOmegaMod_exactPair hΩ hcA
  have hΛ' : Q3T7M.HM (quotFamily Λ N₀) := oddQuotHyp ↥Y Λ hΛ N₀ hN₀odd
  have hmemΛ : ∀ {J : Subgroup G}, J ∈ ExactLayer.tqMembers Ω c →
      (ExactLayer.exactCore c J).subgroupOf Y ∈ Λ := fun {J} hJ =>
    ⟨ExactLayer.exactCore c J, ExactLayer.exactCore_mem_exactFamily hJ,
      ExactLayer.exactCore_le_exactLayer hJ, rfl⟩
  have hexΛ : ∀ {L : Subgroup ↥Y}, L ∈ Λ → ∃ J ∈ ExactLayer.tqMembers Ω c,
      L = (ExactLayer.exactCore c J).subgroupOf Y := by
    rintro L ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩
    exact ⟨J, hJ, rfl⟩
  let good : Subgroup ↥Y → Prop := fun L => ∃ J ∈ ExactLayer.tqMembers Ω c,
    L = (ExactLayer.exactCore c J).subgroupOf Y ∧ J ∈ dstarComp Ω B
  have hstepΛ : ∀ {L L' : Subgroup ↥Y}, L' ∈ Λ → good L → dstarAdj Λ L L' → good L' := by
    intro L L' hL' hgood hadj
    obtain ⟨J, hJ, rfl, hJB⟩ := hgood
    obtain ⟨J', hJ', rfl⟩ := hexΛ hL'
    have h1 := dstarAdj_map hadj
    rw [Subgroup.map_subgroupOf_eq_of_le (ExactLayer.exactCore_le_exactLayer hJ),
      Subgroup.map_subgroupOf_eq_of_le (ExactLayer.exactCore_le_exactLayer hJ')] at h1
    exact ⟨J', hJ', rfl, hJB.tail (Q3T7.dstarAdj_of_exactFamily3 hΩ hcA hJ hJ' h1)⟩
  have hBΛ := hmemΛ hB
  intro M hM
  have hMΛ := hmemΛ hM
  obtain ⟨M', hM', hMeq, hMgood⟩ := exists_good_lift (N := N₀) good hBΛ
    ⟨B, hB, rfl, Relation.ReflTransGen.refl⟩
    (fun L hL L' hL' hgL hadj => by
      obtain ⟨-, hadj | hadj⟩ := hadj
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr hΛ hΛ' hN₀odd hL hL' hadj
        have h1 := omegaStarNbr_conj hΛ.conjInvariant hn' (n⁻¹ : ↥Y)
        rw [conjSub_inv_conjSub] at h1
        have hnn : QuotientGroup.mk' N₀ n⁻¹ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (N₀.inv_mem hn)
        refine ⟨conjSub n⁻¹ L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact hstepΛ (hΛ.conjInvariant _ L' hL') hgL ⟨hΛ.conjInvariant _ L' hL', Or.inl h1⟩
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr hΛ hΛ' hN₀odd hL' hL hadj
        have hnn : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
        refine ⟨conjSub n L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact hstepΛ (hΛ.conjInvariant _ L' hL') hgL ⟨hΛ.conjInvariant _ L' hL', Or.inr hn'⟩)
    (hconn _ (map_mem_quotFamily hBΛ) _ (map_mem_quotFamily hMΛ))
  obtain ⟨n, hn, hMn⟩ := exists_conj_of_map_eq hΛ hN₀odd hM' hMΛ hMeq
  obtain ⟨J, hJ, rfl, hJB⟩ := hMgood
  have hnC : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    ExactLayer.exactLayer_le_centralizer Ω c n.2
  have hnO : (n : G) ∈ oddCoreOf Y := ⟨n, hn, rfl⟩
  refine ⟨(n : G), oddCoreOf_exactLayer_le hΩ.conjInvariant c hnO, J, hJ, hJB, ?_⟩
  have h3 : conjSub n ((ExactLayer.exactCore c J).subgroupOf Y) =
      (conjSub (n : G) (ExactLayer.exactCore c J)).subgroupOf Y := conjSub_subgroupOf Y n _
  rw [h3] at hMn
  have hle1 : ExactLayer.exactCore c M ≤ Y := ExactLayer.exactCore_le_exactLayer hM
  have hle2 : conjSub (n : G) (ExactLayer.exactCore c J) ≤ Y := by
    have := conjSub_mono (n := (n : G)) (ExactLayer.exactCore_le_exactLayer hJ)
    rwa [conjSub_eq_self_of_mem n.2] at this
  have h4 := congrArg (Subgroup.map Y.subtype) hMn
  rw [Subgroup.map_subgroupOf_eq_of_le hle1, Subgroup.map_subgroupOf_eq_of_le hle2] at h4
  have h5 : ExactLayer.exactCore c M = ExactLayer.exactCore c (conjSub (n : G) J) := by
    have h6 := ExactLayer.exactCore_conjSub (n : G) c J
    rw [conj_eq_of_mem_centralizer_singleton hnC] at h6
    rw [h4, h6]
  exact Q3T7.eq_of_exactCore3_eq hΩg hcA hM
    (ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hnC hJ) h5

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
