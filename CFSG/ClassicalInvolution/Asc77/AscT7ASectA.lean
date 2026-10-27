module

public import CFSG.ClassicalInvolution.Asc77.AscE184SecE
public import CFSG.ClassicalInvolution.Asc77.AscIH8Red
public import CFSG.ClassicalInvolution.Asc77.AscT3Stmt

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic AscE184Sect

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem exists_conj_mem_dstarComp_of_conn (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A) {B : Subgroup G}
    (hB : B ∈ sectionMembers Ω A)
    (hconn : ∀ L ∈ quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        (classicalInvolutionOddCore ↥(sectionHull Ω A)),
      ∀ M ∈ quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        (classicalInvolutionOddCore ↥(sectionHull Ω A)),
      M ∈ dstarComp (quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        (classicalInvolutionOddCore ↥(sectionHull Ω A))) L)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ sectionMembers Ω A) :
    ∃ n ∈ classicalInvolutionOddCore ↥(sectionHull Ω A), ∃ J ∈ sectionMembers Ω A,
      J ∈ dstarComp Ω B ∧ J₁ = conjSub (n : G) J := by
  set Y := sectionHull Ω A with hYdef
  set Λ : Set (Subgroup ↥Y) := restrictFamily (sectionFamily Ω A) Y with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f Λ := hypOmegaMod_sectionFamily hp hq hΩ hA
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq ↥Y Λ hΛ N₀ hN₀odd
  have hBΛ : (secMember A B).subgroupOf Y ∈ Λ := subgroupOf_secMember_mem hB
  have hJ₁Λ : (secMember A J₁).subgroupOf Y ∈ Λ := subgroupOf_secMember_mem hJ₁
  obtain ⟨M, hM', hMeq, hMgood⟩ := exists_good_lift (N := N₀) (sectionGood Ω A B) hBΛ
    ⟨B, hB, rfl, Relation.ReflTransGen.refl⟩
    (fun L hL L' hL' hgL hadj => by
      obtain ⟨-, hadj | hadj⟩ := hadj
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr hp hq hΛ hΛ' hN₀odd hL hL' hadj
        have h1 := omegaStarNbr_conj hΛ.conjInvariant hn' (n⁻¹ : ↥Y)
        rw [conjSub_inv_conjSub] at h1
        have hnn : QuotientGroup.mk' N₀ n⁻¹ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (N₀.inv_mem hn)
        refine ⟨conjSub n⁻¹ L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact sectionGood_step hp hq hΩ hA (hΛ.conjInvariant _ L' hL') hgL
            ⟨hΛ.conjInvariant _ L' hL', Or.inl h1⟩
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr hp hq hΛ hΛ' hN₀odd hL' hL hadj
        have hnn : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
        refine ⟨conjSub n L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact sectionGood_step hp hq hΩ hA (hΛ.conjInvariant _ L' hL') hgL
            ⟨hΛ.conjInvariant _ L' hL', Or.inr hn'⟩)
    (hconn _ (map_mem_quotFamily hBΛ) _ (map_mem_quotFamily hJ₁Λ))
  obtain ⟨n, hn, hJ₁n⟩ := exists_conj_of_map_eq hp hq hΛ hN₀odd hM' hJ₁Λ hMeq
  obtain ⟨J, hJ, rfl, hJB⟩ := hMgood
  refine ⟨n, hn, J, hJ, hJB, ?_⟩
  have hnC : (n : G) ∈ Subgroup.centralizer (A : Set G) := sectionHull_le_centralizer Ω A n.2
  have h1 : (secMember A J₁).subgroupOf Y =
      (secMember A (conjSub (n : G) J)).subgroupOf Y := by
    rw [hJ₁n, ← conjSub_secMember hnC]
    exact conjSub_subgroupOf Y n (secMember A J)
  have h2 : secMember A J₁ = secMember A (conjSub (n : G) J) := by
    have hle1 : secMember A J₁ ≤ Y := le_sectionHull hJ₁
    have hle2 : secMember A (conjSub (n : G) J) ≤ Y :=
      le_sectionHull (conjSub_mem_sectionMembers hΩ hnC hJ)
    have := congrArg (Subgroup.map Y.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hle1, Subgroup.map_subgroupOf_eq_of_le hle2] at this
  exact eq_of_secMember_eq hp hΩ hA hJ₁ (conjSub_mem_sectionMembers hΩ hnC hJ) h2

section Twin

@[expose] def TwinTriple {X : Type} [Group X] (Φ : Set (Subgroup X)) : Prop :=
  ∃ K ∈ Φ, ∃ K' ∈ twinSet Φ K, K' ≠ K ∧ ∃ J ∈ omegaNbr Φ K, J ∈ omegaNbr Φ K'

variable (p f) in
@[expose] def DStarConnectedTwin : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), HypOmegaMod p f Φ →
    classicalInvolutionOddCore X = ⊥ → (∀ L ∈ Φ, AEmpty Φ L) →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) → OmegaLie p f Φ → TwinTriple Φ →
      T3.DStarConnected Φ

theorem dstarConnected_quot_of_twinTriple (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A) (hY : sectionHull Ω A ≠ ⊤)
    (hBelow : CITBelowU p f (Nat.card G)) (h3s : T3.Thm3SectBelow p f (Nat.card G))
    (hMF : DStarConnectedTwin p f)
    (htt : TwinTriple (quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
      (classicalInvolutionOddCore ↥(sectionHull Ω A)))) :
    T3.DStarConnected (quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
      (classicalInvolutionOddCore ↥(sectionHull Ω A))) := by
  set Y := sectionHull Ω A with hYdef
  set Λ : Set (Subgroup ↥Y) := restrictFamily (sectionFamily Ω A) Y with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f Λ := hypOmegaMod_sectionFamily hp hq hΩ hA
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq ↥Y Λ hΛ N₀ hN₀odd
  have hltY := natCard_lt_of_ne_top hY
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  by_contra hdis
  have hΛA : ∀ L ∈ Λ, AEmpty Λ L := h3s hp hq ↥Y hltY Λ hΛ hdis
  have hAΛ' := aEmpty_quotFamily hp hq hΛ hΛ' hN₀odd hΛA
  obtain ⟨K₀, hK₀, -⟩ := id htt
  rcases dichotomy_of_thm4 hp hq (thm4Below_of_citBelow hBelow) hlt hΛ' hOq hAΛ' hK₀ with hc | horb
  · exact hdis (T3.dstarConnected_of_pivot hK₀ hc)
  · have htrans : ∀ K ∈ quotFamily Λ N₀, ∀ L ∈ quotFamily Λ N₀, ∃ g : ↥Y ⧸ N₀, conjSub g K = L := by
      intro K hK L hL
      obtain ⟨y₁, hy₁⟩ := horb K hK
      obtain ⟨y₂, hy₂⟩ := horb L hL
      exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
    obtain ⟨D⟩ := ih8_exists_omegaLie hBelow hΛ'.conjInvariant hΛ'.classical ⟨_, hK₀⟩ hOq hlt
    exact hdis (hMF _ _ hΛ' hOq hAΛ' htrans D htt)

end Twin

end CFSG.ClassicalInvolution.Asc77
