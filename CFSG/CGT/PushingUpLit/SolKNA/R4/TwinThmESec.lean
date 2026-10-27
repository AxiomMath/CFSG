module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf7Sec
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

namespace ThmE

section Sec


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem quat_all
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
  intro J hJ P hP
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ := hq J hJ
  obtain ⟨k, -, hk⟩ := exists_conjSub_eq_of_isSylow2In hP₀ hP
  subst hk
  exact ⟨(Subgroup.equivMapOfInjective P₀ (MulAut.conj k).toMonoidHom
    (MulAut.conj k).injective).symm.trans e⟩

theorem quat_restrict
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (Y : Subgroup G) :
    ∀ L ∈ restrictFamily Ω Y, ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
  rintro _ ⟨L, hL, hLY, rfl⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hq L hL
  exact ⟨P.subgroupOf Y, hP.subgroupOf hLY,
    ⟨(Subgroup.subgroupOfEquivOfLe (hP.1.trans hLY)).trans e⟩⟩

theorem twinT4Hyp_of (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (hO : classicalInvolutionOddCore G = ⊥) :
    TwinT4Hyp r G Ω :=
  ⟨hΩ, h2, quat_all hq8, hA, hO⟩

theorem dichotomy_of_thm4Twin {n : ℕ} (h4 : Thm4RTwinBelow r n) (hlt : Nat.card G < n)
    (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hO : classicalInvolutionOddCore G = ⊥) (hA : ∀ L ∈ Ω, AEmpty Ω L) {L : Subgroup G}
    (hL : L ∈ Ω) :
    (∀ M ∈ Ω, M ∈ dstarComp Ω L) ∨ (∀ M ∈ Ω, ∃ y : G, conjSub y L = M) := by
  have hT := twinT4Hyp_of hΩ hq8 h2 hA hO
  by_cases hall : ∀ M ∈ Ω, ∃ y : G, conjSub y L = M
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨M₀, hM₀, hM₀c⟩ := hall
  have hLM₀ : M₀ ≠ L := fun h => hM₀c 1 (by rw [conjSub_one, h])
  have hc0 : Commutes L M₀ := h4.apply hlt hT hL hM₀ (fun ⟨g, hg⟩ => hM₀c g hg)
  have hadj0 : dstarAdj Ω L M₀ := TwinThmE.dstarAdj_of_commutes_gen hΩ hM₀ hLM₀ hc0.symm
  intro M hM
  by_cases hMc : ∃ y : G, conjSub y L = M
  · obtain ⟨y, rfl⟩ := hMc
    have hnot : ¬ ∃ g : G, conjSub g (conjSub y L) = M₀ := by
      rintro ⟨g, hg⟩
      exact hM₀c (g * y) (by rw [conjSub_mul]; exact hg)
    have hc1 : Commutes (conjSub y L) M₀ := h4.apply hlt hT hM hM₀ hnot
    have hne : M₀ ≠ conjSub y L := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj0)
      (TwinThmE.dstarAdj_of_commutes_gen hΩ hM hne.symm hc1)
  · have hc : Commutes L M := h4.apply hlt hT hL hM (fun ⟨g, hg⟩ => hMc ⟨g, hg⟩)
    have hne : M ≠ L := fun h => hMc ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.single (TwinThmE.dstarAdj_of_commutes_gen hΩ hM hne hc.symm)

theorem MinCex.section_le_H (c : MinCex r Ω K S R W H) (hT4 : Thm4RTwinBelow r (Nat.card G))
    {Y : Subgroup G} (hY : Y ≠ ⊤) {Λ : Set (Subgroup ↥Y)} (hΛ : HypOmegaGen Λ)
    (hΛcls : Q3CL.ClassicalClause Λ)
    (hΛq8 : ∀ L ∈ Λ, ∃ P : Subgroup ↥Y, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hΛ2 : ∀ L ∈ Λ, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (S₁ : Sylow 2 ↥Y)
    {K₁ K₁' R₁ R₁' : Subgroup ↥Y} (hK₁ : K₁ ∈ Λ) (hK₁' : K₁' ∈ twinSet Λ K₁) (hne : K₁' ≠ K₁)
    (hR₁ : R₁ ∈ RSet Λ) (hR₁K : R₁ ≤ K₁) (hR₁S : R₁ ≤ (S₁ : Subgroup ↥Y))
    (hR₁' : R₁' ∈ RSet Λ) (hR₁'K : R₁' ≤ K₁') (hR₁'S : R₁' ≤ (S₁ : Subgroup ↥Y))
    (hNH : oddCoreOf Y ≤ H) (hgen : Y ≤ ⨆ L ∈ Λ, L.map Y.subtype)
    (hY1 : (∀ J ∈ Λ, ∃ y : ↥Y, conjSub y K₁ = J) →
      ∀ J ∈ dstarComp Λ K₁, ∃ h ∈ H.subgroupOf Y, conjSub h K₁ = J)
    (hWex : ∃ W₁ ∈ WSet Λ, W₁ ≤ (S₁ : Subgroup ↥Y) ∧
      (∀ s ∈ (S₁ : Subgroup ↥Y), conjSub s W₁ = W₁) ∧ TwinThmEW.CentPairs Λ (S₁ : Subgroup ↥Y) W₁ (H.subgroupOf Y))
    (good : Subgroup ↥Y → Prop) (hgood₀ : good K₁)
    (hgood : ∀ L ∈ Λ, ∀ L' ∈ Λ, good L → dstarAdj Λ L L' → good L')
    (hgoodH : ∀ L ∈ Λ, good L → L.map Y.subtype ≤ H)
    (hA3 : (¬ ∀ L ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
        ∀ J ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
          J ∈ dstarComp (quotFamily Λ (classicalInvolutionOddCore ↥Y)) L) →
      ∀ L ∈ Λ, AEmpty Λ L) : Y ≤ H := by
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : HypOmegaGen (quotFamily Λ N₀) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ hN₀odd
  have hΛq8' := quat_quot_odd hN₀odd hΛq8
  have hΛ2' := two_quot_odd hΛ2 hN₀odd
  have hltY := natCard_lt_of_ne_top hY
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hN₀H : ∀ n ∈ N₀, (n : G) ∈ H := fun n hn => hNH ⟨n, hn, rfl⟩
  by_cases hconn : ∀ M ∈ quotFamily Λ N₀,
      M ∈ dstarComp (quotFamily Λ N₀) (K₁.map (QuotientGroup.mk' N₀))
  ·
    have hmem := E187C.section_connected_of Y.subtype hΛ.conjInvariant
      (fun hL hL' hadj => C25J.exists_conj_omegaStarNbr_gen hΛ hΛ' hN₀odd hL hL' hadj) (fun hK hL h => Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd hK hL h) hN₀H hK₁ good hgood₀ hgood hgoodH hconn
    exact hgen.trans (iSup₂_le fun L hL => hmem L hL)
  ·
    have hdis : ¬ ∀ L ∈ quotFamily Λ N₀, ∀ J ∈ quotFamily Λ N₀,
        J ∈ dstarComp (quotFamily Λ N₀) L :=
      fun h => hconn fun M hM => h _ (map_mem_quotFamily hK₁) M hM
    have hΛA : ∀ L ∈ Λ, AEmpty Λ L := hA3 hdis
    have hAΛ' := aEmpty_quot_odd hΛ hN₀odd hΛA
    rcases dichotomy_of_thm4Twin hT4 hlt hΛ' hΛq8' hΛ2' hOq hAΛ'
      (map_mem_quotFamily hK₁) with hc' | horb
    · exact absurd hc' hconn
    have hall := E187C.section_hall_of hΛ.conjInvariant
      (fun hK hL h => Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd hK hL h) hK₁ horb
    obtain ⟨W₁, hW₁, hW₁S, hW₁n, hCW₁⟩ := hWex
    have hEStand : EStand r Λ K₁ S₁ R₁ W₁ :=
      { hyp := hΛ
        cls := hΛcls
        quat := hΛq8
        two := hΛ2
        ih := EIH.mono (Subgroup.card_le_card_group Y) c.stand.ih
        mem := hK₁
        aEmpty := hΛA K₁ hK₁
        twin := ⟨K₁', hK₁', hne, R₁', hR₁', hR₁'K, hR₁'S⟩
        hR := ⟨hR₁, hR₁K, hR₁S⟩
        hW := ⟨hW₁, hW₁S, hW₁n⟩ }
    have key := c.minimal ↥Y hltY Λ K₁ S₁ R₁ W₁ (H.subgroupOf Y) hEStand ⟨hY1 hall, hCW₁⟩
    exact Subgroup.subgroupOf_eq_top.mp key

end Sec

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
