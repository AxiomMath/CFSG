module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESec

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement

namespace ThmE

section SecHom

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.section_le_H_hom (c : MinCex r Ω K S R W H) (hT4 : Thm4RTwinBelow r (Nat.card G))
    {Y : Type} [Group Y] [Finite Y] (ι : Y →* G) (hι : Function.Injective ι)
    (hY : Nat.card Y < Nat.card G) {Λ : Set (Subgroup Y)} (hΛ : HypOmegaGen Λ)
    (hΛcls : Q3CL.ClassicalClause Λ)
    (hΛq8 : ∀ L ∈ Λ, ∃ P : Subgroup Y, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hΛ2 : ∀ L ∈ Λ, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (S₁ : Sylow 2 Y)
    {K₁ K₁' R₁ R₁' : Subgroup Y} (hK₁ : K₁ ∈ Λ) (hK₁' : K₁' ∈ twinSet Λ K₁) (hne : K₁' ≠ K₁)
    (hR₁ : R₁ ∈ RSet Λ) (hR₁K : R₁ ≤ K₁) (hR₁S : R₁ ≤ (S₁ : Subgroup Y))
    (hR₁' : R₁' ∈ RSet Λ) (hR₁'K : R₁' ≤ K₁') (hR₁'S : R₁' ≤ (S₁ : Subgroup Y))
    (hNH : ∀ n ∈ classicalInvolutionOddCore Y, ι n ∈ H)
    (hY1 : (∀ J ∈ Λ, ∃ y : Y, conjSub y K₁ = J) →
      ∀ J ∈ dstarComp Λ K₁, ∃ h ∈ H.comap ι, conjSub h K₁ = J)
    (hWex : ∃ W₁ ∈ WSet Λ, W₁ ≤ (S₁ : Subgroup Y) ∧
      (∀ s ∈ (S₁ : Subgroup Y), conjSub s W₁ = W₁) ∧ TwinThmEW.CentPairs Λ (S₁ : Subgroup Y) W₁ (H.comap ι))
    (good : Subgroup Y → Prop) (hgood₀ : good K₁)
    (hgood : ∀ L ∈ Λ, ∀ L' ∈ Λ, good L → dstarAdj Λ L L' → good L')
    (hgoodH : ∀ L ∈ Λ, good L → L.map ι ≤ H)
    (hA3 : (¬ ∀ L ∈ quotFamily Λ (classicalInvolutionOddCore Y),
        ∀ J ∈ quotFamily Λ (classicalInvolutionOddCore Y),
          J ∈ dstarComp (quotFamily Λ (classicalInvolutionOddCore Y)) L) →
      ∀ L ∈ Λ, AEmpty Λ L) : ∀ L ∈ Λ, L.map ι ≤ H := by
  set N₀ : Subgroup Y := classicalInvolutionOddCore Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card Y
  have hΛ' : HypOmegaGen (quotFamily Λ N₀) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ hN₀odd
  have hΛq8' := quat_quot_odd hN₀odd hΛq8
  have hΛ2' := two_quot_odd hΛ2 hN₀odd
  have hltY := hY
  have hlt : Nat.card (Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (Y ⧸ N₀) ≤ Nat.card Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hN₀H : ∀ n ∈ N₀, ι n ∈ H := hNH
  by_cases hconn : ∀ M ∈ quotFamily Λ N₀,
      M ∈ dstarComp (quotFamily Λ N₀) (K₁.map (QuotientGroup.mk' N₀))
  ·
    have hmem := E187C.section_connected_of ι hΛ.conjInvariant
      (fun hL hL' hadj => C25J.exists_conj_omegaStarNbr_gen hΛ hΛ' hN₀odd hL hL' hadj) (fun hK hL h => Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd hK hL h) hN₀H hK₁ good hgood₀ hgood hgoodH hconn
    exact hmem
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
        ih := EIH.mono hY.le c.stand.ih
        mem := hK₁
        aEmpty := hΛA K₁ hK₁
        twin := ⟨K₁', hK₁', hne, R₁', hR₁', hR₁'K, hR₁'S⟩
        hR := ⟨hR₁, hR₁K, hR₁S⟩
        hW := ⟨hW₁, hW₁S, hW₁n⟩ }
    have key := c.minimal Y hltY Λ K₁ S₁ R₁ W₁ (H.comap ι) hEStand ⟨hY1 hall, hCW₁⟩
    intro L _
    exact Subgroup.map_le_iff_le_comap.mpr (by rw [key]; exact le_top)

end SecHom

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
