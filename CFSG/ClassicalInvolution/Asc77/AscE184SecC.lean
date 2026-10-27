module

public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscIHThm4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.section_connected_of {G : Type} [Group G] {Y : Type} [Group Y] (ι : Y →* G)
    {Λ : Set (Subgroup Y)} {H : Subgroup G} {N₀ : Subgroup Y} [N₀.Normal]
    {K₁ : Subgroup Y} (hc : ConjInvariant Λ)
    (hexn : ∀ {L L' : Subgroup Y}, L ∈ Λ → L' ∈ Λ →
      L'.map (QuotientGroup.mk' N₀) ∈
        omegaStarNbr (quotFamily Λ N₀) (L.map (QuotientGroup.mk' N₀)) →
      ∃ n ∈ N₀, L' ∈ omegaStarNbr Λ (conjSub n L))
    (hexc : ∀ {K L : Subgroup Y}, K ∈ Λ → L ∈ Λ →
      K.map (QuotientGroup.mk' N₀) = L.map (QuotientGroup.mk' N₀) → ∃ n ∈ N₀, L = conjSub n K)
    (hN₀H : ∀ n ∈ N₀, ι n ∈ H) (hK₁ : K₁ ∈ Λ) (good : Subgroup Y → Prop)
    (hgood₀ : good K₁) (hgood : ∀ L ∈ Λ, ∀ L' ∈ Λ, good L → dstarAdj Λ L L' → good L')
    (hgoodH : ∀ L ∈ Λ, good L → L.map ι ≤ H)
    (hconn : ∀ M ∈ quotFamily Λ N₀,
      M ∈ dstarComp (quotFamily Λ N₀) (K₁.map (QuotientGroup.mk' N₀))) :
    ∀ J' ∈ Λ, J'.map ι ≤ H := by
  intro J' hJ'
  obtain ⟨M, hM', hMeq, hMgood⟩ := exists_good_lift (N := N₀) good hK₁ hgood₀
    (E187C.good_lift_step_of good hc hexn hgood) (hconn _ (map_mem_quotFamily hJ'))
  obtain ⟨n, hn, hJ'n⟩ := hexc hM' hJ' hMeq
  have hMH : M.map ι ≤ H := hgoodH M hM' hMgood
  rw [hJ'n]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ conjSub n M := hy
  rw [mem_conjSub_iff] at hy'
  have hyM : (n⁻¹ * y * n) ∈ M := hy'
  have h1 : (ι n)⁻¹ * ι y * ι n ∈ H := by
    have := hMH ⟨_, hyM, rfl⟩
    rwa [map_mul, map_mul, map_inv] at this
  have h2 : ι n * ((ι n)⁻¹ * ι y * ι n) * (ι n)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (hN₀H n hn) h1) (H.inv_mem (hN₀H n hn))
  simpa [mul_assoc] using h2

theorem E187C.section_hall_of {Y : Type} [Group Y] {Λ : Set (Subgroup Y)}
    {N₀ : Subgroup Y} [N₀.Normal] {K₁ : Subgroup Y} (hc : ConjInvariant Λ)
    (hexc : ∀ {K L : Subgroup Y}, K ∈ Λ → L ∈ Λ →
      K.map (QuotientGroup.mk' N₀) = L.map (QuotientGroup.mk' N₀) → ∃ n ∈ N₀, L = conjSub n K)
    (hK₁ : K₁ ∈ Λ)
    (horb : ∀ M ∈ quotFamily Λ N₀,
      ∃ y : Y ⧸ N₀, conjSub y (K₁.map (QuotientGroup.mk' N₀)) = M) :
    ∀ J ∈ Λ, ∃ y : Y, conjSub y K₁ = J := by
    intro J hJΛ
    obtain ⟨yb, hyb⟩ := horb _ (map_mem_quotFamily hJΛ)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N₀ yb
    have hKy : conjSub y K₁ ∈ Λ := hc y _ hK₁
    have himg : (conjSub y K₁).map (QuotientGroup.mk' N₀) = J.map (QuotientGroup.mk' N₀) := by
      rw [AscQuot.map_conjSub]
      exact hyb
    obtain ⟨n, -, hn⟩ := hexc hKy hJΛ himg
    exact ⟨n * y, by rw [conjSub_mul]; exact hn.symm⟩

theorem E187C.cent_restrict_of {Y : Subgroup G} (hcent : CentralizersSylowPairs Ω K H)
    (hKY : K ≤ Y) :
    CentralizersSylowPairs (restrictFamily Ω Y) (K.subgroupOf Y) (H.subgroupOf Y) := by
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc a ha ha1 ha2
  obtain ⟨L₀, hL₀, hL₀Y, rfl⟩ := hL.1
  obtain ⟨J₀, hJ₀, hJ₀Y, rfl⟩ : ∃ J₀ ∈ Ω, J₀ ≤ Y ∧ J = J₀.subgroupOf Y := by
    rcases hJ with rfl | h
    · exact ⟨L₀, hL₀, hL₀Y, rfl⟩
    · obtain ⟨J₀, hJ₀, hJ₀Y, rfl⟩ := h.1
      exact ⟨J₀, hJ₀, hJ₀Y, rfl⟩
  have hLm := twinSet_map hKY hL
  rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y] at hLm
  have hJm := kPerp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y, Subgroup.map_subgroupOf_eq_of_le hJ₀Y] at hJm
  have hR₁Ω : R₁.map Y.subtype ∈ RSet Ω := map_mem_RSet_restrict hR₁
  have hR₂Ω : R₂.map Y.subtype ∈ RSet Ω := map_mem_RSet_restrict hR₂
  have hR₁L₀ : R₁.map Y.subtype ≤ L₀ := by
    refine (Subgroup.map_mono hR₁L).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y]
  have hR₂J₀ : R₂.map Y.subtype ≤ J₀ := by
    refine (Subgroup.map_mono hR₂J).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJ₀Y]
  have hcm : Commutes (R₁.map Y.subtype) (R₂.map Y.subtype) ∨
      R₂.map Y.subtype = R₁.map Y.subtype := by
    rcases hc with hc | rfl
    · left
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hc x hx y hy)
    · right
      rfl
  have haG : (a : G) ∈ R₁.map Y.subtype ⊔ R₂.map Y.subtype := by
    have : (a : G) ∈ (R₁ ⊔ R₂).map Y.subtype := ⟨a, ha, rfl⟩
    rwa [Subgroup.map_sup] at this
  have hC := hcent L₀ hLm J₀ hJm _ _ hR₁Ω hR₁L₀ hR₂Ω hR₂J₀ hcm (a : G) haG
    (fun h => ha1 (Subtype.ext h)) (congrArg Subtype.val ha2)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hx
  exact Subgroup.mem_subgroupOf.mpr (hC this)


theorem MinCex.section_le_H (c : MinCex p f Ω K S R W H) {Y : Subgroup G} (hY : Y ≠ ⊤)
    {Λ : Set (Subgroup ↥Y)} (hΛ : HypOmegaMod p f Λ) (S₁ : Sylow 2 ↥Y)
    {K₁ K₁' R₁ R₁' : Subgroup ↥Y} (hK₁ : K₁ ∈ Λ) (hK₁' : K₁' ∈ twinSet Λ K₁) (hne : K₁' ≠ K₁)
    (hR₁ : R₁ ∈ RSet Λ) (hR₁K : R₁ ≤ K₁) (hR₁S : R₁ ≤ (S₁ : Subgroup ↥Y))
    (hR₁' : R₁' ∈ RSet Λ) (hR₁'K : R₁' ≤ K₁') (hR₁'S : R₁' ≤ (S₁ : Subgroup ↥Y))
    (hNH : oddCoreOf Y ≤ H) (hgen : Y ≤ ⨆ L ∈ Λ, L.map Y.subtype)
    (hY1 : (∀ J ∈ Λ, ∃ y : ↥Y, conjSub y K₁ = J) →
      ∀ J ∈ dstarComp Λ K₁, ∃ h ∈ H.subgroupOf Y, conjSub h K₁ = J)
    (hcent : CentralizersSylowPairs Λ K₁ (H.subgroupOf Y))
    (good : Subgroup ↥Y → Prop) (hgood₀ : good K₁)
    (hgood : ∀ L ∈ Λ, ∀ L' ∈ Λ, good L → dstarAdj Λ L L' → good L')
    (hgoodH : ∀ L ∈ Λ, good L → L.map Y.subtype ≤ H)
    (hA3 : (¬ ∀ L ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
        ∀ J ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
          J ∈ dstarComp (quotFamily Λ (classicalInvolutionOddCore ↥Y)) L) →
      ∀ L ∈ Λ, AEmpty Λ L) : Y ≤ H := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq ↥Y Λ hΛ N₀ hN₀odd
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
      (fun hL hL' hadj => exists_conj_omegaStarNbr hp hq hΛ hΛ' hN₀odd hL hL' hadj) (fun hK hL h => exists_conj_of_map_eq hp hq hΛ hN₀odd hK hL h) hN₀H hK₁ good hgood₀ hgood hgoodH hconn
    exact hgen.trans (iSup₂_le fun L hL => hmem L hL)
  ·
    have hdis : ¬ ∀ L ∈ quotFamily Λ N₀, ∀ J ∈ quotFamily Λ N₀,
        J ∈ dstarComp (quotFamily Λ N₀) L :=
      fun h => hconn fun M hM => h _ (map_mem_quotFamily hK₁) M hM
    have hΛA : ∀ L ∈ Λ, AEmpty Λ L := hA3 hdis
    have hAΛ' := aEmpty_quotFamily hp hq hΛ hΛ' hN₀odd hΛA
    rcases dichotomy_of_thm4 hp hq (thm4Below_of_citBelow c.stand.below) hlt hΛ' hOq hAΛ'
      (map_mem_quotFamily hK₁) with hc' | horb
    · exact absurd hc' hconn
    have hall := E187C.section_hall_of hΛ.conjInvariant
      (fun hK hL h => exists_conj_of_map_eq hp hq hΛ hN₀odd hK hL h) hK₁ horb
    obtain ⟨W₁, hW₁, hW₁S, hW₁n⟩ := exists_W_of_hypOmega hp hq hΛ S₁
    have hEStand : EStand p f Λ K₁ S₁ R₁ W₁ :=
      { odd := hp
        five := hq
        hyp := hΛ
        below := CITBelowU.mono p f (Subgroup.card_le_card_group Y) c.stand.below
        mem := hK₁
        aEmpty := hΛA K₁ hK₁
        twin := ⟨K₁', hK₁', hne, R₁', hR₁', hR₁'K, hR₁'S⟩
        hR := ⟨hR₁, hR₁K, hR₁S⟩
        hW := ⟨hW₁, hW₁S, hW₁n⟩ }
    have key := c.minimal ↥Y hltY Λ K₁ S₁ R₁ W₁ (H.subgroupOf Y) hEStand ⟨hY1 hall, hcent⟩
    exact Subgroup.subgroupOf_eq_top.mp key

end CFSG.ClassicalInvolution.Asc77
