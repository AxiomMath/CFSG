module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Tz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc


section Pair

theorem omegaNbr_map_of_commutes_gen {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    {N : Subgroup Y} [N.Normal] (hΛ' : HypOmegaGen (quotFamily Λ N)) (hN : Odd (Nat.card N))
    {M₁ M₂ V₁ V₂ : Subgroup Y} (hM₁ : M₁ ∈ Λ) (hM₂ : M₂ ∈ Λ) (hV₁ : IsSylow2In V₁ M₁)
    (hV₂ : IsSylow2In V₂ M₂) (hc : Commutes V₁ V₂)
    (hV₂N : V₂ ≤ Subgroup.normalizer (M₁ : Set Y)) :
    M₂.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Λ N) (M₁.map (QuotientGroup.mk' N)) := by
  refine ⟨map_mem_quotFamily hM₂, (map_ne_of_commutes_sylow_gen hΛ' hN hM₁ hV₁ hV₂ hc).symm,
    V₂.map (QuotientGroup.mk' N),
    mem_RSet_of_isSylow2In (map_mem_quotFamily hM₂) (isSylow2In_map_mk hN hV₂),
    Subgroup.map_mono hV₂.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact Asc77.mk_mem_normalizer_map (hV₂N hx)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem isUniqueInvolution_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup G} {t : G} (hJ : J ∈ tqMembers3 Ω c) (ht : IsUniqueInvolution J t) :
    ∃ (htC : t ∈ Subgroup.centralizer ({c} : Set G))
      (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c),
      IsUniqueInvolution (secImg Ω c J)
        (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull Ω c)) :
          ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) := by
  have hU := isUniqueInvolution_coreAt_of_tq hΩ hc2 hJ ht
  have htC : t ∈ Subgroup.centralizer ({c} : Set G) :=
    TwinADescent.coreAt_le_centralizer c J hU.mem
  have h1 := isUniqueInvolution_subgroupOf hU (TwinADescent.coreAt_le_centralizer c J)
  have h2 := isUniqueInvolution_subgroupOf h1 (le_coreHull hJ)
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(coreHull Ω c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c)
  exact ⟨htC, le_coreHull hJ h1.mem,
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _) h2⟩

theorem omegaNbr_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J J' T T' : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hJ' : J' ∈ tqMembers3 Ω c)
    (hT : IsSylow2In T J) (hT' : IsSylow2In T' J')
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G)) (hT'c : T' ≤ Subgroup.centralizer ({c} : Set G))
    (hcomm : Commutes T T') (hT'J : T' ≤ Subgroup.normalizer (J : Set G)) :
    secImg Ω c J' ∈ omegaNbr (secFam Ω c) (secImg Ω c J) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(coreHull Ω c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c)
  have hΛ' : HypOmegaGen (secFam Ω c) := hypOmegaGen_secFam hΩ hc2
  have hTs : IsSylow2In T (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hT, hTc⟩
  have hT's : IsSylow2In T' (TwinADescent.coreAt c J') :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ'.2).mpr ⟨hT', hT'c⟩
  have hTX := (hTs.subgroupOf (TwinADescent.coreAt_le_centralizer c J)).subgroupOf (le_coreHull hJ)
  have hT'X := (hT's.subgroupOf (TwinADescent.coreAt_le_centralizer c J')).subgroupOf
    (le_coreHull hJ')
  have hTn : T' ≤ Subgroup.normalizer ((TwinADescent.coreAt c J : Subgroup G) : Set G) := by
    intro x hx
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have h6 := TwinADescent.conjSub_coreAt (hT'c hx) J
    rw [mem_normalizer_iff_conjSub_eq.mp (hT'J hx)] at h6
    exact h6
  have hT'NX := le_normalizer_subgroupOf_of_le (le_coreHull hJ)
    (le_normalizer_subgroupOf_of_le (TwinADescent.coreAt_le_centralizer c J) hTn)
  exact omegaNbr_map_of_commutes_gen hΛ' hodd (subgroupOf_mem_hullFam hJ)
    (subgroupOf_mem_hullFam hJ') hTX hT'X (commutes_subgroupOf (commutes_subgroupOf hcomm)) hT'NX

end Pair

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
