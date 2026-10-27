module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuotCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3Odd
public import CFSG.ClassicalInvolution.Asc77.AscC25J14b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section OddStand

variable [PrintedQuotOdd] [PrintedQuotCent]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem map_ne_of_twin (hΩ : HypOmegaGen Ω)
    (hN : Odd (Nat.card N)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.map_ne_of_twin hΩ hN hK hK' hne

theorem MinCexQ8.odd_quot_trans (c : MinCexQ8 Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hΩ' : HypOmegaGen (quotFamily Ω N) := TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN
  exact E187C.odd_quot_trans_of hΩ.conjInvariant
    (fun hL hL' hadj => C25J.exists_conj_omegaStarNbr_gen hΩ hΩ' hN hL hL' hadj) c.hyp.trans
    c.stand.mem

theorem MinCexQ8.odd_quot_stand (c : MinCexQ8 Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) (hNH : N ≤ H) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStandQ8 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb ∧
      CentPairs (quotFamily Ω N) (Sb : Subgroup (G ⧸ N)) Wb (H.map (QuotientGroup.mk' N)) := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hΩ', hcls', hq8'⟩ := oddQuotHypQ8 hΩ c.stand.cls c.stand.q8 hN
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3Q8 G Ω K S R W H c
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  set Sb : Sylow 2 (G ⧸ N) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S with hSbdef
  have hSb : (Sb : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S
  obtain ⟨Wb, hWb, hWbS', hWbn', hCb⟩ :=
    PrintedQuotOdd.exists_W G Ω K S R W H N c.stand c.hyp.cent hN hNH
  have hWbS : Wb ≤ (Sb : Subgroup (G ⧸ N)) := hSb ▸ hWbS'
  have hWbn : ∀ s ∈ (Sb : Subgroup (G ⧸ N)), conjSub s Wb = Wb := by
    rw [hSb]; exact hWbn'
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR' hR'K'
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_, hSb ▸ hCb⟩
  exact
    { hyp := hΩ'
      cls := hcls'
      q8 := hq8'
      two := two_quot_odd c.stand.two hN
      ih := EIH.mono (natCard_quotient_le N) c.stand.ih
      mem := map_mem_quotFamily hK
      aEmpty := aEmpty_quot_odd hΩ hN hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hzK,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K') hzK'⟩,
        map_ne_of_twin hΩ hN hK ⟨hK'Ω, z, hzK, hzK'⟩ hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω) (isSylow2In_map_mk hN hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK) (isSylow2In_map_mk hN hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }

end OddStand

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
