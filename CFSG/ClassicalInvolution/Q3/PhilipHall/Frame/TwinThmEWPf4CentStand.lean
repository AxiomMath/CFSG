module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf4Cent
public import CFSG.ClassicalInvolution.Asc77.AscE186Close
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmQ8CentEng
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuotCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section CentStand

variable [PrintedQuotOdd] [PrintedQuotCent]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

variable (Ω N) in
structure CentQuotQ8 : Prop extends CentQuotGen Ω N where
  central : N ≤ Subgroup.center G
  two : IsPGroup 2 ↥N

theorem centQuotQ8 (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) :
    CentQuotQ8 Ω N :=
  { centQuotGen hΩ hq8 hNc hmeet with central := hNc, two := hN2 }

theorem isSylow2In_map_cent (c : CentQuotQ8 Ω N) {J V : Subgroup G} (hJ : J ∈ Ω)
    (hV : IsSylow2In V J) :
    IsSylow2In (V.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N)) := by
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.CentEng.isSylow2In_map_cent
    c.toCentQuotGen hJ hV

theorem mem_dstarComp_of_twin_gen (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ twinSet Ω K) : L ∈ dstarComp Ω K :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.mem_dstarComp_of_twin_gen hΩ hK hL

theorem MinCexQ8.mem_of_conj_mem_dstar (c : MinCexQ8 Ω K S R W H) {M : Subgroup G}
    (hMS : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M) (hu4 : orderOf u = 4) {x : G}
    (hx : x * u * x⁻¹ ∈ H) : x ∈ H := by
  exact E187C.mem_of_conj_mem_dstar_of c.hyp.trans
    (fun hu hu4 hx => e18_2Q8 G Ω K S R W H c _ hu hu4 _ hx) hMS hu hu4 hx

theorem CentQuotQ8.exists_lift_dstarComp (c : CentQuotQ8 Ω N) {K : Subgroup G} (hK : K ∈ Ω) {Mb : Subgroup (G ⧸ N)}
    (hMb : Mb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ dstarComp Ω K, M.map (QuotientGroup.mk' N) = Mb := by
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.CentEng.exists_lift_dstarComp
    c.toCentQuotGen hK hMb

theorem MinCexQ8.cent_quot_stand (c : MinCexQ8 Ω K S R W H) (hc : CentQuotQ8 Ω N) (hNH : N ≤ H) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStandQ8 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb ∧
      CentPairs (quotFamily Ω N) (Sb : Subgroup (G ⧸ N)) Wb (H.map (QuotientGroup.mk' N)) := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3Q8 G Ω K S R W H c
  have hcls' : Q3CL.ClassicalClause (quotFamily Ω N) :=
    classicalClause_quot_cent hΩ hc.hyp' c.stand.cls hc.two hc.meet
  have hq8' := q8_quot_cent c.stand.q8 hc.meet
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  set Sb : Sylow 2 (G ⧸ N) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S with hSbdef
  have hSb : (Sb : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S
  obtain ⟨Wb, hWb, hWbS', hWbn', hCb⟩ :=
    PrintedQuotCent.exists_W G Ω K S R W H N c hc.central hc.two hNH hc.meet
  have hWbS : Wb ≤ (Sb : Subgroup (G ⧸ N)) := hSb ▸ hWbS'
  have hWbn : ∀ s ∈ (Sb : Subgroup (G ⧸ N)), conjSub s Wb = Wb := by
    rw [hSb]; exact hWbn'
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR' hR'K'
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_, hSb ▸ hCb⟩
  exact
    { hyp := hc.hyp'
      cls := hcls'
      q8 := hq8'
      two := two_quot_cent c.stand.two hc.meet
      ih := EIH.mono (natCard_quotient_le N) c.stand.ih
      mem := map_mem_quotFamily hK
      aEmpty := hc.aEmpty_quotFamily hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K hK) hzK,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K' hK'Ω) hzK'⟩,
        hc.map_ne_of_ne hK hK'Ω hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω) (isSylow2In_map_cent hc hK'Ω hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK) (isSylow2In_map_cent hc hK hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }

theorem MinCexQ8.cent_quot_trans (c : MinCexQ8 Ω K S R W H) (hc : CentQuotQ8 Ω N) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  intro Jb hJb
  obtain ⟨M, hM, hMeq⟩ := hc.exists_lift_dstarComp c.stand.mem hJb
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  refine ⟨QuotientGroup.mk' N h, Subgroup.mem_map_of_mem _ hhH, ?_⟩
  rw [← hMeq, ← hh, AscQuot.map_conjSub]

theorem MinCexQ8.eq_bot_of_central (c : MinCexQ8 Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hNH : N ≤ H)
    (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) : N = ⊥ := by
  by_contra hne
  have hc : CentQuotQ8 Ω N := centQuotQ8 c.stand.hyp c.stand.q8 hNc hN2 hmeet
  obtain ⟨Sb, Rb, Wb, hst, hCb⟩ := c.cent_quot_stand hc hNH
  have h1 := c.minimal (G ⧸ N) (AscE186.natCard_quotient_lt hne) (quotFamily Ω N)
    (K.map (QuotientGroup.mk' N)) Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst
    ⟨c.cent_quot_trans hc, hCb⟩
  exact c.proper (AscE186.eq_top_of_map_eq_top hNH h1)

end CentStand

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
