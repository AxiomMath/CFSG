module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf2Base
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf3OddStand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Pf4Odd

variable [PrintedQuotOdd] [PrintedQuotCent]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.le_H (c : MinCexQ8 Ω K S R W H) : K ≤ H := by
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le
  intro k hk
  apply hcz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz.commute_of_mem hk).symm

theorem MinCexQ8.mem_of_conjSub_le (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {g : G} (hg : conjSub g R ≤ H) : g ∈ H := by
  obtain ⟨u, huR, hu4⟩ :=
    exists_orderOf_eq_four_of_mem_RSet_gen c.stand.hyp c.stand.hR.1
  exact c.mem_of_conj_mem hA hM (c.stand.hR.2.1 huR) hu4 (hg (conj_mem_conjSub huR))

theorem MinCexQ8.normalizer_le_of_le (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {Y : Subgroup G} (hRY : R ≤ Y) (hYH : Y ≤ H) :
    Subgroup.normalizer (Y : Set G) ≤ H :=
  E187C.normalizer_le_of_le_of (fun hg => c.mem_of_conjSub_le hA hM hg) hRY hYH

theorem MinCexQ8.exists_orderOf_four_mem_W (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J)
    (hTS : T ≤ (S : Subgroup G)) : ∃ u ∈ J ⊓ W, orderOf u = 4 ∧ u ∈ T := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  exact E187C.exists_orderOf_four_mem_W_of hM (c.exists_eta hA) hJ hT hTS
    (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
      exact ⟨hcyc, h4⟩)
    (fun hU => hΩ.isPGroup_of_mem_USet hU)

theorem MinCexQ8.exists_fourGroup (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K)
    {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) :
    ∃ U : Subgroup G, U ≤ R ⊔ R' ∧ U ≤ W ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      (∀ x ∈ U, x * x = 1) ∧ 4 ≤ Nat.card U ∧
      ∀ e ∈ U, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ H := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨U, hUR, hUW, hcomm, hsq, hU4, -⟩ := E187C.exists_fourGroup_of (H := ⊤)
    (fun hJ hT hTS => c.exists_orderOf_four_mem_W hA hM hJ hT hTS)
    (by obtain ⟨-, -, -, -, habel, -⟩ := c.exists_eta hA; exact habel)
    (fun hK hR hRK => Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hR hRK)
    (fun hK hJ hA hcard hAK hAJ => hΩ.eq_of_le_of_le hK hJ hA hcard hAK hAJ)
    (fun hK hJ hKJ hzK hzJ => hΩ.le_normalizer_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hJ hKJ hzK hzJ hA hB hAB =>
      hΩ.commutes_of_twin_of_isPGroup hK hJ hKJ hzK hzJ hA hB hAB)
    (fun _ _ _ _ _ _ _ _ _ _ => le_top)
    c.stand.mem hRR hRK hRS hK' hK'ne hR' hR'K' hR'S
  refine ⟨U, hUR, hUW, hcomm, hsq, hU4, fun e he he1 => ?_⟩
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  have hKperp : K' ∈ KPerp Ω K :=
    Set.mem_insert_of_mem _ ⟨hK'Ω, hK'ne, R', hR', hR'K', fun x hx =>
      hΩ.le_normalizer_of_twin hK'Ω c.stand.mem hK'ne hzK' hzK (hR'K' hx)⟩
  exact c.hyp.cent K c.stand.mem
    (inf_W_mem_USet' hΩ c.stand.hW.1 c.stand.hW.2.1 c.stand.mem hRR hRK hRS) K' hKperp R R' hRR
    hRK hRS hR' hR'K' hR'S (commutes_or_eq_of_le_sylow hΩ hRR hR' hRS hR'S) e (hUR he) (hUW he)
    he1 (hsq e he)

theorem MinCexQ8.oddCoreOf_le (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) {R' : Subgroup G}
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {Y : Subgroup G}
    (hY : R ⊔ R' ≤ Y) : oddCoreOf Y ≤ H := by
  obtain ⟨U, hUR, -, hcomm, hsq, hU4, hC⟩ := c.exists_fourGroup hA hM hK' hK'ne hR' hR'K' hR'S
  have hUY : U ≤ Y := hUR.trans hY
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U) (N := oddCoreOf Y)
    (J := H) this (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
    (fun u hu => mem_normalizer_oddCoreOf (hUY hu)) (odd_natCard_oddCoreOf Y)
    (fun e he he1 => inf_le_right.trans (hC e he he1))

theorem MinCexQ8.eq_bot_of_odd (c : MinCexQ8 Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) (hNH : N ≤ H) : N = ⊥ := by
  by_contra hne
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨Sb, Rb, Wb, hst, hCb⟩ := c.odd_quot_stand hN hNH
  have hΩ' : HypOmegaGen (quotFamily Ω N) := TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN
  have h1 := c.minimal (G ⧸ N) (AscE186.natCard_quotient_lt hne) (quotFamily Ω N)
    (K.map (QuotientGroup.mk' N)) Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst
    ⟨c.odd_quot_trans hN, hCb⟩
  exact c.proper (AscE186.eq_top_of_map_eq_top hNH h1)

theorem MinCexQ8.oddCore_le_H (c : MinCexQ8 Ω K S R W H) :
    classicalInvolutionOddCore G ≤ H := by
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨U, -, -, hcomm, hsq, hU4, hC⟩ := c.exists_fourGroup (etaAbelian_of_gen c.stand.hyp)
    (etaMeet_of_gen c.stand.hyp) hK'tw hK'ne hR' hR'K' hR'S
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U)
    (N := classicalInvolutionOddCore G) (J := H) this
    (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
    (fun u _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top u)
    (CFSG.ComponentClassification.OddCore.odd_card G)
    (fun e he he1 => inf_le_right.trans (hC e he he1))

theorem MinCexQ8.oddCore_eq_bot (c : MinCexQ8 Ω K S R W H) :
    classicalInvolutionOddCore G = ⊥ :=
  c.eq_bot_of_odd (CFSG.ComponentClassification.OddCore.odd_card G) c.oddCore_le_H

end Pf4Odd

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
