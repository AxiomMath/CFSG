module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf2Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

namespace ThmE

section Odd


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem quat_quot_odd (hN : Odd (Nat.card N))
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∀ L ∈ quotFamily Ω N, ∃ P : Subgroup (G ⧸ N), IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hq K hK
  have hPN : P ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP.2.1 hP.1 (odd_natCard_inf hN K)
  exact ⟨P.map (QuotientGroup.mk' N), isSylow2In_map_mk hN hP,
    ⟨(AscQuot.quotRestrictEquiv hPN).symm.trans e⟩⟩

theorem oddQuotHyp (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hN : Odd (Nat.card N)) :
    HypOmegaGen (quotFamily Ω N) ∧ Q3CL.ClassicalClause (quotFamily Ω N) ∧
      (∀ L ∈ quotFamily Ω N, ∃ P : Subgroup (G ⧸ N), IsSylow2In P L ∧
        Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))) :=
  ⟨TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN, TwinThmE.classicalClause_quot_odd hΩ hcls hN,
    quat_quot_odd hN hq⟩

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.odd_quot_trans (c : MinCex r Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hΩ' : HypOmegaGen (quotFamily Ω N) := TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN
  exact E187C.odd_quot_trans_of hΩ.conjInvariant
    (fun hL hL' hadj => C25J.exists_conj_omegaStarNbr_gen hΩ hΩ' hN hL hL' hadj) c.hyp.trans
    c.stand.mem

theorem MinCex.odd_quot_stand [PrintedQuotOdd r] (c : MinCex r Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) (hNH : N ≤ H) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStand r (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb ∧
      TwinThmEW.CentPairs (quotFamily Ω N) (Sb : Subgroup (G ⧸ N)) Wb
        (H.map (QuotientGroup.mk' N)) := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hΩ', hcls', hq'⟩ := oddQuotHyp hΩ c.stand.cls c.stand.quat hN
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 G Ω K S R W H c
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
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_, by rw [hSb]; exact hCb⟩
  exact
    { hyp := hΩ'
      cls := hcls'
      quat := hq'
      two := TwinThmE.two_quot_odd c.stand.two hN
      ih := EIH.mono (natCard_quotient_le N) c.stand.ih
      mem := map_mem_quotFamily hK
      aEmpty := TwinThmE.aEmpty_quot_odd hΩ hN hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hzK,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K') hzK'⟩,
        TwinThmE.map_ne_of_twin hΩ hN hK ⟨hK'Ω, z, hzK, hzK'⟩ hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω) (isSylow2In_map_mk hN hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK) (isSylow2In_map_mk hN hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }

theorem MinCex.le_H (c : MinCex r Ω K S R W H) : K ≤ H := by
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le
  intro k hk
  apply hcz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz.commute_of_mem hk).symm

theorem MinCex.mem_of_conjSub_le (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {g : G} (hg : conjSub g R ≤ H) : g ∈ H := by
  obtain ⟨u, huR, hu4⟩ :=
    TwinThmEW.exists_orderOf_eq_four_of_mem_RSet_gen c.stand.hyp c.stand.hR.1
  exact c.mem_of_conj_mem hA hM (c.stand.hR.2.1 huR) hu4 (hg (conj_mem_conjSub huR))

theorem MinCex.normalizer_le_of_le (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {Y : Subgroup G} (hRY : R ≤ Y) (hYH : Y ≤ H) :
    Subgroup.normalizer (Y : Set G) ≤ H :=
  E187C.normalizer_le_of_le_of (fun hg => c.mem_of_conjSub_le hA hM hg) hRY hYH

theorem MinCex.exists_orderOf_four_mem_W (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J)
    (hTS : T ≤ (S : Subgroup G)) : ∃ u ∈ J ⊓ W, orderOf u = 4 ∧ u ∈ T := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  exact E187C.exists_orderOf_four_mem_W_of hM (c.exists_eta hA) hJ hT hTS
    (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
      exact ⟨hcyc, h4⟩)
    (fun hU => hΩ.isPGroup_of_mem_USet hU)

theorem MinCex.exists_fourGroup (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω)
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
    (TwinThmEW.inf_W_mem_USet' hΩ c.stand.hW.1 c.stand.hW.2.1 c.stand.mem hRR hRK hRS) K' hKperp R R'
    hRR hRK hRS hR' hR'K' hR'S (TwinThmEW.commutes_or_eq_of_le_sylow hΩ hRR hR' hRS hR'S) e
    (hUR he) (hUW he) he1 (hsq e he)

theorem MinCex.oddCoreOf_le (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
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

theorem MinCex.eq_bot_of_odd [PrintedQuotOdd r] (c : MinCex r Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) (hNH : N ≤ H) : N = ⊥ := by
  by_contra hne
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨Sb, Rb, Wb, hst, hCb⟩ := c.odd_quot_stand hN hNH
  have hΩ' : HypOmegaGen (quotFamily Ω N) := TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN
  have h1 := c.minimal (G ⧸ N) (AscE186.natCard_quotient_lt hne) (quotFamily Ω N)
    (K.map (QuotientGroup.mk' N)) Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst
    ⟨c.odd_quot_trans hN, hCb⟩
  exact c.proper (AscE186.eq_top_of_map_eq_top hNH h1)

theorem MinCex.oddCore_le_H (c : MinCex r Ω K S R W H) :
    classicalInvolutionOddCore G ≤ H := by
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨U, -, -, hcomm, hsq, hU4, hC⟩ := c.exists_fourGroup (TwinThmEW.etaAbelian_of_gen c.stand.hyp)
    (TwinThmEW.etaMeet_of_gen c.stand.hyp) hK'tw hK'ne hR' hR'K' hR'S
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U)
    (N := classicalInvolutionOddCore G) (J := H) this
    (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
    (fun u _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top u)
    (CFSG.ComponentClassification.OddCore.odd_card G)
    (fun e he he1 => inf_le_right.trans (hC e he he1))

theorem MinCex.oddCore_eq_bot [PrintedQuotOdd r] (c : MinCex r Ω K S R W H) :
    classicalInvolutionOddCore G = ⊥ :=
  c.eq_bot_of_odd (CFSG.ComponentClassification.OddCore.odd_card G) c.oddCore_le_H

end Odd

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
