module

public import CFSG.GH74.Generic.BProg.B3.S3Pump306aLayer
public import CFSG.GH74.Generic.BProg.B3.S3Pump306aAltY
public import CFSG.GH74.Generic.BProg.B3.S3Pump306aExcl
public import CFSG.GH74.Generic.BProg.B3.S3Pump306aSetup
public import CFSG.GH74.Generic.BProg.B3.S3SL2Pump
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial Subgroup
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {x y : G} {K A T : Subgroup G}

theorem barSub_pumpup_of_F
    (hC2 : C2CoverInput) (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    (hLO : pPrimeCoreOf 2 (Ly K y) ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G)))
    {H : Subgroup G} (hHc : IsPCompIn 2 (centralizer ({y} : Set G)) H)
    (hxH : x ∈ normalizer (H : Set G)) (hLH : Ly K y ≤ H) :
    barSub y H = barSub y (Ly K y) := by
  classical
  refine le_antisymm ?_ (barSub_mono hLH)
  by_contra hle
  have hne : barSub y (Ly K y) ≠ barSub y H := fun heq => hle (heq ▸ le_rfl)
  have hcfg := cfg_of_setup30 h hT
  have hx : orderOf x = 2 := hcfg.hx
  have hy : orderOf y = 2 := hcfg.hy
  have hxy : x ∈ centralizer ({y} : Set G) := TwoThin.mem_centralizer_symm (hcfg.hK.1 hcfg.hyK)
  have hyL : y ∈ Ly K y := (Setup30.layer h).2.1
  have hyH : y ∈ H := hLH hyL
  have hcomm1 := hF.2.2.2.2
  have hY : Gen4 (CentralizerBar y) := gen4_bar h.hyp.gen4 y
  have hYO := pPrimeCore_bar_eq_bot y
  have hHb : CFSG.IsComponent (barSub y H) := FalseCtxS45Comp.isComponent_bar hHc
  have hs : orderOf (proj y ⟨x, hxy⟩) = 2 := GLS.C3.Layer1.PumpCalc.orderOf_sbar hx hxy
  have hs2 : proj y ⟨x, hxy⟩ * proj y ⟨x, hxy⟩ = 1 := by
    have := pow_orderOf_eq_one (proj y ⟨x, hxy⟩)
    rwa [hs, pow_two] at this
  have hsN : proj y ⟨x, hxy⟩ ∈ normalizer ((barSub y H : Subgroup (CentralizerBar y)) : Set _) :=
    ObsPump.bar_mem_normalizer hHc.1 hxy hxH
  have hxc : proj y ⟨x, hxy⟩ ∈ _root_.commutator (CentralizerBar y) := by
    obtain ⟨c, hc, hcx⟩ := hcomm1
    have h1 : proj y ⟨x, hxy⟩ ∈ (_root_.commutator ↥(centralizer ({y} : Set G))).map (proj y) := by
      refine ⟨c, hc, ?_⟩
      have : c = ⟨x, hxy⟩ := Subtype.ext hcx
      rw [this]
    have h2 : (_root_.commutator ↥(centralizer ({y} : Set G))).map (proj y) ≤
        _root_.commutator (CentralizerBar y) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 h1
  have hKP : GLS.IsKProperSimple G :=
    ⟨h.hyp.simple, h.hyp.nonab, CFSG.GH74.kProper_of_kgh h.hyp.kgh⟩
  have hCal : InCalK2 ↥(barSub y H) := GLS.inCalK2_of_isComponent hKP hy hHb
  have hGH : GHList (↥(barSub y H) ⧸ center ↥(barSub y H)) :=
    ghList_of_quasisimple h.hyp.simple h.hyp.nonab h.hyp.kgh hy hHb.1
  have hZ2 : IsPGroup 2 ↥(center ↥(barSub y H)) := by
    have := pCore_isPGroup (p := 2) (G := ↥(barSub y H))
    rw [← hCal.2.1] at this
    exact this
  have hZ1 : center ↥(barSub y H) ≠ ⊥ := center_bar_ne_bot hy hyH
  have hG2 : ¬ InG2 ↥(barSub y H) := not_inG2_bar h hHc hyH
  have hLb := layer_bar_isPCompIn h hT hxy hLH
  have hLlay := layer_bar_eq h hT hF hxy hHc hLH
  have hLsl2 := hasSL2_bar h hLO
  have htable := kg_sl2_pumpup_of_input hC2 hY hYO hHb hZ2 hZ1 hGH hCal hG2 hs hsN hLb hLlay hLsl2 hne
  obtain ⟨q, hqodd, hq5, hLbcard⟩ := S3SL2Basic.sl2_card_data hLsl2
  have hLbH : barSub y (Ly K y) ≤ barSub y H := barSub_mono hLH
  have hLbc : ∀ l ∈ barSub y (Ly K y), proj y ⟨x, hxy⟩ * l = l * proj y ⟨x, hxy⟩ := fun l hl =>
    (mem_centralizer_singleton_iff.1 (hLb.1 hl).1).symm
  have hperf : ⁅barSub y (Ly K y), barSub y (Ly K y)⁆ = barSub y (Ly K y) :=
    GLS.C3.Layer1.Bk.perfect_of_isPCompIn hLb
  have hLbna : ∃ a ∈ barSub y (Ly K y), ∃ b ∈ barSub y (Ly K y), a * b ≠ b * a :=
    S3SL2Basic.exists_noncomm_of_perfect hperf
      (by rw [hLbcard]; have := S3SL2Basic.sl2_card_ge hq5; omega)
  have hns : ∃ g ∈ barSub y H, proj y ⟨x, hxy⟩ * g ≠ g * proj y ⟨x, hxy⟩ := by
    by_contra hcon
    push Not at hcon
    exact hne (S3SL2Basic.eq_of_centralizes hHb.1 hcon hLb hLbna)
  have hzc : ∀ g : CentralizerBar y, g * proj y ⟨y, yy_mem y⟩ = proj y ⟨y, yy_mem y⟩ * g :=
    fun g => ybar_central y g
  have hzH : proj y ⟨y, yy_mem y⟩ ∈ barSub y H := proj_mem_barSub (yy_mem y) hyH
  have hz1 : proj y ⟨y, yy_mem y⟩ ≠ 1 := ybar_ne_one hy
  rcases htable with hSL2 | hA7 | hA8 | hL34
  ·
    obtain ⟨F, hFf, hFfin, hFodd, ⟨e⟩⟩ := hSL2
    have h3 : 3 < Nat.card F := by
      have hdvd : Nat.card ↥(barSub y (Ly K y)) ∣ Nat.card ↥(barSub y H) :=
        Subgroup.card_dvd_of_le hLbH
      have hcardH : Nat.card ↥(barSub y H) = Nat.card F * (Nat.card F ^ 2 - 1) := by
        rw [Nat.card_congr e.toEquiv]
        exact TwoThin.card_statedSL_two F
      have hle120 := S3SL2Basic.sl2_card_ge hq5
      have hpos : 0 < Nat.card ↥(barSub y H) := Nat.card_pos
      have hLb' : Nat.card ↥(barSub y (Ly K y)) ≤ Nat.card ↥(barSub y H) := Nat.le_of_dvd hpos hdvd
      rw [hLbcard] at hLb'
      rw [hcardH] at hLb'
      by_contra hF3
      push Not at hF3
      have hF1 : 0 < Nat.card F := Nat.card_pos
      interval_cases hN : Nat.card F <;> omega
    exact false_of_sl2 hY hHb hFodd h3 (e.trans (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F)) hs2 hsN hxc
      hLbH hLbc hLbna hns
  · exact false_of_alt hY (n := 7) (by norm_num) (by norm_num) hHb hA7 hzc hzH hz1 hs2 hsN hxc hns
      hLbH hLbc hLsl2
  · exact false_of_alt hY (n := 8) (by norm_num) (by norm_num) hHb hA8 hzc hzH hz1 hs2 hsN hxc hns
      hLbH hLbc hLsl2
  · exact false_of_l34 hY hHb hZ2 hZ1 hL34

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
