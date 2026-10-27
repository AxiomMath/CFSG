module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedGlue
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerListK
public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.LocalAnalysis.EvenBN

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem isSimpleGroup_L (d : Data G h) : IsSimpleGroup d.L :=
  d.e.isSimpleGroup_congr.2 (CFSG.Quasithin.H13.Sec53F.Unit.isSimpleGroup_hypPSU_five h)

theorem Hyp.not_comm_L (hd : d.Hyp) : ¬ ∀ x ∈ d.L, ∀ y ∈ d.L, x * y = y * x := by
  intro hcomm
  haveI := d.isSimpleGroup_L
  obtain ⟨x, hx⟩ := exists_ne (1 : d.L)
  have hcen : x ∈ Subgroup.center d.L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2 x x.2)
  rw [hd.setting.center_eq_bot] at hcen
  exact hx (Subgroup.mem_bot.1 hcen)

theorem Hyp.even_card_L (hd : d.Hyp) : Even (Nat.card d.L) := by
  have h1 : Nat.card d.P ∣ Nat.card d.L := Subgroup.card_dvd_of_le d.P_le_L
  rw [d.card_P] at h1
  have h0 : f ≠ 0 := by have := hd.two_le; omega
  exact even_iff_two_dvd.2 ((dvd_pow (dvd_pow_self 2 h0) (by norm_num)).trans h1)

theorem Hyp.isSylowOf_tP (hd : d.Hyp) : IsSylowOf 2 d.tP (d.L ⊔ zpowers d.t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL := d.P_le_L
  have htt := hd.t_mul_t
  have hLt := hd.L_le_centralizer
  have hPt : d.P ≤ centralizer ({d.t} : Set G) := hPL.trans hLt
  have htL := hd.t_not_mem_L
  have htP : d.t ∉ d.P := fun h => htL (hPL h)
  refine isSylowOf_of_card (sup_le le_sup_right (hPL.trans le_sup_left)) ?_
  have h1 := Common.SwapUnique.card_sup_zpowers_of_le_centralizer htt hPt htP
  have h2 := Common.SwapUnique.card_sup_zpowers_of_le_centralizer htt hLt htL
  have hS := (isSylowOf_P d).card_eq
  have hL0 : Nat.card d.L ≠ 0 := Nat.card_pos.ne'
  have hf2 : (Nat.card (d.L ⊔ zpowers d.t : Subgroup G)).factorization 2 =
      (Nat.card d.L).factorization 2 + 1 := by
    rw [h2, Nat.factorization_mul (by norm_num) hL0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
    ring
  rw [Data.tP, sup_comm, h1, hf2, hS]
  ring

end Data

namespace CaseBParts

open Data

structure OwnParts : Prop where
  p11 : Sec52SylowStatement
  p12 : Sec52FactorsStatement
  p13 : Sec52SInvStatement
  p14 : Sec52GenStatement
  p15 : Sec52CommStatement
  p16 : Sec52Statement
  p21 : HGenStatement
  p22 : NormalizerTPStatement
  p3 : PerfectNormalizerStatement
  p41 : InvolutoryFixedElemAbStatement
  p42 : NonSwapStatement

variable (op : OwnParts) {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

include op

theorem OwnParts.false_of_caseBHyp (hB : d.CaseBHyp) : False := by
  obtain ⟨c⟩ := hB.nonempty_caseBData
  have hd := hB.hyp
  have h11 := op.p11 G f K h d hB c
  have h12 := op.p12 G f K h d hB c h11
  have h13 := op.p13 G f K h d hB c h11 h12
  have h14 := op.p14 G f K h d hB c h11 h12 h13
  have h15 := op.p15 G f K h d hB c h11 h12 h13 h14
  have h52 := op.p16 G f K h d hB c h15
  have hgen := op.p21 G f K h d hB c h11 h52
  have hN := op.p22 G f K h d hB
  have hperf := op.p3 G f K h d hB c h52
  have hnorm := op.p42 op.p41 G f K h d hB c h52
  haveI : IsSimpleGroup G := hd.setting.std.simple
  have hNR : normalizer (d.tP : Set G) ≤
      normalizer ((c.Nc ⊔ c.Nc.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) := by
    have e : c.Nc ⊔ c.Nc.map (MulAut.conj d.t).toMonoidHom = d.L ⊔ d.V := hgen
    rw [e]
    exact hN
  exact Common.false_of_swap_configuration (G := G) (t := d.t) hd.t_two (L := d.L) (G₀ := c.Nc)
    (R := d.tP) d.isSimpleGroup_L hd.not_comm_L hd.even_card_L hd.L_le_centralizer
    (fun D hDC hD => hd.perfect_le_L (perfectLeInn h) hDC hD) h52.quasisimple h52.odd_center
    h52.commute h52.diag_mem h52.diag_surj hd.isSylowOf_tP hNR hperf hnorm

end CaseBParts

open CaseBParts in
theorem u5ProductCaseExclusion_of_parts_core
    (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement)
    (sp : SharedParts) (op : OwnParts) :
    CFSG.Yardstones.M41b0c98b3153.U5ProductCaseExclusion := by
  intro G _ _ f K _ h d hd hnl
  exact op.false_of_caseBHyp (sp.caseBHyp ⟨⟨hGMS, hL, hd⟩, hnl⟩)

open CaseBParts in
theorem u5ProductCaseExclusion_of_parts
    (sp : SharedParts) (op : OwnParts) :
    CFSG.Yardstones.M41b0c98b3153.U5ProductCaseExclusion :=
  u5ProductCaseExclusion_of_parts_core GMSK.gmsUnitarySharpKRankOne
    GMSK.gmsLinearStandardLayerListKRankOne sp op

end CFSG.LocalAnalysis.EvenBN.U5
