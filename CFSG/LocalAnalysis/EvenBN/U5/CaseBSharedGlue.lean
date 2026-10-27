module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec38Outcome_of_input (hp : d.ProductCaseHyp) (hi : d.Sec38Input)
    (hnn : d.Sec38NotNormal) : d.Sec38Outcome :=
  ⟨hi.t_mem, GMSK.sharpOutcomeU3_oddCore_quotient_of_quasisimple hp.gms hi.kgroup hi.quasisimple
    hi.model hi.order_two hi.centralizes hi.normal hi.rank hi.centre_le hnn⟩

theorem sec39Outcome_of_input (hp : d.ProductCaseHyp) (hi : d.Sec39Input)
    (hnn : d.Sec39NotNormal) : d.Sec39Outcome := by
  obtain ⟨k, _, _, hk, ⟨φ⟩⟩ := hi.field
  have h2 := hp.hyp.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hi.t_mem, ?_⟩
  set tb := proj d.D ⟨d.t, hi.t_mem⟩ with htb
  have hAt : bar d.D d.N₁ ≤ centralizer ({tb} : Set (Bar d.D)) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hi.centralizes a ha)
  obtain ⟨hstd, hsyl⟩ := GMSK.stdLinearData_odd_quotient (n := 2 * f) (by omega) hk φ
    hi.order_two hAt hi.normal
    (GMSK.exists_sylow_inf_centralizer_eq_zpowers hi.order_two hi.centralizes hi.rank) (OD d)
    (GMSK.odd_card_standardComponentOddCore (Bar d.D)) hnn
  have hO : CFSG.Open.standardComponentOddCore (Bar d.D ⧸ OD d) = ⊥ :=
    GMSK.standardComponentOddCore_quotient_eq_bot (Bar d.D)
  refine ⟨hp.gmsL _ (hi.kgroup.quotient _) hO (2 * f) _ hstd hsyl, ?_⟩
  set θ := QuotientGroup.mk' (OD d) with hθ
  have htO : tb ∉ OD d := by
    intro hmem
    have hodd := GMSK.odd_card_standardComponentOddCore (Bar d.D)
    have hdvd : orderOf (⟨tb, hmem⟩ : OD d) ∣ Nat.card (OD d) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hi.order_two] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have ht'1 : θ tb ≠ 1 := fun h1 => htO ((QuotientGroup.eq_one_iff tb).1 h1)
  have htb2 : tb ^ 2 = 1 := by
    rw [← hi.order_two]
    exact pow_orderOf_eq_one tb
  have ht'2 : orderOf (θ tb) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, htb2, map_one]) ht'1
  have ht'A : θ tb ∈ centralizer ((AbarD d : Subgroup (Bar d.D ⧸ OD d)) : Set (Bar d.D ⧸ OD d)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hi.centralizes a ha]
  set C := centralizer ((AbarD d : Subgroup (Bar d.D ⧸ OD d)) : Set (Bar d.D ⧸ OD d)) with hC
  have hle : zpowers (θ tb) ≤ C := zpowers_le.2 ht'A
  have hcard : Nat.card ((zpowers (θ tb)).subgroupOf C) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, ht'2]
  have hP2 : IsPGroup 2 ((zpowers (θ tb)).subgroupOf C) :=
    IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  obtain ⟨S, hS⟩ := hP2.exists_le_sylow
  have hSc : Nat.card S = 2 := hsyl S
  have hPS : (zpowers (θ tb)).subgroupOf C = (S : Subgroup C) :=
    eq_of_le_of_card_ge hS (by rw [hcard, hSc])
  have hodd : ¬ 2 ∣ (zpowers (θ tb)).relIndex C := by
    rw [Subgroup.relIndex, hPS]
    exact Sylow.not_dvd_index S
  exact GMSK.oneOrTwoLayer_of_stdLinearData hO hstd ht'2 ht'A hodd

theorem exists_sylow_L₂_of_hyp (hp : d.ProductCaseHyp) :
    ∃ S : Subgroup G, IsSylowOf 2 S d.L₂ ∧ d.P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL := hp.hyp.P_le_L₂ hp.gms
  have hP2 : IsPGroup 2 (d.P.subgroupOf d.L₂) := d.isPGroup_P.comap_subtype
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  exact ⟨(Q : Subgroup d.L₂).map d.L₂.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩⟩

end Data

namespace CaseBParts

open Data

structure SharedParts : Prop where
  s8 : SU3SylowTIStatement
  s8l3 : L3AutOddStatement
  s8l3d : L3DihedralStatement
  s38a1 : Sec38a1Statement
  s38a2 : Sec38a2Statement
  s38b : Sec38InputStatement
  s38c : Sec38NotNormalStatement
  s38o : Sec38OddStatement
  s38d : Sec38LayerStatement
  s39a1 : Sec39a1Statement
  s39a : Sec39aStatement
  s39b : Sec39bStatement
  s39c : Sec39cStatement
  s39d : Sec39dStatement
  s39e : Sec39eStatement
  s39i : Sec39InputStatement
  s39n : Sec39NotNormalStatement
  s39r : Sec39ReducedStatement
  s39l : Sec39LayerStatement
  s39o : Sec39LOneStatement
  s39dd : Sec39OddStatement
  s310o : Sec3101OrdersStatement
  s310c : Sec3102Statement
  s310a1 : Sec3101A1Statement
  s310a2 : Sec3101A2Statement
  s310e : Sec3101EStatement
  s310b : Sec3101BStatement
  s310d : Sec310ThreeStatement
  s311a : Sec311TransStatement
  s311b : Sec311NotTransStatement
  s312a : Sec312AStatement
  s312b : Sec312BStatement
  s313a : Sec313TransStatement
  s313b : Sec313NotTransStatement

variable (sp : SharedParts) {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

include sp

theorem SharedParts.sec3_8 (hp : d.ProductCaseHyp) : d.Sec3_8 := by
  have a1 := sp.s38a1 G f K h d hp
  have a : d.Sec38a := ⟨a1, sp.s38a2 G f K h d hp a1⟩
  have hi := sp.s38b G f K h d hp a
  have hnn := sp.s38c G f K h d hp a hi
  have ho := Data.sec38Outcome_of_input hp hi hnn
  have hod := sp.s38o sp.s8l3 sp.s8l3d G f K h d hp a hi hnn ho
  have hl := sp.s38d G f K h d hp a hi hnn ho hod
  exact ⟨hl.L₂_eq, hl.V_le, hl.odd, a.secondCenter, a.maximal⟩

theorem SharedParts.know92 (hp : d.ProductCaseHyp) : d.Know92 := by
  have k8 : d.Know8 := ⟨sp.sec3_8 hp⟩
  have ha1 := fun S hS hP => sp.s39a1 sp.s8 G f K h d hp k8 S hS hP
  have ha := fun S hS hP => sp.s39a G f K h d hp k8 S hS hP (ha1 S hS hP)
  have hb := fun S hS hP => sp.s39b G f K h d hp k8 S hS hP (ha S hS hP)
  have hc := fun S hS hP => sp.s39c G f K h d hp k8 S hS hP (ha S hS hP) (hb S hS hP)
  have hd' := fun S hS hP => sp.s39d G f K h d hp k8 S hS hP (ha S hS hP) (hb S hS hP)
    (hc S hS hP)
  refine ⟨k8, fun S hS hP => ⟨(ha S hS hP).S_eq, (hd' S hS hP).1, (hd' S hS hP).2⟩,
    fun S hS hP => ⟨(hc S hS hP).1, (hc S hS hP).2.1, (hc S hS hP).2.2, (hb S hS hP).1,
      (hb S hS hP).2⟩, ha⟩

theorem SharedParts.know93 (hp : d.ProductCaseHyp) : d.Know93 := by
  have k92 := sp.know92 hp
  have he := sp.s39e G f K h d hp k92
  have hi := sp.s39i G f K h d hp k92 he
  have hnn := sp.s39n G f K h d hp k92 he hi
  have ho := Data.sec39Outcome_of_input hp hi hnn
  have hr := sp.s39r G f K h d hp k92 he hi hnn ho
  have hl := sp.s39l G f K h d hp k92 he hi hnn ho hr
  exact ⟨k92, ⟨sp.s39o G f K h d hp k92 he hr hl, sp.s39dd G f K h d hp k92 he hr hl⟩, he⟩

theorem SharedParts.know10 (hp : d.ProductCaseHyp) : d.Know10 := by
  have k93 := sp.know93 hp
  have hO : d.Sec3101OrdersAll := sp.s310o G f K h d hp k93
  have h2 := sp.s310c G f K h d hp k93 hO
  have ha1 := fun S hS hP => sp.s310a1 G f K h d hp k93 h2 S hS hP (hO S hS hP)
  have ha2 := fun S hS hP =>
    sp.s310a2 G f K h d hp k93 h2 S hS hP (hO S hS hP) (ha1 S hS hP)
  have ha : ∀ S, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec3101A S :=
    fun S hS hP => ⟨ha1 S hS hP, ha2 S hS hP⟩
  have he := fun S hS hP =>
    sp.s310e G f K h d hp k93 h2 S hS hP (hO S hS hP) (ha S hS hP)
  have hb := fun S hS hP =>
    sp.s310b G f K h d hp k93 h2 S hS hP (hO S hS hP) (ha S hS hP) (he S hS hP)
  have h1 : d.Sec3_10_one := fun S hS hP => by
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha S hS hP
    obtain ⟨e1, e2, e3⟩ := he S hS hP
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb S hS hP
    exact ⟨a1, a2, a3, a4, e1, e2, b1, b2, e3, b3, b4, b5⟩
  exact ⟨k93, h1, h2, sp.s310d G f K h d hp k93 h1 h2, hO⟩

theorem SharedParts.sec3_11 (hp : d.ProductCaseHyp) : d.Sec3_11 := by
  have k10 := sp.know10 hp
  by_contra hnot
  obtain ⟨S, hS, hP⟩ := Data.exists_sylow_L₂_of_hyp hp
  obtain ⟨J, hJo, hJn, hJt⟩ := sp.s311a G f K h d hp k10 S hS hP hnot
  exact sp.s311b G f K h d hp k10 S hS hP J hJo hJn hJt

theorem SharedParts.know11 (hp : d.ProductCaseHyp) : d.Know11 :=
  ⟨sp.know10 hp, sp.sec3_11 hp⟩

theorem SharedParts.know12 (hp : d.ProductCaseHyp) : d.Know12 := by
  have k11 := sp.know11 hp
  have ha := sp.s312a G f K h d hp k11
  have hb := sp.s312b G f K h d hp k11 ha
  refine ⟨k11, fun k _ _ hk ψ => ⟨(ha k _ _ hk ψ).1, (ha k _ _ hk ψ).2, hb k _ _ hk ψ⟩⟩

theorem SharedParts.sec3_13_one (hp : d.ProductCaseHyp) : d.Sec3_13_one := by
  have k12 := sp.know12 hp
  have ha := sp.s313a G f K h d hp k12
  have hb := sp.s313b G f K h d hp k12
  intro S hS hP k _ _ hk ψ hle
  obtain ⟨J, hJo, hJn, hJt⟩ := ha S hS hP k _ _ hk ψ hle
  exact absurd hJt (hb S hS hP J hJo hJn)

theorem SharedParts.caseBHyp (hp : d.ProductCaseHyp) : d.CaseBHyp := by
  have k12 := sp.know12 hp
  exact ⟨hp.hyp, hp.gms, k12.s8, k12.s9_1, k12.s9_2, k12.s9_3, k12.s10_1, k12.s10_2, k12.s11,
    k12.s12, sp.sec3_13_one hp, hp.caseB⟩

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
