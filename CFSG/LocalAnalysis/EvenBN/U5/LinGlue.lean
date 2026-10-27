module

public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin38
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39Sylow
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39c
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39NotNormal
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin311
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec313Two
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec41
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43One
public import CFSG.LocalAnalysis.EvenBN.U5.LinSylowR
public import CFSG.LocalAnalysis.EvenBN.U5.LinJr
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightJr
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightC
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightOdd
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofModelL3
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofModelL3D
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineB
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineInput
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineThree
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineLOne
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineOdd
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenA
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenA2
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenE
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenB
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenThree
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTwelveA
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTwelveB
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.LocalAnalysis.EvenBN
open scoped MatrixGroups commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_sec38Outcome_of_input (hp : d.CaseHyp) (hi : d.Sec38Input)
    (hnn : d.Sec38NotNormal) : d.Sec38Outcome :=
  ⟨hi.t_mem, GMSK.sharpOutcomeU3_oddCore_quotient_of_quasisimple hp.gms hi.kgroup hi.quasisimple
    hi.model hi.order_two hi.centralizes hi.normal hi.rank hi.centre_le hnn⟩

theorem lin_sec39Outcome_of_input (hp : d.CaseHyp) (hi : d.Sec39Input)
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
  have ht'A : θ tb ∈
      centralizer ((AbarD d : Subgroup (Bar d.D ⧸ OD d)) : Set (Bar d.D ⧸ OD d)) := by
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

theorem lin_nonempty_caseData (hl : d.LinCtx) (hs : d.Sec3_11) : Nonempty d.CaseBData := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ψ, α, hdiag, hswap⟩ := hs
  have hPL := hl.hyp.P_le_L₂ hl.gms
  have hP2 : IsPGroup 2 (d.P.subgroupOf d.L₂) := d.isPGroup_P.comap_subtype
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  exact ⟨⟨(Q : Subgroup d.L₂).map d.L₂.subtype, ⟨Q, rfl⟩,
    fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩, k, hk, ψ, α, hdiag, hswap⟩⟩

end Data

theorem lin_isPerfect_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : Group.IsPerfect X :=
  ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X)).resolve_left fun hb => by
    obtain ⟨a, b, hab⟩ := hna
    have hmem : ⁅a, b⁆ ∈ commutator X :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hb, Subgroup.mem_bot] at hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hmem)⟩

namespace LinCase

structure LinSteps : Prop where
  s38b : ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.CaseHyp → d.Sec38a → d.Sec38Input
  s39d : ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.LinCtx → d.Know8 →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec39a S → d.Sec39b → d.Sec39c S →
        d.Sec39d S
  s39r : ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.CaseHyp → d.Know92 → d.Sec39e →
      d.Sec39Input → d.Sec39NotNormal → d.Sec39Outcome → d.Sec39Reduced
  s310c : ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.LinCtx → d.Know93 → d.Sec3101OrdersAll →
      d.Sec3_10_two
  s311a : ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.CaseHyp → d.Know10 → d.Sec311Trans
  a4 : ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.LinCtx → d.Know12 →
      ∀ c : d.CaseBData, c.Sec41 → c.Sec42 →
        (∀ Y : Subgroup G, Y ≤ d.D → CFSG.IsElementaryAbelian 2 Y → Y ≤ c.Bc ∨ Y ≤ c.Bt) →
        ∀ X : Subgroup G, X ≤ c.S → CFSG.IsElementaryAbelian 2 X → (2 ^ f) ^ 10 < Nat.card X →
          X ≤ c.Bc ∨ X ≤ c.Bt
  a6 : ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.LinCtx → d.Know12 →
      ∀ c : d.CaseBData, ∀ R : Subgroup G, IsSylowOf 2 R (normalizer (d.D : Set G)) → c.S ≤ R →
        c.Sec43Out R

variable (st : LinSteps) {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

include st

theorem LinSteps.sec3_8 (hl : d.LinCtx) : d.Sec3_8 := by
  have hc := hl.toCaseHyp
  have a1 := Data.sec38a1_of_hyp hc
  have a : d.Sec38a := ⟨a1, Data.sec38a2_of_hyp hc a1⟩
  have hi := st.s38b G f K h d hc a
  have hnn := Data.sec38_notNormal hc a hi
  have ho := Data.lin_sec38Outcome_of_input hc hi hnn
  have hod := Data.sec38_odd CaseBParts.l3AutOdd CaseBParts.l3Dihedral hc a hi hnn ho
  have hly := Data.lin_sec38_layer hl hi ho hod
  exact ⟨hly.L₂_eq, hly.V_le, hly.odd, a.secondCenter, a.maximal⟩

theorem LinSteps.know92 (hl : d.LinCtx) : d.Know92 := by
  have hc := hl.toCaseHyp
  have k8 : d.Know8 := ⟨st.sec3_8 hl⟩
  have ha1 := fun S hS hP => Data.lin_sec39a1 hl k8 S hS hP
  have ha := fun S hS hP => Data.sec39a_of_hyp hc k8 S hS hP (ha1 S hS hP)
  have hb := fun S hS hP => Data.sec39b_of_hyp hc k8 S hS hP (ha S hS hP)
  have hcc := fun S hS hP => Data.lin_sec39c hl k8 S hS hP (ha S hS hP) (hb S hS hP)
  have hd' := fun S hS hP => st.s39d G f K h d hl k8 S hS hP (ha S hS hP) (hb S hS hP)
    (hcc S hS hP)
  refine ⟨k8, fun S hS hP => ⟨(ha S hS hP).S_eq, (hd' S hS hP).1, (hd' S hS hP).2⟩,
    fun S hS hP => ⟨(hcc S hS hP).1, (hcc S hS hP).2.1, (hcc S hS hP).2.2, (hb S hS hP).1,
      (hb S hS hP).2⟩, ha⟩

theorem LinSteps.know93 (hl : d.LinCtx) : d.Know93 := by
  have hc := hl.toCaseHyp
  have k92 := st.know92 hl
  have he := Data.sec39e_of_hyp hc k92
  have hi := Data.sec39_input hc k92 he
  have hnn := Data.lin_sec39_notNormal hl k92 he hi
  have ho := Data.lin_sec39Outcome_of_input hc hi hnn
  have hr := st.s39r G f K h d hc k92 he hi hnn ho
  have hly := Data.sec39_layer hc k92 he hi hnn ho hr
  exact ⟨k92, ⟨Data.sec39_lOne hc k92 he hr hly, Data.sec39_odd hc k92 he hr hly⟩, he⟩

theorem LinSteps.know10 (hl : d.LinCtx) : d.Know10 := by
  have hc := hl.toCaseHyp
  have k93 := st.know93 hl
  have hO : d.Sec3101OrdersAll := Data.sec3101Orders_of_hyp hc k93
  have h2 := st.s310c G f K h d hl k93 hO
  have ha1 := fun S hS hP => Data.sec3101A1_of_hyp hc k93 h2 S hS hP (hO S hS hP)
  have ha2 := fun S hS hP =>
    Data.sec3101A2_of_hyp hc k93 h2 S hS hP (hO S hS hP) (ha1 S hS hP)
  have ha : ∀ S, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec3101A S :=
    fun S hS hP => ⟨ha1 S hS hP, ha2 S hS hP⟩
  have he := fun S hS hP =>
    Data.sec3101E_of_hyp hc k93 h2 S hS hP (hO S hS hP) (ha S hS hP)
  have hb := fun S hS hP =>
    Data.sec3101B_of_hyp hc k93 h2 S hS hP (hO S hS hP) (ha S hS hP) (he S hS hP)
  have h1 : d.Sec3_10_one := fun S hS hP => by
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha S hS hP
    obtain ⟨e1, e2, e3⟩ := he S hS hP
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb S hS hP
    exact ⟨a1, a2, a3, a4, e1, e2, b1, b2, e3, b3, b4, b5⟩
  exact ⟨k93, h1, h2, Data.sec310Three_of_hyp hc k93 h1 h2, hO⟩

theorem LinSteps.sec3_11 (hl : d.LinCtx) : d.Sec3_11 := by
  have hc := hl.toCaseHyp
  have k10 := st.know10 hl
  by_contra hnot
  obtain ⟨S, hS, hP⟩ := Data.sec312_exists_S hc
  obtain ⟨J, hJo, hJn, hJt⟩ := st.s311a G f K h d hc k10 S hS hP hnot
  exact Data.lin_sec311NotTrans hl k10 S hS hP J hJo hJn hJt

theorem LinSteps.know11 (hl : d.LinCtx) : d.Know11 :=
  ⟨st.know10 hl, st.sec3_11 hl⟩

theorem LinSteps.know12 (hl : d.LinCtx) : d.Know12 := by
  have hc := hl.toCaseHyp
  have k11 := st.know11 hl
  have ha := Data.sec312A_of_hyp hc k11
  have hb := Data.sec312B_of_hyp hc k11 ha
  exact ⟨k11, fun k _ _ hk ψ => ⟨(ha k _ _ hk ψ).1, (ha k _ _ hk ψ).2, hb k _ _ hk ψ⟩⟩

theorem LinSteps.false_of_linCtx (hl : d.LinCtx) : False := by
  have hd := hl.hyp
  have k12 := st.know12 hl
  obtain ⟨c⟩ := Data.lin_nonempty_caseData hl k12.s11
  have hz := Data.CaseBData.lin_card_centerIn_Uc_le hl k12 c
  have h41 := Data.sec41_of_hyp hl k12 c hz
  have h42 := Data.CaseBData.lin_sec42_of_hyp hl k12 c h41
  have h43 := Data.CaseBData.lin_sec43_one hl k12 c h42
  have h44 := st.a4 G f K h d hl k12 c h41 h42 h43
  obtain ⟨R, hR, hSR, htR⟩ := Data.sylow_R hl k12 c
  have hout := st.a6 G f K h d hl k12 c R hR hSR
  have hkc := Data.sec43_three hl k12 c h42 h44 R hout
  haveI : IsSimpleGroup G := hd.setting.std.simple
  haveI : Group.IsPerfect G := lin_isPerfect_of_simple hd.setting.std.nonab
  have hDS : d.D ≤ c.S := (k12.s9_1 c.S c.S_syl c.P_le_S).1 ▸ le_sup_right
  have hne : c.Bc ≠ c.Bt := by
    intro heq
    have h1 : c.Bc = d.F := by
      have := h42.inf
      rwa [← heq, inf_idem] at this
    have h2 := h42.card
    rw [h1, hd.card_F hl.gms] at h2
    have hf := hd.two_le
    have h3 : (2 ^ f) ^ 8 < (2 ^ f) ^ 12 :=
      Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by norm_num)) (by norm_num)
    exact absurd h2 h3.ne
  exact swap_endgame G f hd.two_le d.t c.Bc d.D R hd.t_two h42.elem h42.card hne h42.sup.symm h43
    (fun X hXC hX => hd.card_le_of_le_centralizer hXC hX) hR (hDS.trans hSR) htR hkc

omit st

end LinCase

open LinCase in
theorem u5LinearCaseExclusion_of_steps
    (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement) (st : LinSteps) :
    CFSG.Yardstones.M41b0c98b3153.U5LinearCaseExclusion := by
  intro G _ _ f K _ h d hd hA
  exact st.false_of_linCtx ⟨hGMS, hL, hd, hA⟩

end CFSG.LocalAnalysis.EvenBN.U5
