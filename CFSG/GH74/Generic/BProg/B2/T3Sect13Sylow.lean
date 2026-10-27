module

public import CFSG.GH74.Generic.BProg.B2.T3Rank
import CFSG.GH74.Generic.BProg.B1.PilotS1
import CFSG.GH74.Generic.BProg.B2.T1Basic
import CFSG.GH74.Generic.BProg.Cor2Easy
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankNS
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.GH74.Generic.BProg.B1.PilotS4
import CFSG.GH74.Generic.S3.LeavesFine
import CFSG.GH74.Generic.S3.Lem37

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

namespace T3Sect13Sylow

open CFSG.GH74.GLS.C3.Layer1

theorem pRank_le_pRank_barIn {E K M : Subgroup G} (hEK : E ≤ K) (hKM : K ≤ M)
    (hE : IsElementaryAbelian 2 ↥E) : pRank 2 ↥E ≤ pRank 2 ↥(barIn M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcard : Nat.card ↥E = 2 ^ pRank 2 ↥E := Back.card_eq_two_pow_pRank hE
  have hEM : E ≤ M := hEK.trans hKM
  set E₀ : Subgroup ↥M := E.subgroupOf M with hE₀
  have hE₀el : IsElementaryAbelian 2 ↥E₀ := IsElementaryAbelian.subgroupOf hEM
  have hE₀2 : IsPGroup 2 ↥E₀ := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hE₀card : Nat.card ↥E₀ = 2 ^ pRank 2 ↥E := by
    rw [hE₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEcard]
  set ρ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  set Ē : Subgroup (Mbar M) := E₀.map ρ with hĒ
  have hĒel : IsElementaryAbelian 2 ↥Ē := IsElementaryAbelian.map ρ
  have hĒcard : Nat.card ↥Ē = 2 ^ pRank 2 ↥E := by
    rw [hĒ, B1.PilotS1.card_map_eq_of_inj ρ E₀ (Thm2Comp.eq_one_of_isPGroup hE₀2), hE₀card]
  have hĒle : Ē ≤ barIn M K := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Subgroup.mem_subgroupOf.2 (hEK (Subgroup.mem_subgroupOf.1 he)), rfl⟩
  calc pRank 2 ↥E = pRank 2 ↥Ē := (CFSG.pRank_eq_of_card_eq_pow one_lt_two hĒcard).symm
    _ ≤ pRank 2 ↥(barIn M K) := Back.pRank_mono' hĒle

theorem barIn_normal_of_c1 (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) {H : Subgroup G}
    (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K)
    (hr : pRank 2 (CMbar M K) ≤ 1) : (barIn M K).Normal := by
  have hHsub : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hH.2.1.2
  have hKc : IsComponent (barIn M K) := isComponent_barIn_of_isSubnormal hs hKM (hc1 ▸ hHsub)
  have hE := isE_inf_K hs
  have h2le : 2 ≤ pRank 2 ↥(barIn M K) :=
    hE.2.2.trans (pRank_le_pRank_barIn inf_le_right hKM hE.2.1)
  refine ⟨fun n hn g => ?_⟩
  have hJ : IsComponent (conjugate (barIn M K) g⁻¹) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹⁻¹) hKc
  have hcent : conjugate (barIn M K) g⁻¹ = barIn M K := by
    by_contra hne
    have hJc : conjugate (barIn M K) g⁻¹ ≤ SD.centBarK M K :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((CFSG.LocalCores.distinct_components_commute hJ hKc).resolve_left hne)
    have h1 : pRank 2 ↥(conjugate (barIn M K) g⁻¹) ≤ 1 :=
      (Back.pRank_mono' hJc).trans ((Thm2Comp.pRank_centBarK_le_pRank_CMbar hKM).trans hr)
    rw [Back.pRank_conjugate'] at h1
    omega
  have : g * n * g⁻¹ ∈ conjugate (barIn M K) g⁻¹ := by
    rw [Back.mem_conjugate_iff', show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group]
    exact hn
  rwa [hcent] at this

omit [Finite G] in
theorem mem_CMbar_conj {K M : Subgroup G} (hKM : K ≤ M) (hN : (barIn M K).Normal) {m c : G}
    (hm : m ∈ M) (hc : c ∈ CMbar M K) : m * c * m⁻¹ ∈ CMbar M K := by
  have hcM : c ∈ M := hc.1
  have hcc : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨c, hcM⟩ ∈ SD.centBarK M K :=
    (Thm2Comp.mem_CMbar_iff hKM ⟨c, hcM⟩).1 hc
  have := hN
  have hnc : (SD.centBarK M K).Normal := inferInstance
  have h1 := hnc.conj_mem _ hcc (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨m, hm⟩)
  have e : QuotientGroup.mk' (pPrimeCore 2 ↥M)
      (⟨m * c * m⁻¹, M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm)⟩ : ↥M) =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨m, hm⟩ * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨c, hcM⟩ *
        (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨m, hm⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine (Thm2Comp.mem_CMbar_iff hKM ⟨m * c * m⁻¹, M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm)⟩).2 ?_
  rw [e]
  exact h1

theorem two_le_pRank_of_commuting_involutions {X : Subgroup G} {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) :
    2 ≤ pRank 2 ↥X := by
  obtain ⟨-, hel, hcard⟩ := B1.PilotS5.closure_pair_facts ha2 hb2 hab hne
  have hle : closure ({a, b} : Set G) ≤ X := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.1 hy]; exact hb
  have := hel
  have h1 : pRank 2 ↥(closure ({a, b} : Set G)) = 2 :=
    CFSG.pRank_eq_of_card_eq_pow one_lt_two (by rw [hcard]; norm_num)
  have := Back.pRank_mono' hle
  omega

theorem eq_of_orderOf_two_of_pRank_le_one {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) (hr : pRank 2 ↥Q ≤ 1)
    {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    omega
  obtain ⟨z, hzQ, hz2, hzc⟩ := Thm2Comp.exists_involution_mem_center hQ ha ha1
  have key : ∀ c ∈ Q, orderOf c = 2 → c = z := by
    intro c hc hc2
    by_contra hne
    have := two_le_pRank_of_commuting_involutions hc hzQ hc2 hz2 (hzc c hc).symm hne
    omega
  exact (key a ha ha2).trans (key b hb hb2).symm

theorem exists_sylow_between (hs : Stage2Setup G x K A M P Q) (h2 : Stage2Concl2 M) (hQM : Q ≤ M) :
    ∃ T : Sylow 2 G, Q ≤ (T : Subgroup G) ∧ (T : Subgroup G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := inU0_A hs
  have hAel : IsElementaryAbelian 2 ↥A := hA.1.2.1
  have hA2 : IsPGroup 2 ↥A := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨T₀, hAT₀⟩ := hA2.exists_le_sylow
  have hT₀M : (T₀ : Subgroup G) ≤ M := cor2_c h2 _ A T₀.isPGroup' hA hAT₀
  have hQp : IsPGroup 2 ↥(Q.subgroupOf M) := hs.sylowQ.isPGroup.comap_subtype
  obtain ⟨P', hP'⟩ := hQp.exists_le_sylow
  have hP₀ : IsSylowOf 2 ((P' : Subgroup ↥M).map M.subtype) M := ⟨P', rfl⟩
  have hQP : Q ≤ (P' : Subgroup ↥M).map M.subtype := fun q hq =>
    ⟨⟨q, hQM hq⟩, hP' (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  obtain ⟨-, hp2, hdvd⟩ := isSylowOf_iff.1 hP₀
  have hMdvd : ¬ 2 ∣ M.index := fun h =>
    T₀.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hT₀M))
  have hidx : ¬ 2 ∣ ((P' : Subgroup ↥M).map M.subtype).index := by
    rw [← Subgroup.relIndex_mul_index (hP₀.le)]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact hdvd h
    · exact hMdvd h
  refine ⟨hp2.toSylow hidx, ?_, ?_⟩
  · rw [IsPGroup.toSylow_coe]; exact hQP
  · rw [IsPGroup.toSylow_coe]; exact hP₀.le

end T3Sect13Sylow

theorem sylow_center_of_c1 (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) (hQM : Q ≤ M)
    (h2 : Stage2Concl2 M) {H : Subgroup G} (hH : IsMinSubnormalIn K M H)
    (hc1 : barIn M H = barIn M K) (hr : pRank 2 (CMbar M K) ≤ 1) :
    (barIn M K).Normal ∧ ∃ T : Sylow 2 G, Q ≤ (T : Subgroup G) ∧ (T : Subgroup G) ≤ M ∧
      ∀ t ∈ (T : Subgroup G), t * x = x * t := by
  have hN := T3Sect13Sylow.barIn_normal_of_c1 hs hKM hH hc1 hr
  refine ⟨hN, ?_⟩
  obtain ⟨T, hQT, hTM⟩ := T3Sect13Sylow.exists_sylow_between hs h2 hQM
  refine ⟨T, hQT, hTM, ?_⟩
  have hQsyl : IsSylowOf 2 Q (CMbar M K) := T3Rank.isSylowOf_CMbar hs hKM hH hc1
  have hTX : (T : Subgroup G) ⊓ CMbar M K = Q :=
    hQsyl.eq_of_le (le_inf hQT hQsyl.le) inf_le_right T.isPGroup'.to_inf_left
  have hrQ : pRank 2 ↥Q ≤ 1 := by
    rw [← Thm2Comp.pRank_eq_pRank_sylow hQsyl]; exact hr
  intro t ht
  have hxQ : x ∈ Q := x_mem_Q hs
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hconjQ : t * x * t⁻¹ ∈ Q := by
    rw [← hTX]
    refine ⟨T.mul_mem (T.mul_mem ht (hQT hxQ)) (T.inv_mem ht), ?_⟩
    exact T3Sect13Sylow.mem_CMbar_conj hKM hN (hTM ht) (hQsyl.le hxQ)
  have hconj2 : orderOf (t * x * t⁻¹) = 2 := by
    rw [← hx2]
    exact (isConj_iff.2 ⟨t, rfl⟩ : IsConj x (t * x * t⁻¹)).orderOf_eq.symm
  have := T3Sect13Sylow.eq_of_orderOf_two_of_pRank_le_one hs.sylowQ.isPGroup hrQ hconjQ hxQ hconj2 hx2
  calc t * x = (t * x * t⁻¹) * t := by group
    _ = x * t := by rw [this]

end CFSG.GH74.Generic.BProg.B2
