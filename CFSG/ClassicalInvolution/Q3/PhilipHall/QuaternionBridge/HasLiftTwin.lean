module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.QuotientFamily
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Q3.TL3GlueR
public import CFSG.ClassicalInvolution.Q3.TL3GoodLift
public import CFSG.ClassicalInvolution.Q3.TL3TopRestrict

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

theorem le_map_centralizer_of_isClassicalMember3 (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) {L : Subgroup (Y ⧸ N)}
    (hL : IsClassicalMember3 L (QuotientGroup.mk' N t)) :
    L ≤ (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) := by
  have hLC : L ≤ Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) :=
    isSubnormal_le hL.subnormal
  obtain ⟨e⟩ := hL.nonempty_equiv
  obtain ⟨ψ, hψs, hψk⟩ := Q3T7T2.exists_proj e
  have hcl := Q3T7T2.odd_closure_of_proj ψ hψs hψk
  rw [← hcl]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxL, hxo⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨g, hgC, -, hgx⟩ := exists_lift_centralizer (t := t) hNc hN2 hxo (hLC hxL)
    (pow_orderOf_eq_one _)
  exact ⟨g, hgC, hgx⟩

theorem Q8TwinDatum.restrict_tight {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hd : Q8TwinDatum R S t) {H : Subgroup Y} (hSH : (S : Subgroup R).map R.subtype ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (R : Set Y)) :
    ∃ S' : Sylow 2 (R.subgroupOf H),
      TightDatum (R.subgroupOf H) S' (⟨t, hSH hd.mem⟩ : H) ∧
        Nonempty ((S' : Subgroup (R.subgroupOf H)) ≃* (S : Subgroup R)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SY : Subgroup Y := (S : Subgroup R).map R.subtype with hSY
  have hSR : SY ≤ R := Subgroup.map_subtype_le _
  have hle : SY.subgroupOf H ≤ R.subgroupOf H := Subgroup.subgroupOf_mono H hSR
  set P0 : Subgroup ↥(R.subgroupOf H) := (SY.subgroupOf H).subgroupOf (R.subgroupOf H) with hP0
  let e1 : ↥P0 ≃* ↥(SY.subgroupOf H) := Subgroup.subgroupOfEquivOfLe hle
  let e2 : ↥(SY.subgroupOf H) ≃* ↥SY := Subgroup.subgroupOfEquivOfLe hSH
  let e3 : ↥SY ≃* ↥(S : Subgroup R) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm
  let e : ↥P0 ≃* ↥(S : Subgroup R) := e1.trans (e2.trans e3)
  have hb : 2 ^ (Nat.card ↥R).factorization 2 = Nat.card P0 := by
    rw [Nat.card_congr e.toEquiv, Sylow.card_eq_multiplicity S]
  have hdvdR : Nat.card ↥(R.subgroupOf H) ∣ Nat.card ↥R :=
    Subgroup.card_dvd_of_injective (subgroupOfToSub R H) (subgroupOfToSub_injective R H)
  have hP0dvd : Nat.card P0 ∣ Nat.card ↥(R.subgroupOf H) := Subgroup.card_subgroup_dvd_card P0
  have hle1 : (Nat.card ↥(R.subgroupOf H)).factorization 2 ≤ (Nat.card ↥R).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvdR 2
  have hle2 : (Nat.card ↥R).factorization 2 ≤ (Nat.card ↥(R.subgroupOf H)).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', hb]
    exact hP0dvd
  have hcard : Nat.card P0 = 2 ^ (Nat.card ↥(R.subgroupOf H)).factorization 2 := by
    rw [le_antisymm hle1 hle2, hb]
  have hS'coe : ((Sylow.ofCard P0 hcard : Sylow 2 ↥(R.subgroupOf H)) :
      Subgroup ↥(R.subgroupOf H)) = P0 := rfl
  have htR : (⟨t, hSH hd.mem⟩ : H) ∈ R.subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.map_subtype_le _ hd.mem)
  have hcent : R.subgroupOf H ≤ Subgroup.centralizer ({(⟨t, hSH hd.mem⟩ : H)} : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hx))
  refine ⟨Sylow.ofCard P0 hcard, ?_, ⟨e⟩⟩
  obtain ⟨r, hr, ⟨f⟩⟩ := hd.quat
  refine ⟨⟨r, hr, ⟨e.trans f⟩⟩, ?_, ?_, hcent, ?_, ?_⟩
  · rw [hS'coe]
    exact ⟨⟨⟨t, hSH hd.mem⟩, htR⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hd.mem), rfl⟩
  · rw [Subgroup.orderOf_mk]
    exact hd.order
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr ?_
    intro c _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := (Subgroup.mem_normalizer_iff.mp (hnorm c.2)) (x : Y)
    exact this
  · exact isPGroup_two_quotient_subgroupOf R H hd.twoGroup

theorem good_of_hasLift_twin (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    (hL : TightHasLift (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t)) :
    GoodThreeElement R t := by
  classical
  obtain ⟨L, hKL, hL⟩ := hL
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hdq := q8TwinDatum_map hd hN2 htN
  have hC1Cb : (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  have hLC₁ := le_map_centralizer_of_isClassicalMember3 (t := t) hNc hN2 hL
  have hRC : R ≤ Subgroup.centralizer ({t} : Set Y) := hd.cent
  have hRC₁ : R.map (QuotientGroup.mk' N) ≤
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) := Subgroup.map_mono hRC
  have htC₁ : QuotientGroup.mk' N t ∈
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hSC₁ : ((TwistQ.sylowMap N S : Sylow 2 ↥(R.map (QuotientGroup.mk' N))) :
      Subgroup ↥(R.map (QuotientGroup.mk' N))).map (R.map (QuotientGroup.mk' N)).subtype ≤
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) :=
    (Subgroup.map_subtype_le _).trans hRC₁
  have hnorm : (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) ≤
      Subgroup.normalizer ((R.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_normalizer_iff_conjSub_eq, ← TwistQ.conjSub_map (N := N)]
    have h1 : conjSub g R = R := mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer hg)
    rw [h1]
  obtain ⟨S', hd', -⟩ := hdq.restrict_tight hSC₁ hnorm
  have hKC₁ : tightCore (R.map (QuotientGroup.mk' N)) ≤
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) :=
    (tightCore_le _).trans hRC₁
  have hHL : TightHasLift ((R.map (QuotientGroup.mk' N)).subgroupOf
      ((Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N))) ⟨_, htC₁⟩ := by
    refine ⟨L.subgroupOf ((Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N)), ?_,
      hL.subgroupOf hLC₁⟩
    rw [tightCore_subgroupOf hKC₁]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hKL (Subgroup.mem_subgroupOf.mp hx))
  have hgood := hd'.good_of_hasLift hHL
  obtain ⟨x, k, hxC, hxH, hx3, hnt, hD⟩ := partial_good_of_restrict htC₁ hgood
  exact good_of_partial hd hNc hN2 htN ⟨x, k, hxC, hxH, hx3, hnt, hD⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
