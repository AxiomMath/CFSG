module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IsPerfect
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

variable {Y : Type*} [Group Y] [Finite Y]

private theorem eq_of_orderOf_eq_two_of_isCyclic' {P : Type*} [Group P] [Finite P] [IsCyclic P]
    {a b : P} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  haveI : Fintype P := Fintype.ofFinite P
  have hdvd : 2 ∣ Fintype.card P := by
    rw [← ha]
    exact orderOf_dvd_card
  have hcard := IsCyclic.card_orderOf_eq_totient hdvd
  rw [Nat.totient_two] at hcard
  exact Finset.card_le_one.1 hcard.le a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩) b
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)

private theorem perfect_eq_bot_of_solvable {G : Type*} [Group G] {A P : Subgroup G}
    (hA : Group.IsSolvable A) (hP : ⁅P, P⁆ = P) (hPA : P ≤ A) : P = ⊥ := by
  haveI : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  haveI : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPA)
  rcases subsingleton_or_nontrivial P with h | h
  · exact Subgroup.eq_bot_of_subsingleton P
  · exact absurd ‹Group.IsSolvable P› (Group.IsPerfect.not_isSolvable P)

private theorem perfect_le_ker_of_solvable {G Q : Type*} [Group G] [Group Q]
    [Group.IsSolvable Q] (f : G →* Q) {P : Subgroup G} (hP : ⁅P, P⁆ = P) : P ≤ f.ker := by
  rw [← Subgroup.map_eq_bot_iff]
  exact perfect_eq_bot_of_solvable (A := ⊤) inferInstance (by rw [← map_commutator, hP]) le_top

theorem isCyclic_of_isPGroup_of_isCyclic_sylow {K : Subgroup Y}
    (hK : ∃ S : Sylow 2 K, IsCyclic (S : Subgroup K)) {U : Subgroup Y} (hU : IsPGroup 2 U)
    (hUK : U ≤ K) : IsCyclic U := by
  obtain ⟨S, hS⟩ := hK
  have hU' : IsPGroup 2 (U.subgroupOf K) := hU.comap_subtype (K := K)
  obtain ⟨T, hT⟩ := hU'.exists_le_sylow
  have hTcyc : IsCyclic (T : Subgroup K) := (Sylow.equiv T S).isCyclic.mpr hS
  have hU'cyc : IsCyclic (U.subgroupOf K) := Subgroup.isCyclic_of_le hT
  exact (subgroupOfEquivOfLe hUK).isCyclic.mp hU'cyc

theorem isCyclic_sylow_of_forall_le_inf_centralizer {K : Subgroup Y} {t : Y} (htK : t ∈ K)
    (ht : orderOf t = 2)
    (h : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ K ⊓ centralizer ({t} : Set Y) → IsCyclic U)
    (S : Sylow 2 K) : IsCyclic (S : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tK : K := ⟨t, htK⟩ with htKdef
  have htK2 : orderOf tK = 2 := by rw [htKdef, Subgroup.orderOf_mk, ht]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  have hp : IsPGroup 2 (zpowers tK) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htK2, pow_one])
  obtain ⟨S1, hS1⟩ := hp.exists_le_sylow
  let R : Subgroup Y := (S1 : Subgroup K).map K.subtype
  let C : Subgroup Y := centralizer ({t} : Set Y)
  have hRpg : IsPGroup 2 R := S1.isPGroup'.map K.subtype
  have hRK : R ≤ K := map_subtype_le (S1 : Subgroup K)
  have htR : t ∈ R := ⟨tK, hS1 (mem_zpowers tK), rfl⟩
  have hRntriv : Nontrivial R := ⟨⟨⟨t, htR⟩, 1, fun h1 => ht1 (congrArg Subtype.val h1)⟩⟩
  have hCircC : IsCyclic (R ⊓ C : Subgroup Y) :=
    h _ (hRpg.to_le inf_le_left) (inf_le_inf_right C hRK)
  have h2dvd : 2 ∣ Nat.card (Subgroup.center R) := by
    haveI : Nontrivial R := hRntriv
    haveI : Nontrivial (Subgroup.center R) := hRpg.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center R)
    have hzR1 : (z : R) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
    have h1 : 2 ∣ orderOf (z : R) := hRpg.dvd_orderOf hzR1
    rw [Subgroup.orderOf_coe z] at h1
    exact h1.trans (orderOf_dvd_natCard z)
  obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card' 2 (G := Subgroup.center R) h2dvd
  have hvYord : orderOf ((v : R) : Y) = 2 := by
    rw [Subgroup.orderOf_coe (H := R) (v : R),
      Subgroup.orderOf_coe (H := Subgroup.center R) v, hvord]
  have hvcent : ((v : R) : Y) ∈ C := by
    rw [mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_center_iff.mp v.2 (⟨t, htR⟩ : R)
    exact (congrArg Subtype.val hcomm).symm
  have hvR : ((v : R) : Y) ∈ R := (v : R).2
  have hvC : ((v : R) : Y) ∈ R ⊓ C := ⟨hvR, hvcent⟩
  have htC : t ∈ R ⊓ C :=
    ⟨htR, mem_centralizer_singleton_iff.2 rfl⟩
  have hvtY : ((v : R) : Y) = t := by
    have ha : orderOf (⟨((v : R) : Y), hvC⟩ : (R ⊓ C : Subgroup Y)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hvYord
    have hb : orderOf (⟨t, htC⟩ : (R ⊓ C : Subgroup Y)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact ht
    exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic' ha hb)
  have htCent : (⟨t, htR⟩ : R) ∈ Subgroup.center R :=
    (Subtype.ext hvtY : (v : R) = ⟨t, htR⟩) ▸ v.2
  have hRC : R ≤ C := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_center_iff.mp htCent (⟨r, hr⟩ : R)
    exact congrArg Subtype.val hcomm
  have hRcyc : IsCyclic R := by
    haveI : IsCyclic (R ⊓ C : Subgroup Y) := hCircC
    exact Subgroup.isCyclic_of_le (le_inf le_rfl hRC)
  have hS1cyc : IsCyclic (S1 : Subgroup K) :=
    (Subgroup.equivMapOfInjective (S1 : Subgroup K) K.subtype K.subtype_injective).isCyclic.mpr
      hRcyc
  exact (Sylow.equiv S1 S).isCyclic.mp hS1cyc

theorem exists_conj_eq_of_isCyclic_sylow {K : Subgroup Y}
    (hK : ∃ S : Sylow 2 K, IsCyclic (S : Subgroup K)) {t u : Y} (htK : t ∈ K)
    (ht : orderOf t = 2) (huK : u ∈ K) (hu : orderOf u = 2) : ∃ k ∈ K, k * t * k⁻¹ = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : ∀ S : Sylow 2 K, IsCyclic (S : Subgroup K) := by
    intro S
    obtain ⟨S0, hS0⟩ := hK
    exact (Sylow.equiv S S0).isCyclic.mpr hS0
  set tK : K := ⟨t, htK⟩ with htKdef
  set uK : K := ⟨u, huK⟩ with huKdef
  have htK2 : orderOf tK = 2 := by rw [htKdef, Subgroup.orderOf_mk, ht]
  have huK2 : orderOf uK = 2 := by rw [huKdef, Subgroup.orderOf_mk, hu]
  have hpt : IsPGroup 2 (zpowers tK) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htK2, pow_one])
  have hpu : IsPGroup 2 (zpowers uK) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huK2, pow_one])
  obtain ⟨St, hSt⟩ := hpt.exists_le_sylow
  obtain ⟨Su, hSu⟩ := hpu.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K St Su
  have hmem : k * tK * k⁻¹ ∈ (Su : Subgroup K) := by
    rw [← hk, Sylow.coe_subgroup_smul]
    have h2 := smul_mem_pointwise_smul tK (MulAut.conj k) (St : Subgroup K)
      (hSt (mem_zpowers tK))
    simpa [MulAut.smul_def, MulAut.conj_apply] using h2
  have hwK : orderOf (k * tK * k⁻¹) = 2 := by
    rw [← MulAut.conj_apply k tK, MulEquiv.orderOf_eq]
    exact htK2
  haveI : IsCyclic (Su : Subgroup K) := hcyc Su
  have hword : orderOf (⟨k * tK * k⁻¹, hmem⟩ : (Su : Subgroup K)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hwK
  have huord : orderOf (⟨uK, hSu (mem_zpowers uK)⟩ : (Su : Subgroup K)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact huK2
  have hwu : (⟨k * tK * k⁻¹, hmem⟩ : (Su : Subgroup K)) = ⟨uK, hSu (mem_zpowers uK)⟩ :=
    eq_of_orderOf_eq_two_of_isCyclic' hword huord
  have hkeq : k * tK * k⁻¹ = uK := congrArg Subtype.val hwu
  exact ⟨(k : Y), k.2, by simpa using congrArg Subtype.val hkeq⟩

theorem perfect_eq_bot_of_isCyclic_sylow {K P : Subgroup Y}
    (hK : ∃ S : Sylow 2 K, IsCyclic (S : Subgroup K)) (hPK : P ≤ K) (hP : ⁅P, P⁆ = P) :
    P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 P) := inferInstance
  have hScyc : IsCyclic (S : Subgroup P) := by
    have hmapcyc : IsCyclic ((S : Subgroup P).map P.subtype) :=
      isCyclic_of_isPGroup_of_isCyclic_sylow hK (S.isPGroup'.map P.subtype)
        ((map_subtype_le (S : Subgroup P)).trans hPK)
    exact (Subgroup.equivMapOfInjective (S : Subgroup P) P.subtype
      P.subtype_injective).isCyclic.mpr hmapcyc
  obtain ⟨-, -, -, ⟨hn, hodd, hidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  have hq : IsPGroup 2 (P ⧸ pPrimeCore 2 P) := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [← index_eq_card, hidx, hk])
  have := hq.isNilpotent
  have hPtop : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    have := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hP)
    rwa [_root_.commutator_def] at this
  have htop : pPrimeCore 2 P = ⊤ := by
    have := perfect_le_ker_of_solvable (QuotientGroup.mk' (pPrimeCore 2 P)) hPtop
    rw [QuotientGroup.ker_mk'] at this
    exact top_le_iff.mp this
  have hPodd : Odd (Nat.card P) := by
    rw [htop, card_top] at hodd
    exact hodd
  exact perfect_eq_bot_of_solvable (A := P) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hPodd) hP le_rfl

end CFSG.OddStandard.AltStdSec.SwapPartner
