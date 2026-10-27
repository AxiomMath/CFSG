module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.AltDown
open Equiv Equiv.Perm
open scoped commutatorElement

theorem up7a8_kdAltExact {n p : ℕ} (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (alternatingGroup (Fin n))} (hα : α ^ p = 1) (hα1 : α ≠ 1)
    {I : Subgroup (alternatingGroup (Fin n))} (hI : GLAPComponent p (fixSubgroup α) I) :
    ∃ m k : ℕ, 5 ≤ m ∧ 0 < k ∧ n = m + p * k ∧ Nonempty (↥I ≃* alternatingGroup (Fin m)) := by
  obtain ⟨x, hx1, hxp, rfl⟩ := exists_conj_of_alt hn hp hp2 hα hα1
  have hσp : (x : Perm (Fin n)) ^ p = 1 := by simpa using congrArg Subtype.val hxp
  have hσ1 : (x : Perm (Fin n)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hIF := le_range_ofSubtype_of_glaPComponent hp hp2 hxp hI
  obtain ⟨m, hm⟩ : ∃ m, ((x : Perm (Fin n)).support)ᶜ.card = m := ⟨_, rfl⟩
  have hsupp : ((x : Perm (Fin n)).support).card + m = n := by
    have h := Finset.card_compl ((x : Perm (Fin n)).support)
    have h2 : ((x : Perm (Fin n)).support).card ≤ n := by
      simpa using Finset.card_le_univ ((x : Perm (Fin n)).support)
    rw [Fintype.card_fin, hm] at h
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := (x : Perm (Fin n)))
    (by rw [pow_one]; exact hσp)
  rw [hm, Fintype.card_fin] at hmod
  have hdvd : p ∣ ((x : Perm (Fin n)).support).card := by
    have h1 : p ∣ n - m := (Nat.modEq_iff_dvd' (by omega)).1 hmod
    have h2 : ((x : Perm (Fin n)).support).card = n - m := by omega
    rw [h2]
    exact h1
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < ((x : Perm (Fin n)).support).card :=
    Nat.pos_of_ne_zero (fun h => hσ1 (Equiv.Perm.card_support_eq_zero.1 h))
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  obtain ⟨e⟩ := nonempty_range_ofSubtype_equiv ((x : Perm (Fin n)).support)ᶜ m hm
  have hIdvd : Nat.card I ∣ m.factorial := by
    have h1 := Subgroup.card_dvd_of_le hIF
    rw [Nat.card_congr e.toEquiv] at h1
    exact h1.trans (by simpa using natCard_alternatingGroup_dvd_factorial (Fin m))
  haveI : Nontrivial ↥I := nontrivial_of_glaPComponent hp hI
  have hm5 : 5 ≤ m := by
    by_contra hlt
    haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hI)
    exact false_of_isPerfect_of_card_dvd_twentyFour
      (hIdvd.trans (factorial_dvd_twentyFour (not_le.1 hlt)))
  have hm5' : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm5
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hm5'
  haveI : IsSimpleGroup ↥(alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range :=
    e.isSimpleGroup
  have hFC : (alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range ≤
      fixSubgroup (MulAut.conj x) := fun k hk =>
    mem_fixSubgroup_conj.2 (Subtype.ext (commute_of_mem_range_ofSubtype_compl hk).eq)
  have hIeq := eq_of_isSubnormal_of_isSimpleGroup (glaPComponent_of_le hp hI hIF hFC).2.1
    ((Subgroup.nontrivial_iff_ne_bot I).1 inferInstance)
  exact ⟨m, k, hm5, hk0, by rw [← hsupp, hk]; ring, ⟨(MulEquiv.subgroupCongr hIeq).trans e⟩⟩

theorem up7a8_alt_iso_eq {m k : ℕ} (hm : 5 ≤ m) (hk : 5 ≤ k)
    (e : alternatingGroup (Fin m) ≃* alternatingGroup (Fin k)) : m = k := by
  have hc : ∀ j : ℕ, 5 ≤ j → Nat.card (alternatingGroup (Fin j)) = j.factorial / 2 := by
    intro j hj
    haveI : Nontrivial (Fin j) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have hcard : Nat.card (alternatingGroup (Fin m)) = Nat.card (alternatingGroup (Fin k)) :=
    Nat.card_congr e.toEquiv
  rw [hc m hm, hc k hk] at hcard
  have hm2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hk2 : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hfac : m.factorial = k.factorial := by
    have h1 := Nat.div_mul_cancel hm2
    have h2 := Nat.div_mul_cancel hk2
    rw [← h1, ← h2, hcard]
  exact (Nat.factorial_inj (by omega)).1 hfac

theorem up7a8_odd_center {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : GLAPComponent 3 X K) : Odd (Nat.card (Subgroup.center (PQuot 3 K))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : CFSG.pPrimeCore 3 (PQuot 3 K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  rw [Nat.odd_iff]
  by_contra hev
  have h2 : 2 ∣ Nat.card (Subgroup.center (PQuot 3 K)) := by
    omega
  haveI := Fintype.ofFinite (Subgroup.center (PQuot 3 K))
  have h2' : 2 ∣ Fintype.card (Subgroup.center (PQuot 3 K)) := by
    rw [← Nat.card_eq_fintype_card]
    exact h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 h2'
  have hzc : (z : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := z.2
  set N : Subgroup (PQuot 3 K) := Subgroup.zpowers (z : PQuot 3 K) with hN
  have hNnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute g (z : PQuot 3 K) := Subgroup.mem_center_iff.1 hzc g
    have hgz : g * (z : PQuot 3 K) ^ j * g⁻¹ = (z : PQuot 3 K) ^ j := by
      rw [(hcomm.zpow_right j).eq, mul_inv_cancel_right]
    rw [hgz, hN]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
  have hzord : orderOf (z : PQuot 3 K) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hNcard : Nat.card N = 2 := by
    rw [hN, Nat.card_zpowers, hzord]
  have hNle : N ≤ CFSG.pPrimeCore 3 (PQuot 3 K) := by
    unfold CFSG.pPrimeCore
    exact le_sSup ⟨hNnorm, by rw [hNcard]; norm_num⟩
  rw [hbot, le_bot_iff] at hNle
  have hz1 : (z : PQuot 3 K) = 1 := by
    have : (z : PQuot 3 K) ∈ N := Subgroup.mem_zpowers _
    rw [hNle, Subgroup.mem_bot] at this
    exact this
  rw [hz1, orderOf_one] at hzord
  norm_num at hzord

theorem up7a8_center_bot {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : GLAPComponent 3 X K) {n : ℕ} (hn : 8 ≤ n)
    (e : PSimple 3 K ≃* alternatingGroup (Fin n)) : Subgroup.center (PQuot 3 K) = ⊥ :=
  CFSG.ComponentClassification.RankTwoAlt.center_eq_bot_of_odd
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK).1 hn e (up7a8_odd_center hK)

end CFSG.LocalAnalysis.GLTheoremA
