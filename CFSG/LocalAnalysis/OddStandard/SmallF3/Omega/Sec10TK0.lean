module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TQ8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10T_two_elem_K0 [Finite G] (hK0 : Asc82Lemma10K0) (h36 : Asc82Lemma36)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {v : G}
    (hv : v ∈ secK0 t z) (hv2 : ∃ m : ℕ, v ^ (2 ^ m) = 1) : v ∈ secQ K1 K2 := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hOleC : oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (L : Set G) :=
    sec10K0_oddCore_le_centralizer hpsp hzL hz2 hLt hN
  have hK1L : K1 ≤ L := hctx.pocket1.2.1.trans inf_le_left
  have hK2L : K2 ≤ L := hctx.pocket2.2.1.trans inf_le_left
  have hKsupL : K1 ⊔ K2 ≤ L := sup_le hK1L hK2L
  have hvO : v ∈ oddCoreIn (centralizer ({t} : Set G)) ⊔ K1 ⊔ K2 := by
    rw [← (hK0 G t L S z K1 K2 hctx).1]; exact hv
  rw [sup_assoc] at hvO
  have hcOK : ∀ h ∈ oddCoreIn (centralizer ({t} : Set G)), ∀ k ∈ K1 ⊔ K2, h * k = k * h := by
    intro h hh k hk
    exact (Subgroup.mem_centralizer_iff.mp (hOleC hh) k (hKsupL hk)).symm
  obtain ⟨o, hoO, k, hkK, hvk⟩ := exists_mul_of_mem_sup_of_commute hcOK hvO
  have hc12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  obtain ⟨a, haK1, b, hbK2, hkab⟩ := exists_mul_of_mem_sup_of_commute hc12 hkK
  obtain ⟨m, hm⟩ := hv2
  have hoc : Commute o k := hcOK o hoO k hkK
  have hprod : o ^ (2 ^ m) * k ^ (2 ^ m) = 1 := by
    rw [← hoc.mul_pow (2 ^ m), ← hvk, hm]
  have ho_inv : o ^ (2 ^ m) = (k ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hkL : k ∈ L := hKsupL hkK
  have ho_pow_inf : o ^ (2 ^ m) ∈ L ⊓ centralizer (L : Set G) := by
    refine ⟨?_, Subgroup.pow_mem _ (hOleC hoO) (2 ^ m)⟩
    rw [ho_inv]
    exact L.inv_mem (Subgroup.pow_mem L hkL (2 ^ m))
  have ho_pow_one : o ^ (2 ^ m) = 1 := by
    have hbot : o ^ (2 ^ m) ∈ (⊥ : Subgroup G) := by rw [← hLC]; exact ho_pow_inf
    simpa using hbot
  have hdvdO : orderOf o ∣ Nat.card (oddCoreIn (centralizer ({t} : Set G))) :=
    (oddCoreIn (centralizer ({t} : Set G))).orderOf_dvd_natCard hoO
  have hoddO : Odd (orderOf o) :=
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (centralizer ({t} : Set G))).of_dvd_nat
      hdvdO
  have hoorder : orderOf o ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one ho_pow_one
  have hcop : Nat.Coprime (orderOf o) (2 ^ m) :=
    (Nat.coprime_two_right.mpr hoddO).pow_right m
  have ho1 : o = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hoorder)
  have hvk2 : v = k := by rw [hvk, ho1, one_mul]
  have hk_pow : k ^ (2 ^ m) = 1 := by rw [← hvk2]; exact hm
  have hab_comm : Commute a b := hc12 a haK1 b hbK2
  have hab_pow : a ^ (2 ^ m) * b ^ (2 ^ m) = 1 := by
    rw [← hab_comm.mul_pow (2 ^ m), ← hkab, hk_pow]
  have hK1K2 : K1 ⊓ K2 = zpowers z := (sec10KS_main hP5 hC5 hpsp hctx).2.2
  have ha_pow_inf : a ^ (2 ^ m) ∈ K1 ⊓ K2 :=
    ⟨Subgroup.pow_mem K1 haK1 (2 ^ m), by
      rw [eq_inv_of_mul_eq_one_left hab_pow]
      exact K2.inv_mem (Subgroup.pow_mem K2 hbK2 (2 ^ m))⟩
  have hz_dvd : orderOf z ∣ 2 := by rw [hz2]
  have ha_z : a ^ (2 ^ m) ∈ zpowers z := by rw [← hK1K2]; exact ha_pow_inf
  have ha_sq : (a ^ (2 ^ m)) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers ha_z).trans hz_dvd)
  have ha_pow_succ : a ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, ha_sq]
  have hb_pow_inf : b ^ (2 ^ m) ∈ K1 ⊓ K2 :=
    ⟨by
      rw [eq_inv_of_mul_eq_one_right hab_pow]
      exact K1.inv_mem (Subgroup.pow_mem K1 haK1 (2 ^ m)), Subgroup.pow_mem K2 hbK2 (2 ^ m)⟩
  have hb_z : b ^ (2 ^ m) ∈ zpowers z := by rw [← hK1K2]; exact hb_pow_inf
  have hb_sq : (b ^ (2 ^ m)) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hb_z).trans hz_dvd)
  have hb_pow_succ : b ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, hb_sq]
  have haQ1 : a ∈ twoCoreIn K1 :=
    sec10T_two_elem_Q1 hP5 hC5 hpsp hctx haK1 ⟨m + 1, ha_pow_succ⟩
  have hbQ2 : b ∈ twoCoreIn K2 :=
    sec10T_two_elem_Q1 hP5 hC5 hpsp hctx.swap hbK2 ⟨m + 1, hb_pow_succ⟩
  have hvab : v = a * b := by rw [hvk, ho1, one_mul, hkab]
  rw [sec10KS_twoCore_sup hP5 hC5 hpsp hctx, hvab]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haQ1) (Subgroup.mem_sup_right hbQ2)

end CFSG.OddStandard.SmallF3.Omega
