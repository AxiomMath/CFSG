module

public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Bar

variable {G : Type} [Group G]

theorem LC_le_Cen (z : G) : LC z ≤ Cen z := Subgroup.map_subtype_le _

theorem mem_Cen_self (z : G) : z ∈ Cen z :=
  Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]

theorem ker_toBar (z : G) : (toBar z).ker = pPrimeCore 2 ↥(Cen z) := QuotientGroup.ker_mk' _

theorem toBar_surjective (z : G) : Function.Surjective (toBar z) := QuotientGroup.mk'_surjective _

theorem odd_card_ker_toBar [Finite G] (z : G) : Odd (Nat.card (toBar z).ker) := by
  rw [ker_toBar]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))

theorem toBar_z_mem_center (z : G) : toBar z ⟨z, mem_Cen_self z⟩ ∈ center (CentralizerBar z) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨c, rfl⟩ := toBar_surjective z y
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp c.2 z (Set.mem_singleton z)).symm

theorem z_mem_of_toBar_eq [Finite G] {z : G} (hz : orderOf z = 2) {K : Subgroup G} {k : G} (hk : k ∈ K)
    (hkC : k ∈ Cen z) (h : toBar z ⟨k, hkC⟩ = toBar z ⟨z, mem_Cen_self z⟩) : z ∈ K := by
  have hn : (⟨k, hkC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩ ∈ (toBar z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hodd : Odd (orderOf ((⟨k, hkC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩ : ↥(Cen z))) := by
    have h1 : orderOf (⟨_, hn⟩ : (toBar z).ker) ∣ Nat.card (toBar z).ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (odd_card_ker_toBar z) h1
  set m := orderOf ((⟨k, hkC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩ : ↥(Cen z)) with hm
  have hpow : ((⟨k, hkC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩) ^ m = 1 := pow_orderOf_eq_one _
  have hpowG : (k⁻¹ * z) ^ m = 1 := by
    have := congrArg (fun x : ↥(Cen z) => (x : G)) hpow
    simpa using this
  have hcomm : Commute k⁻¹ z := by
    have : Commute k z := (Subgroup.mem_centralizer_iff.mp hkC z (Set.mem_singleton z)).symm
    exact this.inv_left
  rw [hcomm.mul_pow, inv_pow] at hpowG
  obtain ⟨j, hj⟩ := hodd
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hzm : z ^ m = z := by
    rw [hj, pow_succ, pow_mul, hz2, one_pow, one_mul]
  rw [hzm, inv_mul_eq_one] at hpowG
  rw [← hpowG]
  exact Subgroup.pow_mem K hk m

end Bar

end CFSG.GH74.GLS.Stage2.Local
