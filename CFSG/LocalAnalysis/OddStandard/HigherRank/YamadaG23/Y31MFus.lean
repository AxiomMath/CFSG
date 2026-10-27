module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Cyc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFConj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_M_invol_fusion (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    {t' : G} (ht'M : t' ∈ L ⊔ centIn s.H L) (ht'2 : orderOf t' = 2) (hne : t' ≠ s.t) :
    ∃ l ∈ L, l * t' * l⁻¹ = s.fr.z ∨ l * t' * l⁻¹ = s.fr.z * s.t := by
  have hA : LFactsA s := lfactsA_of_setting hS hZ s
  have hCH : centIn s.H L ≤ s.H := inf_le_left
  have hCnorm : centIn s.H L ≤ Subgroup.normalizer (L : Set G) := hCH.trans (s3_H_le_N s hS)
  have ht'M' : t' ∈ (L : Set G) * (centIn s.H L : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L (centIn s.H L) hCnorm]
    exact ht'M
  obtain ⟨a, haL, c, hcC, hac⟩ := Set.mem_mul.mp ht'M'
  have hcomm : Commute a c :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcC).2 a haL
  have ht'sq : t' ^ 2 = 1 := by simpa [ht'2] using pow_orderOf_eq_one t'
  have ha2c2 : a ^ 2 * c ^ 2 = 1 := by
    have h := ht'sq
    rw [← hac, hcomm.mul_pow 2] at h
    exact h
  have hc2 : c ^ 2 = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right ha2c2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = orderOf (a ^ 2) := ⟨orderOf (a ^ 2), rfl⟩
  have ha2L : a ^ 2 ∈ L := Subgroup.pow_mem L haL 2
  have ha2eq : a ^ 2 = (c ^ 2)⁻¹ := by rw [hc2, inv_inv]
  have ha2cent : a ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
    rw [ha2eq]
    exact (Subgroup.centralizer (L : Set G)).inv_mem
      (Subgroup.pow_mem (Subgroup.centralizer (L : Set G)) (Subgroup.mem_inf.mp hcC).2 2)
  have ha2z : (⟨a ^ 2, ha2L⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp ha2cent g g.2)
  have hdvd : orderOf (a ^ 2) ∣ Nat.card ↥(center ↥L) := by
    have h : orderOf (⟨a ^ 2, ha2L⟩ : ↥L) ∣ Nat.card ↥(center ↥L) :=
      (center ↥L).orderOf_dvd_natCard ha2z
    rwa [Subgroup.orderOf_mk (a ^ 2) ha2L] at h
  have hoddm : Odd m := by rw [hm]; exact Odd.of_dvd_nat hZ hdvd
  have hpow2m : (a ^ 2) ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one (a ^ 2)
  have ht'pow : t' ^ m = t' := by
    obtain ⟨k, hk⟩ := hoddm
    rw [hk, pow_add, pow_mul, ht'sq, one_pow, one_mul, pow_one]
  have ht'eq : t' = a ^ m * c ^ m := by
    rw [← ht'pow, ← hac, hcomm.mul_pow m]
  have hl'sq : (a ^ m) ^ 2 = 1 := by
    calc (a ^ m) ^ 2 = a ^ (m * 2) := (pow_mul a m 2).symm
      _ = a ^ (2 * m) := by rw [Nat.mul_comm]
      _ = (a ^ 2) ^ m := pow_mul a 2 m
      _ = 1 := hpow2m
  have hc'sq : (c ^ m) ^ 2 = 1 := by
    calc (c ^ m) ^ 2 = c ^ (m * 2) := (pow_mul c m 2).symm
      _ = c ^ (2 * m) := by rw [Nat.mul_comm]
      _ = (c ^ 2) ^ m := pow_mul c 2 m
      _ = ((a ^ 2)⁻¹) ^ m := by rw [hc2]
      _ = ((a ^ 2) ^ m)⁻¹ := inv_pow _ _
      _ = 1 := by rw [hpow2m, inv_one]
  have hc'C : c ^ m ∈ centIn s.H L := Subgroup.pow_mem (centIn s.H L) hcC m
  have hc'_eq : c ^ m = 1 ∨ c ^ m = s.t := by
    by_cases h1 : c ^ m = 1
    · exact Or.inl h1
    · exact Or.inr (s3_invol_cenH (s := s) hS hc'C (orderOf_eq_prime hc'sq h1))
  have ht'ne1 : t' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht'2
    omega
  have hl'L : a ^ m ∈ L := Subgroup.pow_mem L haL m
  have hl'ne : a ^ m ≠ 1 := by
    intro hl'1
    have ht'cm : t' = c ^ m := by rw [ht'eq, hl'1, one_mul]
    rcases hc'_eq with hc'1 | hc't
    · exact ht'ne1 (by rw [ht'cm, hc'1])
    · exact hne (by rw [ht'cm, hc't])
  have hl'2 : orderOf (a ^ m) = 2 := orderOf_eq_prime hl'sq hl'ne
  obtain ⟨l₀, hl₀L, hconj⟩ :=
    s3_invol_conj hS hZ s hl'L hl'2 (s3_z_mem_L s) (s3_z_order s hA)
  have hc'comm : Commute l₀ (c ^ m) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc'C).2 l₀ hl₀L
  have hconjc : l₀ * c ^ m * l₀⁻¹ = c ^ m := by
    rw [hc'comm]
    group
  have hmain : l₀ * t' * l₀⁻¹ = s.fr.z * c ^ m := by
    rw [ht'eq]
    calc l₀ * (a ^ m * c ^ m) * l₀⁻¹
        = (l₀ * a ^ m * l₀⁻¹) * (l₀ * c ^ m * l₀⁻¹) := by group
      _ = s.fr.z * c ^ m := by rw [← hconj, hconjc]
  refine ⟨l₀, hl₀L, ?_⟩
  rcases hc'_eq with hc'1 | hc't
  · left
    rw [hmain, hc'1, mul_one]
  · right
    rw [hmain, hc't]

end CFSG.OddStandard.HigherRank.YamadaG23
