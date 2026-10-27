module

public import CFSG.GH74.KGroups.TwoM12Syl3
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeShapeProd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.GH74.KGroups.TwoM12

@[expose] def c27 : Perm (Fin 12) := x27 * y27 * x27⁻¹ * y27⁻¹

@[expose] def g27 : Perm (Fin 12) :=
  m12gA * m12gB⁻¹ * m12gA * m12gB * m12gA * m12gB⁻¹ * m12gA * m12gB * m12gA

@[expose] def t27 : Perm (Fin 12) := x27⁻¹ * y27 * x27

theorem g27_conj : g27 * c27 * g27⁻¹ = t27 := by decide +kernel

theorem c27_comm_x : c27 * x27 = x27 * c27 := by decide +kernel

theorem c27_comm_y : c27 * y27 = y27 * c27 := by decide +kernel

theorem c27_ne_one : c27 ≠ 1 := by decide +kernel

theorem c27_cube : c27 ^ 3 = 1 := by decide +kernel

theorem t27_cube : t27 ^ 3 = 1 := by decide +kernel

theorem t27_noncomm : t27 * x27 ≠ x27 * t27 := by decide +kernel

theorem t27_sq_noncomm : t27 ^ 2 * x27 ≠ x27 * t27 ^ 2 := by decide +kernel

theorem x27_y27_noncomm : x27 * y27 ≠ y27 * x27 := by decide +kernel

theorem g27_mem : g27 ∈ NativeSporadic.M12 := by
  have ha : m12gA ∈ NativeSporadic.M12 := m12a.2
  have hb : m12gB ∈ NativeSporadic.M12 := m12b.2
  have hb' : m12gB⁻¹ ∈ NativeSporadic.M12 := NativeSporadic.M12.inv_mem hb
  exact NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem
    (NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem
    (NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem ha hb') ha) hb) ha) hb') ha) hb) ha

theorem c27_mem : c27 ∈ T27 := by
  unfold c27
  exact T27.mul_mem (T27.mul_mem (T27.mul_mem x27_mem_T27 y27_mem_T27)
    (T27.inv_mem x27_mem_T27)) (T27.inv_mem y27_mem_T27)

theorem t27_mem : t27 ∈ T27 := by
  unfold t27
  exact T27.mul_mem (T27.mul_mem (T27.inv_mem x27_mem_T27) y27_mem_T27) x27_mem_T27

theorem mem_zpowers_c27 {s : Perm (Fin 12)} (hs : s ∈ T27)
    (hc : ∀ t ∈ T27, t * s = s * t) : s ∈ Subgroup.zpowers c27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnc : ¬ ∀ u v : T27, u * v = v * u := by
    intro h
    have h1 := congrArg Subtype.val (h ⟨x27, x27_mem_T27⟩ ⟨y27, y27_mem_T27⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_mk] at h1
    exact x27_y27_noncomm h1
  have hle := L28Sq.card_center_le_three card_T27 hnc
  have hcZ : (⟨c27, c27_mem⟩ : T27) ∈ Subgroup.center T27 := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨u, hu⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    have hle' : T27 ≤ Subgroup.centralizer ({c27} : Set (Perm (Fin 12))) := by
      rw [T27_eq, Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr c27_comm_x.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr c27_comm_y.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle' hu))
  have hoc : orderOf (⟨c27, c27_mem⟩ : T27) = 3 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => c27_ne_one ?_
    · simp only [SubgroupClass.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one]
      exact c27_cube
    · have h1 := congrArg Subtype.val h
      simpa only [Subgroup.coe_mk, OneMemClass.coe_one] using h1
  have hZ : Subgroup.center T27 = Subgroup.zpowers ⟨c27, c27_mem⟩ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hcZ) ?_
    rw [Nat.card_zpowers, hoc]
    exact hle
  have hsZ : (⟨s, hs⟩ : T27) ∈ Subgroup.center T27 := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨u, hu⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    exact hc u hu
  rw [hZ] at hsZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsZ
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h1 := congrArg Subtype.val hk
  simpa only [SubgroupClass.coe_zpow, Subgroup.coe_mk] using h1

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
