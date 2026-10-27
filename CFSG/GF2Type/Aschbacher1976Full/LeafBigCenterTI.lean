module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.BorelTits.Basic
import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicRootTI
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate

public section

namespace CFSG.GF2Type.Aschbacher1976Full.LeafBigCenter

open Subgroup CFSG CFSG.LocalAnalysis.GorensteinLyons

variable {G : Type} [Group G] [Finite G]

theorem orderOf_conj_eq (g z : G) : orderOf (g * z * g⁻¹) = orderOf z := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g) z
  rwa [MulAut.conj_apply] at h

theorem conjugate_one_eq (A : Subgroup G) : conjugate A 1 = A := by
  ext x
  simp [mem_conjugate_iff_conj_mem]

theorem involution_eq_of_isCyclic {A : Subgroup G} (hA : IsCyclic A) {z y : G} (hzA : z ∈ A)
    (hyA : y ∈ A) (hz2 : orderOf z = 2) (hy2 : orderOf y = 2) : y = z := by
  have hcard : Nat.card (zpowers y) = Nat.card (zpowers z) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hy2, hz2]
  have heq : zpowers y = zpowers z :=
    CFSG.DisconnectedInvolutionGraph.Helpers.cyclic_overgroup_equal_card_subgroups A
      (zpowers y) (zpowers z) (zpowers_le.mpr hyA) (zpowers_le.mpr hzA) hcard
  have hy : y ∈ zpowers z := by
    rw [← heq]
    exact mem_zpowers y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmod : z ^ (k % 2) = z ^ k := by
    have h := zpow_mod_orderOf z k
    rw [hz2] at h
    exact_mod_cast h
  have hy' : y = z ^ (k % 2) := by
    rw [hmod, hk]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hy'
    rw [hy', orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  · rw [h1, zpow_one] at hy'
    exact hy'

theorem normalizer_le_centralizer_of_isCyclic {A : Subgroup G} (hA : IsCyclic A) {z : G}
    (hzA : z ∈ A) (hz2 : orderOf z = 2) :
    normalizer (A : Set G) ≤ centralizer ({z} : Set G) := by
  intro g hg
  have hgz : g * z * g⁻¹ ∈ A := (mem_normalizer_iff.mp hg z).mp hzA
  have heq : g * z * g⁻¹ = z :=
    involution_eq_of_isCyclic hA hzA hgz hz2 ((orderOf_conj_eq g z).trans hz2)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq)

theorem ti_of_bigCenter {Y : Subgroup G} (hY : IsCyclic Y) (hY2 : IsPGroup 2 Y) {z : G}
    (hzY : z ∈ Y) (hz2 : orderOf z = 2)
    (hN : ∀ g ∈ centralizer ({z} : Set G), conjugate Y g = Y) :
    ∀ g : G, conjugate Y g = Y ∨ Y ⊓ conjugate Y g = ⊥ := by
  intro g
  by_cases hbot : Y ⊓ conjugate Y g = ⊥
  · exact Or.inr hbot
  left
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : IsPGroup 2 (Y ⊓ conjugate Y g : Subgroup G) := hY2.to_le inf_le_left
  have hgt : 1 < Nat.card (Y ⊓ conjugate Y g : Subgroup G) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    exact hbot
  have hdvd : 2 ∣ Nat.card (Y ⊓ conjugate Y g : Subgroup G) := by
    rcases hK2.card_eq_or_dvd with h1 | h1
    · omega
    · exact h1
  obtain ⟨u, hu⟩ :=
    exists_prime_orderOf_dvd_card' (G := (Y ⊓ conjugate Y g : Subgroup G)) 2 hdvd
  have hu' : orderOf (u : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hu
  have huY : (u : G) ∈ Y := (Subgroup.mem_inf.mp u.2).1
  have hug : (u : G) ∈ conjugate Y g := (Subgroup.mem_inf.mp u.2).2
  have hzu : (u : G) = z := involution_eq_of_isCyclic hY hzY huY hz2 hu'
  have hzg : z ∈ conjugate Y g := hzu ▸ hug
  have hgz : g * z * g⁻¹ ∈ Y := mem_conjugate_iff_conj_mem.mp hzg
  have heq : g * z * g⁻¹ = z :=
    involution_eq_of_isCyclic hY hzY hgz hz2 ((orderOf_conj_eq g z).trans hz2)
  exact hN g (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq))

theorem exists_order_four_of_isCyclic {Y : Subgroup G} (hY : IsCyclic Y) (hY2 : IsPGroup 2 Y)
    (h8 : 8 ≤ Nat.card Y) {z : G} (hzY : z ∈ Y) (hz2 : orderOf z = 2) :
    ∃ x ∈ Y, orderOf x = 4 ∧ x ^ 2 = z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY2
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_one] at h2
    have h8' : 8 ≤ 2 ^ n := hn ▸ h8
    omega
  have h4 : 4 ∣ Nat.card Y := by
    have e : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [hn, e]
    exact pow_dvd_pow 2 hn2
  obtain ⟨y₀, hy₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
  have hyo : orderOf (y₀ : G) = Nat.card Y := by
    rw [Subgroup.orderOf_coe, hy₀]
  have hne : Nat.card Y / 4 ≠ 0 := by omega
  have hdvd : Nat.card Y / 4 ∣ orderOf (y₀ : G) := by
    rw [hyo]
    exact Nat.div_dvd_of_dvd h4
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = (y₀ : G) ^ (Nat.card Y / 4) := ⟨_, rfl⟩
  have hx4 : orderOf x = 4 := by
    rw [hxdef, orderOf_pow_of_dvd hne hdvd, hyo, Nat.div_div_self h4 (by omega)]
  have hxY : x ∈ Y := by
    rw [hxdef]
    exact Y.pow_mem y₀.2 _
  have h2dvd : 2 ∣ orderOf x := by
    rw [hx4]
    norm_num
  have hx22 : orderOf (x ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd two_ne_zero h2dvd, hx4]
  exact ⟨x, hxY, hx4, involution_eq_of_isCyclic hY hzY (Y.pow_mem hxY 2) hz2 hx22⟩

theorem centralizer_le_normalizer_fz (z : G) :
    centralizer ({z} : Set G) ≤ normalizer ((Fz z : Subgroup G) : Set G) := by
  haveI : (generalizedFitting ↥(Hz z)).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥(Hz z))).1
  exact (Subgroup.le_normalizer).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (generalizedFitting ↥(Hz z)))

end CFSG.GF2Type.Aschbacher1976Full.LeafBigCenter
