module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup

theorem commute_of_isCyclic_two_group {G : Type} [Group G] (R : Subgroup G) [IsCyclic R]
    (hR : IsPGroup 2 R) (z : G) (hz : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (R : Set G)) : ∀ y ∈ R, z * y = y * z := by
  obtain ⟨g, hgR, hgen⟩ : ∃ g ∈ R, ∀ y ∈ R, ∃ m : ℤ, g ^ m = y := by
    obtain ⟨g', hg'⟩ := IsCyclic.exists_generator (α := R)
    refine ⟨(g' : G), g'.2, fun y hy => ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg' ⟨y, hy⟩)
    exact ⟨m, by simpa [Subgroup.coe_zpow] using congrArg (fun x : R => (x : G)) hm⟩
  have hconj : ∀ h ∈ R, z * h * z⁻¹ ∈ R := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp hzN h).mp hh
  obtain ⟨j, hj⟩ := hgen (z * g * z⁻¹) (hconj g hgR)
  have hconjpow : ∀ m : ℤ, z * g ^ m * z⁻¹ = g ^ (j * m) := by
    intro m
    rw [← conj_zpow, ← hj, ← zpow_mul]
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hz3' : z * z * z = 1 := (pow_three' z).symm.trans hz3
  have hC : z * (z * (z * g * z⁻¹) * z⁻¹) * z⁻¹ = g := by
    have e3 : z * (z * (z * g * z⁻¹) * z⁻¹) * z⁻¹ = (z * z * z) * g * (z * z * z)⁻¹ := by
      group
    rw [e3, hz3', inv_one, mul_one, one_mul]
  have hg3 : g ^ (j * (j * j)) = g := by
    rw [← hconjpow (j * j), ← hconjpow j, hj]
    exact hC
  have hg3' : g ^ (j * (j * j) - 1) = 1 := by
    rw [zpow_sub, hg3, zpow_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hR ⟨g, hgR⟩
  have hk' : g ^ (2 ^ k) = 1 := by
    simpa [Subgroup.coe_pow] using congrArg Subtype.val hk
  have hgN : g ^ ((2 : ℤ) ^ k) = 1 := by
    rw [show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hk'
  obtain ⟨q, hq⟩ := Int.even_mul_succ_self j
  have ht : j * j + j + 1 = 2 * q + 1 := by linear_combination hq
  have hcop : IsCoprime ((2 : ℤ) ^ k) (j * j + j + 1) := by
    have h2q : IsCoprime (2 : ℤ) (2 * q + 1) := ⟨-q, 1, by ring⟩
    rw [ht]
    exact h2q.pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have hX : (g ^ (j - 1)) ^ ((2 : ℤ) ^ k) = 1 := by
    rw [← zpow_mul, zpow_mul', hgN, one_zpow]
  have hY : (g ^ (j - 1)) ^ (j * j + j + 1) = 1 := by
    rw [← zpow_mul, show (j - 1) * (j * j + j + 1) = j * (j * j) - 1 by ring, hg3']
  have key : g ^ (j - 1) = 1 := by
    have e1 : g ^ (j - 1) = (g ^ (j - 1)) ^ (a * (2 : ℤ) ^ k + b * (j * j + j + 1)) := by
      rw [hab, zpow_one]
    rw [e1, zpow_add, zpow_mul', zpow_mul', hX, hY, one_zpow, one_zpow, mul_one]
  have hgj : g ^ j = g := by
    have h1 : g ^ (j - 1 + 1) = g ^ (j - 1) * g ^ (1 : ℤ) := zpow_add g (j - 1) 1
    rw [show j - 1 + 1 = j by ring, key, zpow_one, one_mul] at h1
    exact h1
  have hzg : z * g * z⁻¹ = g := hj.symm.trans hgj
  have hcomm : Commute z g := mul_inv_eq_iff_eq_mul.mp hzg
  intro y hy
  obtain ⟨m, rfl⟩ := hgen y hy
  exact (hcomm.zpow_right m).eq

theorem isCyclic_of_two_group_of_quotient_cyclic {H : Type} [Group H] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (P' : Subgroup H) [P'.Normal] (hP' : IsPGroup p P') (hq : IsCyclic (H ⧸ P'))
    (R : Subgroup H) (hR : IsPGroup 2 R) : IsCyclic R := by
  have hcop : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr (Ne.symm hp2)
  let f : R →* H ⧸ P' := (QuotientGroup.mk' P').comp R.subtype
  apply isCyclic_of_injective f
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxP : (x : H) ∈ P' := (QuotientGroup.eq_one_iff (N := P') (x : H)).mp hx
  obtain ⟨a, ha⟩ := hR x
  obtain ⟨b, hb⟩ := hP' ⟨(x : H), hxP⟩
  have ha' : (x : H) ^ 2 ^ a = 1 := by
    simpa [Subgroup.coe_pow] using congrArg Subtype.val ha
  have hb' : (x : H) ^ p ^ b = 1 := by
    simpa [Subgroup.coe_pow] using congrArg Subtype.val hb
  have hg : (x : H) ^ Nat.gcd (2 ^ a) (p ^ b) = 1 := pow_gcd_eq_one.mpr ⟨ha', hb'⟩
  rw [show Nat.gcd (2 ^ a) (p ^ b) = 1 from Nat.Coprime.pow a b hcop, pow_one] at hg
  exact Subtype.ext (by simpa using hg)

private theorem dihedral_rotation_or_reflection {n : ℕ} (w : DihedralGroup n) :
    (∃ i : ZMod n, w = DihedralGroup.r i) ∨ (∃ j : ZMod n, w = DihedralGroup.sr j) := by
  cases w with
  | r i => exact Or.inl ⟨i, rfl⟩
  | sr j => exact Or.inr ⟨j, rfl⟩

theorem commute_of_dihedral {H : Type} [Group H] {n : ℕ} (e : H ≃* DihedralGroup n) (z : H)
    (hz : orderOf z = 3) (R : Subgroup H) (hR : IsPGroup 2 R)
    (hzN : z ∈ Subgroup.normalizer (R : Set H)) : ∀ y ∈ R, z * y = y * z := by
  have hconj : ∀ h ∈ R, z * h * z⁻¹ ∈ R := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp hzN h).mp hh
  have hezord : orderOf (e z) = 3 := by
    rw [← hz]
    exact orderOf_injective e.toMonoidHom e.injective z
  obtain ⟨i, hi⟩ : ∃ i : ZMod n, e z = DihedralGroup.r i := by
    rcases dihedral_rotation_or_reflection (e z) with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact ⟨i, hi⟩
    · rw [hj, DihedralGroup.orderOf_sr] at hezord
      norm_num at hezord
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have h3 : i * ((3 : ℕ) : ZMod n) = 0 := by
    have h := congrArg (⇑e) hz3
    rw [map_pow, map_one, hi, DihedralGroup.r_pow, DihedralGroup.one_def] at h
    exact DihedralGroup.r.inj h
  have h3' : i * 3 = 0 := by exact_mod_cast h3
  intro y hy
  rcases dihedral_rotation_or_reflection (e y) with ⟨j, hj⟩ | ⟨j, hj⟩
  ·
    apply e.injective
    rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  ·
    exfalso
    have hc : y * z * y⁻¹ * z⁻¹ ∈ R := by
      have h1 : z * y⁻¹ * z⁻¹ ∈ R := hconj y⁻¹ (R.inv_mem hy)
      have h2 : y * (z * y⁻¹ * z⁻¹) ∈ R := R.mul_mem hy h1
      simpa only [mul_assoc] using h2
    have hcz : y * z * y⁻¹ * z⁻¹ = z := by
      apply e.injective
      simp only [map_mul, map_inv, hi, hj]
      rw [DihedralGroup.inv_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r]
      congr 1
      linear_combination (-1 : ZMod n) * h3'
    rw [hcz] at hc
    obtain ⟨k, hk⟩ := hR ⟨z, hc⟩
    have hzk : z ^ 2 ^ k = 1 := by
      simpa [Subgroup.coe_pow] using congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := by
      have h := orderOf_dvd_of_pow_eq_one hzk
      rwa [hz] at h
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h2

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
