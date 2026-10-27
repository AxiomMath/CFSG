module

public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {m : ℕ}

theorem quaternionGroup_orderOf_a_self (hm : 1 ≤ m) :
    orderOf (a (m : ZMod (2 * m)) : QuaternionGroup m) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self, a_zero]
  · rw [Ne, ← a_zero, a.injEq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega

theorem mem_nativeQuaternionZ_iff (hm : 1 ≤ m) {y : QuaternionGroup m} :
    y ∈ CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ m ↔ y = 1 ∨ y = a m := by
  constructor
  · intro hy
    change y ∈ Subgroup.zpowers _ at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_mod_orderOf, quaternionGroup_orderOf_a_self hm]
    have h0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h1 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
    obtain h | h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem quaternionGroup_a_two_pow (k : ℕ) :
    (a 2 : QuaternionGroup m) ^ k = a ((2 * k : ℕ) : ZMod (2 * m)) := by
  rw [← a_one_pow, pow_mul, a_one_pow, Nat.cast_ofNat]

theorem quaternionGroup_a_self_mem_zpowers (hm : Even m) :
    (a (m : ZMod (2 * m)) : QuaternionGroup m) ∈ Subgroup.zpowers (a 2) := by
  obtain ⟨k, rfl⟩ := hm
  rw [show ((k + k : ℕ) : ZMod (2 * (k + k))) = ((2 * k : ℕ) : ZMod (2 * (k + k))) from
    congrArg (fun x : ℕ => (x : ZMod (2 * (k + k)))) (two_mul k).symm,
    ← quaternionGroup_a_two_pow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem quaternionGroup_mul_self_mem_zpowers [NeZero m] (hm : Even m) (y : QuaternionGroup m) :
    y * y ∈ Subgroup.zpowers (a 2) := by
  rcases y with i | i
  · rw [a_mul_a, show i + i = ((2 * i.val : ℕ) : ZMod (2 * m)) by
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring, ← quaternionGroup_a_two_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [xa_mul_xa, add_sub_cancel_right]
    exact quaternionGroup_a_self_mem_zpowers hm

theorem quaternionGroup_conj_xa (i : ZMod (2 * m)) :
    (a 1 : QuaternionGroup m) * xa i * (a 1)⁻¹ = xa (i - 2) := by
  change a 1 * xa i * a (-1) = xa (i - 2)
  rw [a_mul_xa, xa_mul_a]
  congr 1
  ring

theorem quaternionGroup_isSquare [NeZero m] (hm : 4 ∣ m) {i : ZMod (2 * m)}
    (hi : (a i : QuaternionGroup m) * a i = a m) : ∃ j : ZMod (2 * m), a j * a j = a i := by
  rw [a_mul_a, a.injEq] at hi
  have h4 : 4 ∣ 2 * m := hm.trans (dvd_mul_left m 2)
  set ρ := ZMod.castHom h4 (ZMod 4)
  have hρ : ρ i + ρ i = 0 := by
    rw [← map_add, hi, map_natCast, (ZMod.natCast_eq_zero_iff m 4).mpr hm]
  have hval : (ρ i).val = i.val % 4 := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have hcases : ∀ x : ZMod 4, x + x = 0 → x.val = 0 ∨ x.val = 2 := by decide
  have heven : i.val % 2 = 0 := by
    rcases hcases _ hρ with h | h <;> omega
  refine ⟨((i.val / 2 : ℕ) : ZMod (2 * m)), ?_⟩
  rw [a_mul_a, ← Nat.cast_add, show i.val / 2 + i.val / 2 = i.val by omega,
    ZMod.natCast_zmod_val]

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
