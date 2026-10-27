module

public import CFSG.Certificates.Kernel.PackPermSound
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KModel
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup CFSG.KC.PackPerm CFSG.CGT.T75JM

private theorem permOf_toList (d : ℕ) (t : Array ℕ) :
    (CFSG.KS.PK.permOf d fun x => t.toList.getD x x) = tperm d t := by
  unfold tperm
  congr 1
  funext x
  simp [List.getD, Array.getD_eq_getD_getElem?]

private theorem evalG_sW {H : Type*} [Group H] (g h : H) (k : ℕ) :
    evalG g h (KData.sW k) = (g * h) ^ k := by
  rw [KData.sW, evalG_flatten_replicate]
  simp [evalG]

private theorem mem_center_of_gens {G : Type*} [Group G] {x y z : G}
    (hg : closure ({x, y} : Set G) = ⊤) (hx : x * z = z * x) (hy : y * z = z * y) :
    z ∈ center G := by
  have hle : closure ({x, y} : Set G) ≤ centralizer {z} := by
    rw [closure_le]
    rintro w (rfl | rfl) <;>
      simp only [SetLike.mem_coe, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exacts [hx.symm, hy.symm]
  rw [hg] at hle
  exact mem_center_iff.2 fun g => (mem_centralizer_iff.1 (hle (mem_top g)) z rfl).symm

theorem model3_facts_of_rel
    (h : relCheck 18 KData.m3aT.toList KData.m3bT.toList
      [(KData.sW 15, []), (0 :: KData.sW 5, KData.sW 5 ++ [0]),
        (1 :: KData.sW 5, KData.sW 5 ++ [1]), ([0, 0], []), ([1, 1, 1, 1], []),
        ((List.replicate 5 [0, 1, 1]).flatten, [])]
      [KData.sW 3, KData.sW 5] = true) :
    orderOf s3 = 15 ∧ a3 ^ 2 = 1 ∧ b3 ^ 4 = 1 ∧ (a3 * b3 * b3) ^ 5 = 1 ∧ c3 ∈ center model3 := by
  obtain ⟨he, hn⟩ := relCheck_sound h
  have e0 : tperm 18 KData.m3aT = perm3a := rfl
  have e1 : tperm 18 KData.m3bT = perm3b := rfl
  simp only [permOf_toList, e0, e1] at he hn
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he hn
  obtain ⟨h15, hca, hcb, ha, hb, hab⟩ := he
  obtain ⟨h3, h5⟩ := hn
  simp only [evalG_sW, evalG, evalG_append, evalG_flatten_replicate] at h15 hca hcb ha hb hab h3 h5
  simp only [if_true, one_ne_zero, if_false, mul_one] at hca hcb ha hb hab
  have hs : ∀ n : ℕ, ((s3 ^ n : model3) : Equiv.Perm (Fin 18)) = (perm3a * perm3b) ^ n :=
    fun n => Subgroup.coe_pow _ _ n
  have hne : ∀ n : ℕ, (perm3a * perm3b) ^ n ≠ 1 → s3 ^ n ≠ 1 :=
    fun n hn he => hn ((hs n).symm.trans (congrArg Subtype.val he))
  have hc : ((c3 : model3) : Equiv.Perm (Fin 18)) = (perm3a * perm3b) ^ 5 := hs 5
  refine ⟨orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (Subtype.ext ((hs 15).trans h15))
      fun p hp hpd => ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, ?_⟩
  · have hpd' : p ∣ 3 * 5 := hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd' with hp3 | hp5
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hp3]
      exact hne 5 h5
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hp5]
      exact hne 3 h3
  · rw [Subgroup.coe_pow, pow_two]
    exact ha
  · rw [Subgroup.coe_pow]
    simpa [pow_succ, mul_assoc, a3, b3] using hb
  · rw [Subgroup.coe_pow]
    simpa [mul_assoc, a3, b3] using hab
  · refine mem_center_of_gens closure_gens3 (Subtype.ext ?_) (Subtype.ext ?_) <;>
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exacts [hca, hcb]

theorem model6_facts_of_rel
    (h : relCheck 162 KData.m6aT.toList KData.m6bT.toList
      [(KData.sW 30, []), (0 :: KData.sW 5, KData.sW 5 ++ [0]),
        (1 :: KData.sW 5, KData.sW 5 ++ [1]), ([0, 0], KData.sW 15),
        ([1, 1, 1, 1], KData.sW 15), ((List.replicate 5 [0, 1, 1]).flatten, [])]
      [KData.sW 15, KData.sW 10, KData.sW 6] = true) :
    orderOf s6 = 30 ∧ a6 ^ 2 = c6 ^ 3 ∧ b6 ^ 4 = c6 ^ 3 ∧ (a6 * b6 * b6) ^ 5 = 1 ∧
      c6 ∈ center model6 := by
  obtain ⟨he, hn⟩ := relCheck_sound h
  have e0 : tperm 162 KData.m6aT = perm6a := rfl
  have e1 : tperm 162 KData.m6bT = perm6b := rfl
  simp only [permOf_toList, e0, e1] at he hn
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he hn
  obtain ⟨h30, hca, hcb, ha, hb, hab⟩ := he
  obtain ⟨h15, h10, h6⟩ := hn
  simp only [evalG_sW, evalG, evalG_append, evalG_flatten_replicate] at h30 hca hcb ha hb hab h15 h10 h6
  simp only [if_true, one_ne_zero, if_false, mul_one] at hca hcb ha hb hab
  have hs : ∀ n : ℕ, ((s6 ^ n : model6) : Equiv.Perm (Fin 162)) = (perm6a * perm6b) ^ n :=
    fun n => Subgroup.coe_pow _ _ n
  have hne : ∀ n : ℕ, (perm6a * perm6b) ^ n ≠ 1 → s6 ^ n ≠ 1 :=
    fun n hn he => hn ((hs n).symm.trans (congrArg Subtype.val he))
  have hc : ((c6 : model6) : Equiv.Perm (Fin 162)) = (perm6a * perm6b) ^ 5 := hs 5
  have hc3 : ((c6 ^ 3 : model6) : Equiv.Perm (Fin 162)) = (perm6a * perm6b) ^ 15 := by
    rw [c6, ← pow_mul]
    exact hs 15
  refine ⟨orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (Subtype.ext ((hs 30).trans h30))
      fun p hp hpd => ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, ?_⟩
  · have hpd' : p ∣ 2 * 3 * 5 := hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd' with hp23 | hp5
    · rcases (Nat.Prime.dvd_mul hp).1 hp23 with hp2 | hp3
      · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2]
        exact hne 15 h15
      · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hp3]
        exact hne 10 h10
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hp5]
      exact hne 6 h6
  · rw [hc3, Subgroup.coe_pow, pow_two]
    exact ha
  · rw [hc3, Subgroup.coe_pow]
    simpa [pow_succ, mul_assoc, a6, b6] using hb
  · rw [Subgroup.coe_pow]
    simpa [mul_assoc, a6, b6] using hab
  · refine mem_center_of_gens closure_gens6 (Subtype.ext ?_) (Subtype.ext ?_) <;>
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exacts [hca, hcb]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

end
