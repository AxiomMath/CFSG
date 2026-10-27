module

public import CFSG.CharacterTheory.Wreathed.CenterAndDihedralQuotient
public import CFSG.CharacterTheory.Wreathed.MaximalOrder

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem element_base_inv (m : ℕ) (a b : ZMod m) :
    (element m a b 0)⁻¹ = element m (-a) (-b) 0 := by
  apply inv_eq_of_mul_eq_one_right
  rw [element_base_mul]
  simp

theorem element_swap_inv (m : ℕ) (a b : ZMod m) :
    (element m a b 1)⁻¹ = element m (-b) (-a) 1 := by
  apply inv_eq_of_mul_eq_one_right
  rw [element_swap_mul]
  simp [show (1 + 1 : ZMod 2) = 0 by decide]

theorem two_smul_eq_zero_iff (k : ℕ) (c : ZMod (2 ^ (k + 1))) :
    2 • c = 0 ↔ c = 0 ∨ c = ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
  let : NeZero (2 ^ (k + 1)) := ⟨pow_ne_zero _ (by decide)⟩
  have hpos := pow_pos (by decide : 0 < (2 : ℕ)) k
  have hlt := ZMod.val_lt c
  have heq : 2 • c = ((2 * c.val : ℕ) : ZMod (2 ^ (k + 1))) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  rw [heq, ZMod.natCast_eq_zero_iff]
  have hdiv (t : ℕ) : 2 ^ (k + 1) ∣ 2 * t ↔ 2 ^ k ∣ t := by
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, Nat.mul_comm],
      Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))]
  rw [hdiv c.val]
  constructor
  · intro h
    have hval : c.val = 0 ∨ c.val = 2 ^ k := by
      obtain ⟨a, ha⟩ := h
      have hbound : a < 2 := by
        rw [ha, pow_succ] at hlt
        nlinarith
      have ha01 : a = 0 ∨ a = 1 := by omega
      rcases ha01 with rfl | rfl <;> simp_all
    rcases hval with h | h
    · left
      apply ZMod.val_injective (2 ^ (k + 1))
      simpa only [ZMod.val_zero] using h
    · right
      apply ZMod.val_injective (2 ^ (k + 1))
      rw [ZMod.val_natCast_of_lt (by rw [pow_succ]; omega)]
      exact h
  · rintro (rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by rw [pow_succ]; omega)]

theorem half_residue_ne_zero (k : ℕ) :
    ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by rw [pow_succ]; have hp := pow_pos (by decide : 0 < (2 : ℕ)) k; omega),
    ZMod.val_zero] at hv
  exact (pow_ne_zero k (by decide : (2 : ℕ) ≠ 0)) hv

theorem element_base_involution_iff (k : ℕ) (a b : ZMod (2 ^ (k + 1))) :
    orderOf (element (2 ^ (k + 1)) a b 0) = 2 ↔
      (a = (2 ^ k : ℕ) ∧ b = (2 ^ k : ℕ)) ∨
      (a = (2 ^ k : ℕ) ∧ b = 0) ∨
      (a = 0 ∧ b = (2 ^ k : ℕ)) := by
  rw [orderOf_eq_prime_iff, element_base_pow, element_base_eq_one_iff,
    two_smul_eq_zero_iff, two_smul_eq_zero_iff]
  have hne := half_residue_ne_zero k
  rw [ne_eq, element_base_eq_one_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hn⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp only [hne, not_false_eq_true, and_false, true_or, or_true,
        and_self, eq_self, and_true]

theorem element_swap_involution_iff (m : ℕ) (a b : ZMod m) :
    orderOf (element m a b 1) = 2 ↔ a + b = 0 := by
  have hne : element m a b 1 ≠ 1 := by
    intro h
    have hr := congrArg (fun g : Wreath m => Multiplicative.toAdd g.right) h
    change (1 : ZMod 2) = 0 at hr
    exact one_ne_zero hr
  rw [orderOf_eq_prime_iff, element_swap_sq, element_base_eq_one_iff]
  simp only [and_self]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, hne⟩

theorem conjugate_base_by_base (m : ℕ) (a b c d : ZMod m) :
    element m c d 0 * element m a b 0 * (element m c d 0)⁻¹ = element m a b 0 := by
  rw [element_base_inv, element_base_mul, element_base_mul]
  congr 1 <;> abel

theorem conjugate_base_by_swap (m : ℕ) (a b c d : ZMod m) :
    element m c d 1 * element m a b 0 * (element m c d 1)⁻¹ = element m b a 0 := by
  rw [element_swap_inv, element_swap_mul, add_zero, element_swap_mul]
  rw [show (1 + 1 : ZMod 2) = 0 by decide]
  congr 1 <;> abel

theorem conjugate_swap_by_base (m : ℕ) (a b c d : ZMod m) :
    element m c d 0 * element m a b 1 * (element m c d 0)⁻¹ =
      element m (a + c - d) (b + d - c) 1 := by
  rw [element_base_inv, element_base_mul, element_swap_mul, add_zero]
  congr 1 <;> abel

theorem conjugate_swap_by_swap (m : ℕ) (a b c d : ZMod m) :
    element m c d 1 * element m a b 1 * (element m c d 1)⁻¹ =
      element m (b + c - d) (a + d - c) 1 := by
  rw [element_swap_inv, element_swap_mul,
    show (1 + 1 : ZMod 2) = 0 by decide, element_base_mul]
  congr 1 <;> abel

@[simp] theorem element_eq_iff (m : ℕ) (a b c d : ZMod m) (e f : ZMod 2) :
    element m a b e = element m c d f ↔ a = c ∧ b = d ∧ e = f := by
  constructor
  · intro h
    have hc := congrArg (coordinateEquiv m) h
    change (a, b, e) = (c, d, f) at hc
    simpa only [Prod.mk.injEq] using hc
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem base_conjugacy_iff (m : ℕ) (a b : ZMod m) (g : Wreath m) :
    IsConj (element m a b 0) g ↔ g = element m a b 0 ∨ g = element m b a 0 := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨⟨u, v, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective c
    change element m u v e * element m a b 0 * (element m u v e)⁻¹ = g at hc
    rcases swap_exponent_cases e with rfl | rfl
    · left
      rw [conjugate_base_by_base] at hc
      exact hc.symm
    · right
      rw [conjugate_base_by_swap] at hc
      exact hc.symm
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨element m 0 0 1, conjugate_base_by_swap m a b 0 0⟩

theorem outside_involution_conjugate (m : ℕ) (a : ZMod m) :
    IsConj (element m 0 0 1) (element m a (-a) 1) := by
  rw [isConj_iff]
  refine ⟨element m a 0 0, ?_⟩
  rw [conjugate_swap_by_base]
  simp

theorem swap_conjugacy_iff (m : ℕ) (g : Wreath m) :
    IsConj (element m 0 0 1) g ↔ ∃ a : ZMod m, g = element m a (-a) 1 := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective c
    change element m a b e * element m 0 0 1 * (element m a b e)⁻¹ = g at hc
    rcases swap_exponent_cases e with rfl | rfl
    · rw [conjugate_swap_by_base] at hc
      refine ⟨a - b, ?_⟩
      rw [← hc]
      simp only [element_eq_iff]
      constructor
      · abel
      · constructor
        · abel
        · trivial
    · rw [conjugate_swap_by_swap] at hc
      refine ⟨a - b, ?_⟩
      rw [← hc]
      simp only [element_eq_iff]
      constructor
      · abel
      · constructor
        · abel
        · trivial
  · rintro ⟨a, rfl⟩
    exact isConj_iff.mp (outside_involution_conjugate m a)

theorem three_representatives_pairwise_not_conjugate (k : ℕ) :
    ¬IsConj (element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0)
      (element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0) ∧
    ¬IsConj (element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0)
      (element (2 ^ (k + 1)) 0 0 1) ∧
    ¬IsConj (element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0)
      (element (2 ^ (k + 1)) 0 0 1) := by
  have hn := half_residue_ne_zero k
  simp only [base_conjugacy_iff, element_eq_iff, eq_self, one_ne_zero,
    Ne.symm hn, and_false, false_or, not_false_eq_true, and_true]

theorem unique_central_involution (k : ℕ) (g : Wreath (2 ^ (k + 1)))
    (hg : orderOf g = 2) (hz : g ∈ Subgroup.center (Wreath (2 ^ (k + 1)))) :
    g = element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0 := by
  have hm : 1 < 2 ^ (k + 1) := by
    rw [pow_succ]
    have hp := pow_pos (by decide : 0 < (2 : ℕ)) k
    omega
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective g
  change element (2 ^ (k + 1)) a b e ∈ Subgroup.center _ at hz
  rcases (element_mem_center_iff _ hm a b e).mp hz with ⟨rfl, rfl⟩
  change orderOf (element (2 ^ (k + 1)) a a 0) = 2 at hg
  have hne := half_residue_ne_zero k
  rcases (element_base_involution_iff k a a).mp hg with h | h | h
  · rw [h.1]
    rfl
  · exact False.elim (hne (h.1.symm.trans h.2))
  · exact False.elim (hne (h.2.symm.trans h.1))

theorem involution_three_classes (k : ℕ) (g : Wreath (2 ^ (k + 1)))
    (hg : orderOf g = 2) :
    IsConj (element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0) g ∨
    IsConj (element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0) g ∨
    IsConj (element (2 ^ (k + 1)) 0 0 1) g := by
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective g
  change orderOf (element (2 ^ (k + 1)) a b e) = 2 at hg
  change IsConj _ (element (2 ^ (k + 1)) a b e) ∨
    IsConj _ (element (2 ^ (k + 1)) a b e) ∨ IsConj _ (element (2 ^ (k + 1)) a b e)
  rcases swap_exponent_cases e with rfl | rfl
  · rcases (element_base_involution_iff k a b).mp hg with h | h | h
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inl (IsConj.refl _)
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl (IsConj.refl _))
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl ((base_conjugacy_iff _ _ _ _).mpr (Or.inr rfl)))
  · have hb : b = -a := by
      have hsum := (element_swap_involution_iff _ a b).mp hg
      linear_combination hsum
    subst b
    exact Or.inr (Or.inr (outside_involution_conjugate _ a))

end CFSG.Wreathed
