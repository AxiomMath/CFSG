module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseOrbits
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsAlgebra
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalFourier

variable {m : ℕ} [NeZero m] {ζ : ℂ}

theorem zpow_eq_of_modEq (hζ : IsPrimitiveRoot ζ m) {a b : ℤ} (h : a ≡ b [ZMOD m]) :
    ζ ^ a = ζ ^ b := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  have h1 : ζ ^ (a - b) = 1 := (hζ.zpow_eq_one_iff_dvd _).mpr (Int.ModEq.dvd h.symm)
  calc ζ ^ a = ζ ^ (a - b + b) := by rw [sub_add_cancel]
    _ = ζ ^ (a - b) * ζ ^ b := zpow_add₀ hζ0 _ _
    _ = ζ ^ b := by rw [h1, one_mul]

theorem zpow_neg_mul_eq (hζ : IsPrimitiveRoot ζ m) (j k : ℕ) :
    ζ ^ (-((j : ℤ) * k)) = ζ ^ ((-(j : ZMod m)).val * k) := by
  have hmod : ((((-(j : ZMod m)).val : ℕ) : ℤ) * k) ≡ -((j : ℤ) * k) [ZMOD m] := by
    have h : ((((-(j : ZMod m)).val : ℕ) : ℤ) : ZMod m) = ((-(j : ℤ) : ℤ) : ZMod m) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    have h' := (ZMod.intCast_eq_intCast_iff _ _ _).mp h
    rw [neg_mul_eq_neg_mul]
    exact h'.mul_right _
  rw [zpow_eq_of_modEq hζ hmod.symm, ← zpow_natCast]
  push_cast
  rfl

theorem sum_zmod_pow_eq_zero (hζ : IsPrimitiveRoot ζ m) {k : ℕ} (hk : ¬ m ∣ k) :
    ∑ l : ZMod m, ζ ^ (l.val * k) = 0 := by
  have himg : (Finset.univ : Finset (ZMod m)).image ZMod.val = Finset.range m := by
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨l, rfl⟩
      exact ZMod.val_lt l
    · intro ht
      exact ⟨(t : ZMod m), ZMod.val_cast_of_lt ht⟩
  have hsum : ∑ l : ZMod m, ζ ^ (l.val * k) = ∑ t ∈ Finset.range m, (ζ ^ k) ^ t := by
    rw [← himg, Finset.sum_image fun a _ b _ h => ZMod.val_injective m h]
    exact Finset.sum_congr rfl fun l _ => by rw [← pow_mul, mul_comm]
  rw [hsum]
  refine sum_range_pow_eq_zero ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · intro h
    exact hk ((hζ.pow_eq_one_iff_dvd k).mp h)

theorem sum_Ico_neg_cast (g : ZMod m → ℂ) :
    ∑ j ∈ Finset.Ico 1 m, g (-(j : ZMod m)) = ∑ l : ZMod m, g l - g 0 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 : ∑ j ∈ Finset.range m, g (-(j : ZMod m)) = ∑ l : ZMod m, g l := by
    refine Finset.sum_nbij (fun j => -(j : ZMod m)) (fun _ _ => Finset.mem_univ _) ?_ ?_
      fun _ _ => rfl
    · intro a ha b hb h
      have h' : (a : ZMod m) = (b : ZMod m) := neg_inj.mp h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] at h'
      exact h'
    · intro l _
      refine ⟨(-l).val, Finset.mem_coe.mpr (Finset.mem_range.mpr (ZMod.val_lt _)), ?_⟩
      simp only
      rw [ZMod.natCast_zmod_val, neg_neg]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm] at h1
  simp only [Nat.cast_zero, neg_zero] at h1
  rw [← h1]
  ring

theorem sum_Ico_zpow_neg (hζ : IsPrimitiveRoot ζ m) {k : ℕ} (hk : ¬ m ∣ k) :
    ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) = -1 := by
  rw [Finset.sum_congr rfl fun j _ => zpow_neg_mul_eq hζ j k,
    sum_Ico_neg_cast (fun l => ζ ^ (l.val * k)), sum_zmod_pow_eq_zero hζ hk]
  simp

theorem sum_second_row (hζ : IsPrimitiveRoot ζ m) {k : ℕ} (hk : ¬ m ∣ k)
    (c : ZMod m → ZMod m → ℂ) :
    ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
      (∑ i : ZMod m, c i (0 - i) - ∑ i : ZMod m, c i (-(j : ZMod m) - i)) =
    -∑ i : ZMod m, ∑ j : ZMod m, ζ ^ ((i + j).val * k) * c i j := by
  set Cl : ZMod m → ℂ := fun l => ∑ i : ZMod m, c i (l - i) with hCl
  have hsplit : ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
      (∑ i : ZMod m, c i (0 - i) - ∑ i : ZMod m, c i (-(j : ZMod m) - i)) =
      (∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k))) * Cl 0 -
        ∑ j ∈ Finset.Ico 1 m, ζ ^ ((-(j : ZMod m)).val * k) * Cl (-(j : ZMod m)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zpow_neg_mul_eq hζ j k]
    simp only [hCl]
    ring
  have hfull : ∑ l : ZMod m, ζ ^ (l.val * k) * Cl l =
      ∑ i : ZMod m, ∑ j : ZMod m, ζ ^ ((i + j).val * k) * c i j := by
    simp only [hCl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_equiv (Equiv.addLeft i) _ _ fun j => by
      simp only [Equiv.coe_addLeft, add_sub_cancel_left]).symm
  rw [hsplit, sum_Ico_zpow_neg hζ hk,
    sum_Ico_neg_cast (fun l => ζ ^ (l.val * k) * Cl l), ← hfull]
  simp only [ZMod.val_zero, zero_mul, pow_zero, one_mul]
  ring

theorem sum_pairs_off_zero (hζ : IsPrimitiveRoot ζ m) {k : ℕ} (hk : ¬ m ∣ k) (c₀ : ℂ)
    (c : ZMod m → ZMod m → ℂ) (h0 : c 0 0 = 0) (hc : ∀ i j, (i, j) ≠ (0, 0) → c i j = c₀) :
    ∑ i : ZMod m, ∑ j : ZMod m, ζ ^ ((i + j).val * k) * c i j = -c₀ := by
  have hconst : ∑ i : ZMod m, ∑ j : ZMod m, ζ ^ ((i + j).val * k) * c₀ = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_mul, Fintype.sum_equiv (Equiv.addLeft i) (fun j => ζ ^ ((i + j).val * k))
      (fun l => ζ ^ (l.val * k)) fun j => rfl, sum_zmod_pow_eq_zero hζ hk, zero_mul]
  have hdiff : ∑ i : ZMod m, ∑ j : ZMod m, ζ ^ ((i + j).val * k) * (c₀ - c i j) = c₀ := by
    rw [Finset.sum_eq_single (0 : ZMod m) (fun i _ hi => Finset.sum_eq_zero fun j _ => by
        rw [hc i j fun h => hi (Prod.ext_iff.mp h).1, sub_self, mul_zero])
      fun h => absurd (Finset.mem_univ _) h,
      Finset.sum_eq_single (0 : ZMod m) (fun j _ hj => by
        rw [hc 0 j fun h => hj (Prod.ext_iff.mp h).2, sub_self, mul_zero])
      fun h => absurd (Finset.mem_univ _) h, h0]
    simp
  have h := congrArg₂ (· - ·) hconst hdiff
  simp only [← Finset.sum_sub_distrib, mul_sub, sub_sub_cancel] at h
  rw [h]
  ring

theorem sum_pairs_finset (k : ℕ) (O : Finset (ZMod m × ZMod m)) (c₀ : ℂ)
    (c : ZMod m → ZMod m → ℂ) (hc : ∀ i j, c i j = if (i, j) ∈ O then c₀ else 0) :
    ∑ i : ZMod m, ∑ j : ZMod m, ζ ^ ((i + j).val * k) * c i j =
      c₀ * ∑ p ∈ O, ζ ^ ((p.1 + p.2).val * k) := by
  rw [← Fintype.sum_prod_type' (fun i j => ζ ^ ((i + j).val * k) * c i j)]
  simp only [hc, mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem pow_half_eq_neg_one (hζ : IsPrimitiveRoot ζ m) {M : ℕ} (hm : m = 2 * M) :
    ζ ^ M = -1 := by
  have hM : 0 < M := by
    have := Nat.pos_of_ne_zero (NeZero.ne m)
    omega
  have hsq : (ζ ^ M) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← hm, hζ.pow_eq_one]
  have hne : ζ ^ M ≠ 1 := fun h => by
    have := Nat.le_of_dvd hM ((hζ.pow_eq_one_iff_dvd M).mp h)
    omega
  have hsq' : ζ ^ M * ζ ^ M = 1 := by rw [← sq]; exact hsq
  rcases mul_self_eq_one_iff.mp hsq' with h | h
  · exact absurd h hne
  · exact h

end CFSG.Wreathed.ConditionalGlobalDegrees
