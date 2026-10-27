module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseOrbits
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Basic.Complex.Basic

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalGeneralBase

theorem base_column_orbit_invariant {m : ℕ} {β : Type*} (c : ZMod m → ZMod m → β)
    (hsym : ∀ i j, c i j = c j i ∧ c i j = c j (-i - j)) {I J : ZMod m × ZMod m}
    (hJ : J ∈ MulAction.orbit (dualGroup m) I) : c J.1 J.2 = c I.1 I.2 := by
  have hswap : ∀ K : ZMod m × ZMod m, c (dualSwap m K).1 (dualSwap m K).2 = c K.1 K.2 :=
    fun K => (hsym K.1 K.2).1.symm
  have hrot : ∀ K : ZMod m × ZMod m, c (dualRotation m K).1 (dualRotation m K).2 = c K.1 K.2 :=
    fun K => (hsym K.1 K.2).2.symm
  have key : ∀ g ∈ dualGroup m, ∀ K : ZMod m × ZMod m, c (g K).1 (g K).2 = c K.1 K.2 := by
    intro g hg
    induction hg using Subgroup.closure_induction'' with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hswap
      · exact hrot
    | inv_mem x hx =>
      rcases hx with rfl | rfl
      · rw [dualSwap_inv]
        exact hswap
      · intro K
        rw [dualRotation_inv, Equiv.Perm.mul_apply, hrot, hrot]
    | one => exact fun K => rfl
    | mul x y _ _ hx hy => exact fun K => by rw [Equiv.Perm.mul_apply, hx, hy]
  obtain ⟨g, rfl⟩ := hJ
  exact key g.1 g.2 I

theorem neg_natCast_sub_self {m M : ℕ} (hm : m = 2 * M) : -(M : ZMod m) - M = 0 := by
  have h : ((2 * M : ℕ) : ZMod m) = 0 := by
    rw [← hm]
    exact ZMod.natCast_self m
  push_cast at h
  linear_combination -h

theorem orbit_middle {m M : ℕ} (hm : m = 2 * M) :
    MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) =
      {((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0), (0, (M : ZMod m))} := by
  have h := neg_natCast_sub_self hm
  ext J
  rw [mem_orbit_dualGroup_iff, mem_dualSix_iff]
  simp only [h, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem natCast_half_ne_zero {m M : ℕ} (hm : m = 2 * M) (hM : 0 < M) : (M : ZMod m) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd hM h
  omega

theorem sum_antidiagonal_off_middle {m M : ℕ} [NeZero m] (hm : m = 2 * M) (hM : 0 < M) (ξ : ℂ)
    (f : ZMod m → ZMod m → ℂ)
    (hf0 : ∀ i j, (i, j) ∈ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
      (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) → f i j = 0)
    (hf1 : ∀ i j, (i, j) ∉ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
      (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) → f i j = ξ) (l : ZMod m) :
    ∑ i : ZMod m, f i (l - i) = if l = 0 ∨ l = (M : ZMod m) then ((m : ℂ) - 2) * ξ else m * ξ := by
  have hMne := natCast_half_ne_zero hm hM
  have hneg : -(M : ZMod m) = M := by
    have h := neg_natCast_sub_self hm
    linear_combination h
  have h2M : (M : ZMod m) + M = 0 := by
    have h := neg_natCast_sub_self hm
    linear_combination -h
  have hmem : ∀ i : ZMod m, (i, l - i) ∈ ({(0, 0), ((M : ZMod m), (M : ZMod m)),
      ((M : ZMod m), 0), (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) ↔
      (l = 0 ∨ l = (M : ZMod m)) ∧ (i = 0 ∨ i = (M : ZMod m)) := by
    intro i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact ⟨Or.inl (by simpa using h), Or.inl rfl⟩
      · refine ⟨Or.inl ?_, Or.inr rfl⟩
        rw [sub_eq_iff_eq_add, h2M] at h
        exact h
      · exact ⟨Or.inr (sub_eq_zero.mp h), Or.inr rfl⟩
      · exact ⟨Or.inr (by simpa using h), Or.inl rfl⟩
    · rintro ⟨rfl | rfl, rfl | rfl⟩
      · exact Or.inl ⟨rfl, sub_zero 0⟩
      · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
        rw [zero_sub, hneg]
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, sub_zero _⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, sub_self _⟩))
  have hterm : ∀ i : ZMod m, f i (l - i) =
      ξ - if i ∈ ({0, (M : ZMod m)} : Finset (ZMod m)) ∧ (l = 0 ∨ l = (M : ZMod m)) then ξ
        else 0 := by
    intro i
    have hi : i ∈ ({0, (M : ZMod m)} : Finset (ZMod m)) ↔ i = 0 ∨ i = (M : ZMod m) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h : (i, l - i) ∈ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
        (0, (M : ZMod m))} : Set (ZMod m × ZMod m))
    · have h' := (hmem i).mp h
      rw [hf0 i (l - i) h, ite_eq_left ⟨hi.mpr h'.2, h'.1⟩, sub_self]
    · rw [hf1 i (l - i) h, ite_eq_right (fun h' => h ((hmem i).mpr ⟨h'.2, hi.mp h'.1⟩)), sub_zero]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  by_cases hl : l = 0 ∨ l = (M : ZMod m)
  · rw [ite_eq_left hl]
    have hsum : ∑ i : ZMod m, (if i ∈ ({0, (M : ZMod m)} : Finset (ZMod m)) ∧
        (l = 0 ∨ l = (M : ZMod m)) then ξ else 0) = 2 * ξ := by
      rw [Finset.sum_congr rfl fun i _ => if_congr (and_iff_left hl) rfl rfl, Finset.sum_ite_mem,
        Finset.univ_inter, Finset.sum_const, Finset.card_pair hMne.symm, nsmul_eq_mul]
      norm_num
    rw [hsum]
    ring
  · rw [ite_eq_right hl, Finset.sum_eq_zero fun i _ => ite_eq_right fun h => hl h.2, sub_zero]

theorem natCast_eq_half_iff {m M : ℕ} (hm : m = 2 * M) {j : ℕ} (hj : j < m) :
    (j : ZMod m) = (M : ZMod m) ↔ j = M := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega)]

theorem antidiagonal_difference {m M : ℕ} [NeZero m] (hm : m = 2 * M) (hM : 0 < M) (ξ : ℂ)
    (f : ZMod m → ZMod m → ℂ)
    (hf0 : ∀ i j, (i, j) ∈ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
      (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) → f i j = 0)
    (hf1 : ∀ i j, (i, j) ∉ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
      (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) → f i j = ξ)
    (Cl : ZMod m → ℂ) (hCl : ∀ l, Cl l = ∑ i : ZMod m, f i (l - i)) :
    ∀ j ∈ Finset.Ico 1 m, Cl 0 - Cl (-(j : ZMod m)) = if j = M then 0 else -2 * ξ := by
  intro j hj
  rw [Finset.mem_Ico] at hj
  have hneg : -(M : ZMod m) = M := by
    have h := neg_natCast_sub_self hm
    linear_combination h
  have hj0 : -(j : ZMod m) ≠ 0 := by
    rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hjM : -(j : ZMod m) = (M : ZMod m) ↔ j = M := by
    rw [neg_eq_iff_eq_neg, hneg]
    exact natCast_eq_half_iff hm hj.2
  rw [hCl, hCl, sum_antidiagonal_off_middle hm hM ξ f hf0 hf1,
    sum_antidiagonal_off_middle hm hM ξ f hf0 hf1, ite_eq_left (Or.inl rfl)]
  by_cases h : j = M
  · rw [ite_eq_left (Or.inr (hjM.mpr h)), ite_eq_left h, sub_self]
  · rw [ite_eq_right fun h' => h'.elim hj0 fun h'' => h (hjM.mp h''), ite_eq_right h]
    ring

theorem row_value_eq_zero {m M : ℕ} (hm : m = 2 * M) (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (X D : ℕ → ℂ) {val A₁ A₂ κ' : ℂ}
    (hval : 2 * val = A₁ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * 1)) * X j +
      A₂ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * 1)) * D j)
    (hX : ∀ j ∈ Finset.Ico 1 m, X j = 0)
    (hD : ∀ j ∈ Finset.Ico 1 m, D j = if j = M then 0 else κ') : val = 0 := by
  have hpow : ∀ j : ℕ, ζ ^ (-((j : ℤ) * 1)) = ζ⁻¹ ^ j := fun j => by
    rw [mul_one, zpow_neg, zpow_natCast, inv_pow]
  have hgeom : ∑ j ∈ Finset.Ico 1 m, ζ⁻¹ ^ j = -1 := by
    rw [Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ m), hζ.inv.geom_sum_eq_zero (by omega),
      Finset.sum_range_one, pow_zero, zero_sub]
  have hhalf : ζ⁻¹ ^ M = -1 := by
    have hsq : ζ ^ M * ζ ^ M = 1 := by
      rw [← pow_add, show M + M = m by omega, hζ.pow_eq_one]
    have hne : ζ ^ M ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hM.ne' (by omega)
    have hM1 : ζ ^ M = -1 := (mul_self_eq_one_iff.mp hsq).resolve_left hne
    rw [inv_pow, hM1, inv_neg, inv_one]
  have hXsum : ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * 1)) * X j = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hX j hj, mul_zero]
  have hDsum : ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * 1)) * D j = 0 := by
    have hMmem : M ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨hM, by omega⟩
    have hterm : ∀ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * 1)) * D j =
        ζ⁻¹ ^ j * κ' - if j = M then ζ⁻¹ ^ j * κ' else 0 := by
      intro j hj
      rw [hD j hj, hpow]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hgeom,
      Finset.sum_ite_eq' (Finset.Ico 1 m) M, ite_eq_left hMmem, hhalf]
    ring
  rw [hXsum, hDsum, mul_zero, mul_zero, add_zero] at hval
  exact (mul_eq_zero.mp hval).resolve_left two_ne_zero

end CFSG.Wreathed.ConditionalCompleteBase
