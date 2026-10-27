module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesSums
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseVanishing

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalCompleteBase

variable {m M : ℕ} [NeZero m] {ζ : ℂ}

theorem neg_one_pow_val_add (hm : 2 ∣ m) (a b : ZMod m) :
    (-1 : ℂ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  have h₁ : (-1 : ℂ) ^ (a + b).val = (-1) ^ ((a + b).val % 2) := neg_one_pow_eq_pow_mod_two _
  have h₂ : (-1 : ℂ) ^ (a.val + b.val) = (-1) ^ ((a.val + b.val) % 2) :=
    neg_one_pow_eq_pow_mod_two _
  rw [h₁, ← pow_add, h₂, ZMod.val_add, Nat.mod_mod_of_dvd _ hm]

theorem neg_one_pow_val_neg (hm : 2 ∣ m) (a : ZMod m) :
    (-1 : ℂ) ^ (-a).val = (-1) ^ a.val := by
  have h := neg_one_pow_val_add hm (-a) a
  rw [neg_add_cancel, ZMod.val_zero, pow_zero] at h
  have hsq : ((-1 : ℂ) ^ a.val) * (-1) ^ a.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc (-1 : ℂ) ^ (-a).val = (-1) ^ (-a).val * ((-1) ^ a.val * (-1) ^ a.val) := by
        rw [hsq, mul_one]
    _ = ((-1) ^ (-a).val * (-1) ^ a.val) * (-1) ^ a.val := by ring
    _ = (-1) ^ a.val := by rw [← h, one_mul]

theorem pow_val_mul_half (hm : m = 2 * M) (hζ : IsPrimitiveRoot ζ m) (l : ZMod m) :
    ζ ^ (l.val * M) = (-1) ^ l.val := by
  rw [mul_comm, pow_mul, pow_half_eq_neg_one hζ hm]

omit [NeZero m] in
theorem not_dvd_of_mem_Ico {k : ℕ} (hk : k ∈ Finset.Ico 1 m) : ¬ m ∣ k := fun h => by
  obtain ⟨hk₁, hk₂⟩ := Finset.mem_Ico.mp hk
  have := Nat.le_of_dvd (by omega) h
  omega

theorem value_off_zero (hζ : IsPrimitiveRoot ζ m) {X : ℕ → ℂ} {f : ZMod m → ZMod m → ℂ}
    {val A₁ A₂ x₀ c₀ : ℂ} {k : ℕ} (hk : k ∈ Finset.Ico 1 m)
    (hX : ∀ j ∈ Finset.Ico 1 m, X j = x₀) (hf0 : f 0 0 = 0)
    (hf : ∀ i j, (i, j) ≠ (0, 0) → f i j = c₀)
    (hval : 2 * val = A₁ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j +
      A₂ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
        (∑ i : ZMod m, f i (0 - i) - ∑ i : ZMod m, f i (-(j : ZMod m) - i))) :
    2 * val = -(A₁ * x₀) + A₂ * c₀ := by
  have hk' := not_dvd_of_mem_Ico hk
  rw [Finset.sum_congr rfl fun j hj => by rw [hX j hj], ← Finset.sum_mul,
    sum_Ico_zpow_neg hζ hk', sum_second_row hζ hk' f, sum_pairs_off_zero hζ hk' c₀ f hf0 hf]
    at hval
  linear_combination hval

theorem value_middle (hm : m = 2 * M) (hM : 2 ≤ M) (hζ : IsPrimitiveRoot ζ m)
    {X : ℕ → ℂ} {f : ZMod m → ZMod m → ℂ} {val A₁ A₂ x₀ c₀ : ℂ} {k : ℕ}
    (hk : k ∈ Finset.Ico 1 m) (hX : ∀ j ∈ Finset.Ico 1 m, X j = x₀)
    (hf : ∀ i j, f i j =
      if (i, j) ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) then c₀ else 0)
    (hval : 2 * val = A₁ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j +
      A₂ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
        (∑ i : ZMod m, f i (0 - i) - ∑ i : ZMod m, f i (-(j : ZMod m) - i))) :
    2 * val = -(A₁ * x₀) - A₂ * c₀ * (1 + 2 * (-1) ^ k) := by
  have hk' := not_dvd_of_mem_Ico hk
  have hM0 : (M : ZMod m) ≠ 0 := natCast_half_ne_zero hm (by omega)
  set O : Finset (ZMod m × ZMod m) := {((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
    (0, (M : ZMod m))} with hO
  have hc : ∀ i j, f i j = if (i, j) ∈ O then c₀ else 0 := by
    intro i j
    have hmem : (i, j) ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ↔
        (i, j) ∈ O := by
      rw [orbit_middle hm, hO]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
        Finset.mem_singleton]
    by_cases h : (i, j) ∈ O
    · rw [hf, ite_eq_left (hmem.mpr h), ite_eq_left h]
    · rw [hf, ite_eq_right fun h' => h (hmem.mp h'), ite_eq_right h]
  have hMM : (M : ZMod m) + M = 0 := by
    have h := neg_natCast_sub_self hm
    linear_combination -h
  have hMval : (M : ZMod m).val = M := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hsum : ∑ p ∈ O, ζ ^ ((p.1 + p.2).val * k) = 1 + 2 * (-1) ^ k := by
    rw [hO, Finset.sum_insert (by simp [hM0]), Finset.sum_insert (by simp [hM0]),
      Finset.sum_singleton]
    simp only [hMM, add_zero, zero_add, ZMod.val_zero, zero_mul, pow_zero, hMval, pow_mul,
      pow_half_eq_neg_one hζ hm]
    ring
  rw [Finset.sum_congr rfl fun j hj => by rw [hX j hj], ← Finset.sum_mul,
    sum_Ico_zpow_neg hζ hk', sum_second_row hζ hk' f, sum_pairs_finset k O c₀ f hc, hsum]
    at hval
  linear_combination hval

theorem value_single {X : ℕ → ℂ} {f : ZMod m → ZMod m → ℂ} {val A₁ A₂ x₀ : ℂ} {k h : ℕ}
    (hh : h ∈ Finset.Ico 1 m) (hX : ∀ j ∈ Finset.Ico 1 m, X j = if j = h then x₀ else 0)
    (hf : ∀ i j, f i j = 0)
    (hval : 2 * val = A₁ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j +
      A₂ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
        (∑ i : ZMod m, f i (0 - i) - ∑ i : ZMod m, f i (-(j : ZMod m) - i))) :
    2 * val = A₁ * x₀ * ζ ^ (-((h : ℤ) * k)) := by
  rw [Finset.sum_eq_single h (fun j hj hne => by rw [hX j hj, ite_eq_right hne, mul_zero])
      (fun hn => absurd hh hn), hX h hh, ite_eq_left rfl,
    Finset.sum_eq_zero fun j _ => by simp only [hf, Finset.sum_const_zero, sub_self, mul_zero]]
    at hval
  linear_combination hval

theorem value_diag (hm : m = 2 * M) (hM : 2 ≤ M) (hζ : IsPrimitiveRoot ζ m)
    (hm2 : ∃ n, m = 2 ^ n) {X : ℕ → ℂ} {f : ZMod m → ZMod m → ℂ} {val A₁ A₂ x₀ c₀ : ℂ}
    {t : ℕ} {i₀ : ZMod m} (ht : t ∈ Finset.Ico 1 M)
    (hi₀ : i₀ = (t : ZMod m) ∨ i₀ = ((t + M : ℕ) : ZMod m))
    (hX : ∀ j ∈ Finset.Ico 1 m, X j = if j = m - 2 * t then x₀ else 0)
    (hf : ∀ i j, f i j = if (i, j) ∈ MulAction.orbit (dualGroup m) (i₀, i₀) then c₀ else 0)
    (hval : 2 * val = A₁ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j +
      A₂ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
        (∑ i : ZMod m, f i (0 - i) - ∑ i : ZMod m, f i (-(j : ZMod m) - i))) :
    2 * val = A₁ * x₀ - A₂ * c₀ * (1 + 2 * (-1) ^ t) := by
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_Ico.mp ht
  have hm2' : 2 ∣ m := ⟨M, hm⟩
  have hk' : ¬ m ∣ M := not_dvd_of_mem_Ico (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hMeven : Even M := by
    obtain ⟨n, hn⟩ := hm2
    rcases n with _ | _ | n
    · simp at hn
      omega
    · simp at hn
      omega
    · refine ⟨2 ^ n, ?_⟩
      rw [pow_succ, pow_succ] at hn
      omega
  have hi₀val : (-1 : ℂ) ^ i₀.val = (-1) ^ t := by
    rcases hi₀ with rfl | rfl
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), pow_add, hMeven.neg_one_pow, mul_one]
  have hi₀0 : i₀ ≠ 0 := by
    intro h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_zero] at h'
    rcases hi₀ with rfl | rfl
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at h'
      omega
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at h'
      omega
  have hne : -i₀ - i₀ ≠ i₀ := by
    obtain ⟨n, rfl⟩ := hm2
    exact neg_sub_self_ne hi₀0
  set O : Finset (ZMod m × ZMod m) := {(i₀, i₀), (i₀, -i₀ - i₀), (-i₀ - i₀, i₀)} with hO
  have hc : ∀ i j, f i j = if (i, j) ∈ O then c₀ else 0 := by
    intro i j
    have hmem : (i, j) ∈ MulAction.orbit (dualGroup m) (i₀, i₀) ↔ (i, j) ∈ O := by
      rw [mem_orbit_dualGroup_iff, mem_dualSix_iff, hO]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    by_cases h : (i, j) ∈ O
    · rw [hf, ite_eq_left (hmem.mpr h), ite_eq_left h]
    · rw [hf, ite_eq_right fun h' => h (hmem.mp h'), ite_eq_right h]
  have hsum : ∑ p ∈ O, ζ ^ ((p.1 + p.2).val * M) = 1 + 2 * (-1) ^ t := by
    have h₁ : (i₀, i₀) ∉ ({(i₀, -i₀ - i₀), (-i₀ - i₀, i₀)} : Finset (ZMod m × ZMod m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
      exact ⟨fun h => hne h.2.symm, fun h => hne h.1.symm⟩
    have h₂ : (i₀, -i₀ - i₀) ∉ ({(-i₀ - i₀, i₀)} : Finset (ZMod m × ZMod m)) := by
      simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
      exact fun h => absurd h.symm hne
    rw [hO, Finset.sum_insert h₁, Finset.sum_insert h₂, Finset.sum_singleton]
    simp only
    rw [show i₀ + (-i₀ - i₀) = -i₀ by ring, show -i₀ - i₀ + i₀ = -i₀ by ring,
      pow_val_mul_half hm hζ, pow_val_mul_half hm hζ, neg_one_pow_val_add hm2',
      neg_one_pow_val_neg hm2', hi₀val, ← pow_add, ← two_mul, pow_mul]
    norm_num
    ring
  have hj : m - 2 * t ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hroot : ζ ^ (-(((m - 2 * t : ℕ) : ℤ) * M)) = 1 := by
    refine (hζ.zpow_eq_one_iff_dvd _).mpr ⟨-((M : ℤ) - t), ?_⟩
    have hmZ : (m : ℤ) = 2 * M := by exact_mod_cast hm
    rw [Nat.cast_sub (by omega)]
    push_cast
    linear_combination (-(t : ℤ)) * hmZ
  rw [Finset.sum_eq_single (m - 2 * t) (fun j hj' hne' => by rw [hX j hj', ite_eq_right hne',
      mul_zero]) (fun hn => absurd hj hn), hX _ hj, ite_eq_left rfl, hroot,
    sum_second_row hζ hk' f, sum_pairs_finset M O c₀ f hc, hsum] at hval
  linear_combination hval

theorem value_six (hm : m = 2 * M) (hM : 2 ≤ M) (hζ : IsPrimitiveRoot ζ m)
    {X : ℕ → ℂ} {f : ZMod m → ZMod m → ℂ} {val A₁ A₂ c₀ : ℂ} {I : ZMod m × ZMod m}
    (hI : (MulAction.orbit (dualGroup m) I).ncard = 6) (hX : ∀ j ∈ Finset.Ico 1 m, X j = 0)
    (hf : ∀ i j, f i j = if (i, j) ∈ MulAction.orbit (dualGroup m) I then c₀ else 0)
    (hval : 2 * val = A₁ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j +
      A₂ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
        (∑ i : ZMod m, f i (0 - i) - ∑ i : ZMod m, f i (-(j : ZMod m) - i))) :
    2 * val =
      -(A₂ * c₀ * (2 * ((-1) ^ I.1.val + (-1) ^ I.2.val + (-1) ^ (I.1.val + I.2.val)))) := by
  have hm2 : 2 ∣ m := ⟨M, hm⟩
  have hk' : ¬ m ∣ M := not_dvd_of_mem_Ico (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hc : ∀ i j, f i j = if (i, j) ∈ (dualSix I).toFinset then c₀ else 0 := by
    intro i j
    by_cases h : (i, j) ∈ MulAction.orbit (dualGroup m) I
    · rw [hf, ite_eq_left h,
        ite_eq_left (List.mem_toFinset.mpr ((mem_orbit_dualGroup_iff I _).mp h))]
    · rw [hf, ite_eq_right h,
        ite_eq_right fun h' => h ((mem_orbit_dualGroup_iff I _).mpr (List.mem_toFinset.mp h'))]
  have hsum : ∑ p ∈ (dualSix I).toFinset, ζ ^ ((p.1 + p.2).val * M) =
      2 * ((-1) ^ I.1.val + (-1) ^ I.2.val + (-1) ^ (I.1.val + I.2.val)) := by
    have e₁ : I.2 + I.1 = I.1 + I.2 := add_comm _ _
    have e₂ : I.2 + (-I.1 - I.2) = -I.1 := by ring
    have e₃ : -I.1 - I.2 + I.1 = -I.2 := by ring
    have e₄ : I.1 + (-I.1 - I.2) = -I.2 := by ring
    have e₅ : -I.1 - I.2 + I.2 = -I.1 := by ring
    rw [List.sum_toFinset _ ((ncard_orbit_eq_six_iff I).mp hI)]
    simp only [dualSix, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [e₁, e₂, e₃, e₄, e₅]
    simp only [pow_val_mul_half hm hζ, neg_one_pow_val_neg hm2, neg_one_pow_val_add hm2, pow_add]
    ring
  rw [Finset.sum_eq_zero fun j hj => by rw [hX j hj, mul_zero], sum_second_row hζ hk' f,
    sum_pairs_finset M _ c₀ f hc, hsum] at hval
  linear_combination hval

end CFSG.Wreathed.ConditionalGlobalDegrees
