module

public import Mathlib

public noncomputable section

namespace CFSG.Blueprint.Chevalley

variable {R : Type*} [CommRing R]

@[expose] def binomX (m : ℕ) (c : R) : Module.End R (Fin (m + 1) →₀ R) :=
  Finsupp.linearCombination R fun j : Fin (m + 1) =>
    ∑ k : Fin (m - j + 1), ((((j : ℕ) + k).choose k : R) * c ^ (k : ℕ)) •
      Finsupp.single (⟨j + k, by omega⟩ : Fin (m + 1)) 1

@[expose] def binomY (m : ℕ) (c : R) : Module.End R (Fin (m + 1) →₀ R) :=
  Finsupp.linearCombination R fun j : Fin (m + 1) =>
    ∑ k : Fin (j + 1), ((((m - j : ℕ) + k).choose k : R) * c ^ (k : ℕ)) •
      Finsupp.single (⟨j - k, by omega⟩ : Fin (m + 1)) 1

@[expose] def binomN (m : ℕ) (t : Rˣ) : Module.End R (Fin (m + 1) →₀ R) :=
  binomX m (t : R) * binomY m (-((t⁻¹ : Rˣ) : R)) * binomX m (t : R)

variable {m : ℕ}

theorem binomX_single (c : R) (j : Fin (m + 1)) :
    binomX m c (Finsupp.single j 1) =
      ∑ k : Fin (m - j + 1), ((((j : ℕ) + k).choose k : R) * c ^ (k : ℕ)) •
        Finsupp.single (⟨j + k, by omega⟩ : Fin (m + 1)) 1 := by
  rw [binomX, Finsupp.linearCombination_single, one_smul]

theorem binomY_single (c : R) (j : Fin (m + 1)) :
    binomY m c (Finsupp.single j 1) =
      ∑ k : Fin (j + 1), ((((m - j : ℕ) + k).choose k : R) * c ^ (k : ℕ)) •
        Finsupp.single (⟨j - k, by omega⟩ : Fin (m + 1)) 1 := by
  rw [binomY, Finsupp.linearCombination_single, one_smul]

theorem binomX_single_apply (c : R) (j i : Fin (m + 1)) :
    binomX m c (Finsupp.single j 1) i = ((i : ℕ).choose j : R) * c ^ ((i : ℕ) - j) := by
  rw [binomX_single, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Fin.ext_iff, mul_ite,
    mul_one, mul_zero]
  rcases le_or_gt (j : ℕ) i with h | h
  · rw [Finset.sum_eq_single ⟨i - j, by omega⟩ (fun k _ hk => ite_eq_right fun h' => hk (by
        ext; simp only; omega)) (by simp), ite_eq_left (by simp only; omega)]
    simp only [Nat.add_sub_cancel' h, Nat.choose_symm h]
  · rw [Finset.sum_eq_zero fun k _ => ite_eq_right (by omega), Nat.choose_eq_zero_of_lt h,
      Nat.cast_zero, zero_mul]

theorem binomY_single_apply (c : R) (j i : Fin (m + 1)) :
    binomY m c (Finsupp.single j 1) i =
      ((m - i : ℕ).choose (m - j) : R) * c ^ ((j : ℕ) - i) := by
  rw [binomY_single, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Fin.ext_iff, mul_ite,
    mul_one, mul_zero]
  rcases le_or_gt (i : ℕ) j with h | h
  · rw [Finset.sum_eq_single ⟨j - i, by omega⟩ (fun k _ hk => ite_eq_right fun h' => hk (by
        ext; simp only; omega)) (by simp), ite_eq_left (by simp only; omega)]
    have h1 : m - j + (j - i) = m - i := by omega
    have h2 : m - j = (m - i) - (j - i) := by omega
    simp only [h1]
    rw [h2, Nat.choose_symm (by omega)]
  · rw [Finset.sum_eq_zero fun k _ => ite_eq_right (by omega),
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

private theorem end_ext {f g : Module.End R (Fin (m + 1) →₀ R)}
    (h : ∀ i j, f (Finsupp.single j 1) i = g (Finsupp.single j 1) i) : f = g :=
  Finsupp.basisSingleOne.ext fun j => by
    ext i
    simpa using h i j

private theorem mul_single_apply (f g : Module.End R (Fin (m + 1) →₀ R)) (i j : Fin (m + 1)) :
    (f * g) (Finsupp.single j 1) i =
      ∑ l, f (Finsupp.single l 1) i * g (Finsupp.single j 1) l := by
  conv_lhs => rw [Module.End.mul_apply, ← Finsupp.univ_sum_single (g (Finsupp.single j 1))]
  simp only [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

private theorem sum_fin_eq_sum_range_add {M : Type*} [AddCommMonoid M] (g : ℕ → M) {a : ℕ}
    (ha : a ≤ m) (hg : ∀ l < a, g l = 0) :
    ∑ l : Fin (m + 1), g l = ∑ b ∈ Finset.range (m - a + 1), g (a + b) := by
  rw [Fin.sum_univ_eq_sum_range g (m + 1), Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive g (Nat.zero_le a) (by omega : a ≤ m + 1),
    Finset.sum_Ico_eq_sum_range g a (m + 1),
    Finset.sum_eq_zero fun l hl => hg l (by simpa using hl), zero_add,
    show m + 1 - a = m - a + 1 by omega]

theorem binomX_zero : binomX m (0 : R) = 1 := by
  refine end_ext fun i j => ?_
  rw [binomX_single_apply, Module.End.one_apply, Finsupp.single_apply]
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul, ite_eq_right (by omega)]
  · rw [ite_eq_left (Fin.ext h.symm), h, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one,
      one_mul]
  · rw [zero_pow (by omega), mul_zero, ite_eq_right (by omega)]

private theorem sum_choose_mul_choose (c d : R) (i j : Fin (m + 1)) :
    ∑ l : Fin (m + 1), ((i : ℕ).choose l : R) * c ^ ((i : ℕ) - l) *
        (((l : ℕ).choose j : R) * d ^ ((l : ℕ) - j)) =
      ((i : ℕ).choose j : R) * (c + d) ^ ((i : ℕ) - j) := by
  rw [sum_fin_eq_sum_range_add (fun l => ((i : ℕ).choose l : R) * c ^ ((i : ℕ) - l) *
      ((l.choose j : R) * d ^ (l - j))) (Nat.le_of_lt_succ j.2)
      fun l hl => by rw [Nat.choose_eq_zero_of_lt hl, Nat.cast_zero, zero_mul, mul_zero]]
  have hterm : ∀ b ∈ Finset.range (m - j + 1),
      ((i : ℕ).choose (j + b) : R) * c ^ ((i : ℕ) - (j + b)) *
          (((j + b).choose j : R) * d ^ (j + b - j)) =
        ((i : ℕ).choose j : R) * (d ^ b * c ^ ((i - j : ℕ) - b) * ((i - j : ℕ).choose b : R)) := by
    intro b _
    have key := Nat.choose_mul (n := i) (k := j + b) (s := j) (Nat.le_add_right _ _)
    rw [Nat.add_sub_cancel_left] at key
    rw [Nat.add_sub_cancel_left, Nat.sub_sub]
    calc ((i : ℕ).choose (j + b) : R) * c ^ ((i : ℕ) - (j + b)) *
          (((j + b).choose j : R) * d ^ b) =
        (((i : ℕ).choose (j + b) * (j + b).choose j : ℕ) : R) * (d ^ b * c ^ ((i : ℕ) - (j + b)))
          := by push_cast; ring
      _ = _ := by rw [key]; push_cast; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, add_comm c d, add_pow]
  congr 1
  refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun b _ hb => ?_).symm
  rw [Finset.mem_range, not_lt] at hb
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

theorem binomX_mul_binomX (c d : R) : binomX m c * binomX m d = binomX m (c + d) := by
  refine end_ext fun i j => ?_
  simp only [mul_single_apply, binomX_single_apply]
  exact sum_choose_mul_choose c d i j

private def revOp (m : ℕ) : Module.End R (Fin (m + 1) →₀ R) :=
  Finsupp.lmapDomain R R Fin.rev

private theorem revOp_single (j : Fin (m + 1)) :
    revOp m (Finsupp.single j (1 : R)) = Finsupp.single (Fin.rev j) 1 := by
  rw [revOp, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private theorem revOp_apply (v : Fin (m + 1) →₀ R) (i : Fin (m + 1)) :
    revOp m v i = v (Fin.rev i) := by
  rw [revOp, Finsupp.lmapDomain_apply, ← Fin.rev_rev i,
    Finsupp.mapDomain_apply_of_injective Fin.rev_injective, Fin.rev_rev]

private theorem revOp_mul_revOp : revOp m * revOp m = (1 : Module.End R (Fin (m + 1) →₀ R)) := by
  refine end_ext fun i j => ?_
  rw [Module.End.mul_apply, revOp_single, revOp_single, Fin.rev_rev, Module.End.one_apply]

private theorem binomY_eq (c : R) : binomY m c = revOp m * binomX m c * revOp m := by
  refine end_ext fun i j => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, revOp_single, revOp_apply, binomX_single_apply,
    binomY_single_apply, Fin.val_rev, Fin.val_rev, show m + 1 - ((i : ℕ) + 1) = m - i by omega,
    show m + 1 - ((j : ℕ) + 1) = m - j by omega, show m - (i : ℕ) - (m - j) = j - i by omega]

theorem binomY_zero : binomY m (0 : R) = 1 := by
  rw [binomY_eq, binomX_zero, mul_one, revOp_mul_revOp]

theorem binomY_mul_binomY (c d : R) : binomY m c * binomY m d = binomY m (c + d) := by
  rw [binomY_eq, binomY_eq, binomY_eq, ← binomX_mul_binomX]
  simp only [mul_assoc]
  rw [← mul_assoc (revOp m) (revOp m), revOp_mul_revOp, one_mul]

private theorem alternating_sum_choose (n : ℕ) : ∀ i j : ℕ,
    ∑ b ∈ Finset.range (n + 1), (-1 : ℤ) ^ b * (n.choose b : ℤ) * ((i + b).choose j : ℤ) =
      if n ≤ j then (-1) ^ n * (i.choose (j - n) : ℤ) else 0 := by
  induction n with
  | zero => intro i j; simp
  | succ n ih =>
    intro i j
    have hsplit : ∑ b ∈ Finset.range (n + 1 + 1),
        (-1 : ℤ) ^ b * ((n + 1).choose b : ℤ) * ((i + b).choose j : ℤ) =
          ∑ b ∈ Finset.range (n + 1), (-1 : ℤ) ^ b * (n.choose b : ℤ) * ((i + b).choose j : ℤ) -
            ∑ b ∈ Finset.range (n + 1),
              (-1 : ℤ) ^ b * (n.choose b : ℤ) * ((i + 1 + b).choose j : ℤ) := by
      have hlast : ∑ b ∈ Finset.range (n + 1 + 1),
          (-1 : ℤ) ^ b * (n.choose b : ℤ) * ((i + b).choose j : ℤ) =
            ∑ b ∈ Finset.range (n + 1),
              (-1 : ℤ) ^ b * (n.choose b : ℤ) * ((i + b).choose j : ℤ) := by
        rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul,
          add_zero]
      rw [← hlast, Finset.sum_range_succ', Finset.sum_range_succ' (fun b =>
        (-1 : ℤ) ^ b * (n.choose b : ℤ) * ((i + b).choose j : ℤ)), add_sub_right_comm,
        ← Finset.sum_sub_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun b _ => ?_
        rw [Nat.choose_succ_succ', show i + 1 + b = i + (b + 1) by ring]
        push_cast
        ring
      · simp
    rw [hsplit, ih i j, ih (i + 1) j]
    split_ifs with h1 h2 h2
    · obtain ⟨k, rfl⟩ : ∃ k, j = n + 1 + k := ⟨j - (n + 1), by omega⟩
      rw [show n + 1 + k - n = k + 1 by omega, show n + 1 + k - (n + 1) = k by omega,
        Nat.choose_succ_succ']
      push_cast
      ring
    · obtain rfl : j = n := by omega
      simp
    · omega
    · simp

private theorem sum_choose_mul_neg_one_pow (i j : Fin (m + 1)) :
    ∑ l : Fin (m + 1), ((m - i : ℕ).choose (m - l) : R) * (-1) ^ ((l : ℕ) - i) *
        ((l : ℕ).choose j : R) =
      (-1) ^ (j : ℕ) * (((i : ℕ).choose (m - j) : R) * (-1) ^ ((i : ℕ) - (m - j))) := by
  rw [sum_fin_eq_sum_range_add (fun l => ((m - i : ℕ).choose (m - l) : R) * (-1) ^ (l - i) *
      (l.choose j : R)) (Nat.le_of_lt_succ i.2) fun l hl => by
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]]
  have hterm : ∀ b ∈ Finset.range (m - i + 1),
      ((m - i : ℕ).choose (m - (i + b)) : R) * (-1) ^ ((i : ℕ) + b - i) *
          (((i : ℕ) + b).choose j : R) =
        (((-1 : ℤ) ^ b * ((m - i : ℕ).choose b : ℤ) * (((i : ℕ) + b).choose j : ℤ) : ℤ) : R) := by
    intro b hb
    rw [Finset.mem_range] at hb
    rw [show m - ((i : ℕ) + b) = m - i - b by omega, Nat.choose_symm (by omega),
      Nat.add_sub_cancel_left]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Int.cast_sum, alternating_sum_choose]
  split_ifs with h
  · have hsign : (-1 : R) ^ (j : ℕ) * (-1) ^ ((i : ℕ) - (m - j)) = (-1) ^ (m - (i : ℕ)) := by
      rw [← pow_add, show (j : ℕ) + (i - (m - j)) = (m - i) + 2 * (i - (m - j)) by omega,
        pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [show (j : ℕ) - (m - i) = i - (m - j) by omega, Nat.choose_symm (by omega)]
    push_cast
    rw [← hsign]
    ring
  · rw [Int.cast_zero, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, mul_zero]

private def torusOp (m : ℕ) (a : Rˣ) : Module.End R (Fin (m + 1) →₀ R) :=
  Finsupp.linearCombination R fun j : Fin (m + 1) => ((a : R) ^ (j : ℕ)) • Finsupp.single j 1

private theorem torusOp_single (a : Rˣ) (j : Fin (m + 1)) :
    torusOp m a (Finsupp.single j 1) = ((a : R) ^ (j : ℕ)) • Finsupp.single j 1 := by
  rw [torusOp, Finsupp.linearCombination_single, one_smul]

private theorem torusOp_apply (a : Rˣ) (v : Fin (m + 1) →₀ R) (i : Fin (m + 1)) :
    torusOp m a v i = (a : R) ^ (i : ℕ) * v i := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hv, hw, mul_add]
  | single l r =>
    rw [← Finsupp.smul_single_one, map_smul, torusOp_single, Finsupp.smul_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    by_cases h : l = i
    · subst h
      ring
    · simp [h]

private theorem torusOp_mul_torusOp_inv (a : Rˣ) :
    torusOp m a * torusOp m a⁻¹ = (1 : Module.End R (Fin (m + 1) →₀ R)) := by
  refine end_ext fun i j => ?_
  rw [Module.End.mul_apply, torusOp_apply, torusOp_single, Finsupp.smul_apply, smul_eq_mul,
    Module.End.one_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h
    rw [mul_one, ← mul_pow, Units.mul_inv, one_pow]
  · rw [mul_zero, mul_zero]

private theorem torusOp_mul_binomX (a : Rˣ) (c : R) :
    torusOp m a * binomX m c = binomX m (a * c) * torusOp m a := by
  refine end_ext fun i j => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, torusOp_apply, torusOp_single, map_smul,
    Finsupp.smul_apply, smul_eq_mul, binomX_single_apply, binomX_single_apply]
  rcases le_or_gt (j : ℕ) i with h | h
  · rw [mul_pow, ← Nat.add_sub_cancel' h, pow_add, Nat.add_sub_cancel_left]
    ring
  · simp [Nat.choose_eq_zero_of_lt h]

private theorem torusOp_mul_binomY (a : Rˣ) (c : R) :
    torusOp m a * binomY m c = binomY m (((a⁻¹ : Rˣ) : R) * c) * torusOp m a := by
  refine end_ext fun i j => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, torusOp_apply, torusOp_single, map_smul,
    Finsupp.smul_apply, smul_eq_mul, binomY_single_apply, binomY_single_apply]
  rcases le_or_gt (i : ℕ) j with h | h
  · have ha : (a : R) ^ (j : ℕ) * ((a⁻¹ : Rˣ) : R) ^ ((j : ℕ) - i) = (a : R) ^ (i : ℕ) := by
      rw [← Nat.add_sub_cancel' h, pow_add, Nat.add_sub_cancel_left, mul_assoc, ← mul_pow,
        Units.mul_inv, one_pow, mul_one]
    rw [mul_pow, ← ha]
    ring
  · simp [Nat.choose_eq_zero_of_lt (show m - (i : ℕ) < m - j by omega)]

private theorem binomY_neg_one_mul_binomX_one :
    binomY m (-1 : R) * binomX m 1 = binomX m (-1) * (revOp m * torusOp m (-1)) := by
  refine end_ext fun i j => ?_
  rw [mul_single_apply, Module.End.mul_apply, Module.End.mul_apply, torusOp_single, map_smul,
    map_smul, revOp_single, Finsupp.smul_apply, smul_eq_mul, binomX_single_apply, Fin.val_rev,
    show m + 1 - ((j : ℕ) + 1) = m - j by omega, Units.val_neg, Units.val_one]
  simp only [binomY_single_apply, binomX_single_apply, one_pow, mul_one]
  exact sum_choose_mul_neg_one_pow i j

private theorem binomX_one_mul_binomY_neg_one_mul_binomX_one :
    binomX m (1 : R) * binomY m (-1) * binomX m 1 = revOp m * torusOp m (-1) := by
  rw [mul_assoc, binomY_neg_one_mul_binomX_one, ← mul_assoc, binomX_mul_binomX, add_neg_cancel,
    binomX_zero, one_mul]

private theorem binomN_eq (t : Rˣ) :
    binomN m t = torusOp m t * (revOp m * torusOp m (-1)) * torusOp m t⁻¹ := by
  have hX : binomX m (t : R) * torusOp m t = torusOp m t * binomX m 1 := by
    rw [torusOp_mul_binomX, mul_one]
  have hY : binomY m (-((t⁻¹ : Rˣ) : R)) * torusOp m t = torusOp m t * binomY m (-1) := by
    rw [torusOp_mul_binomY, mul_neg_one]
  have hN : binomN m t * torusOp m t = torusOp m t * (revOp m * torusOp m (-1)) := by
    rw [← binomX_one_mul_binomY_neg_one_mul_binomX_one, binomN, mul_assoc, hX, ← mul_assoc,
      mul_assoc (binomX m _), hY, ← mul_assoc, hX]
    simp only [mul_assoc]
  rw [← hN, mul_assoc, torusOp_mul_torusOp_inv, mul_one]

theorem binomN_single (t : Rˣ) (j : Fin (m + 1)) :
    binomN m t (Finsupp.single j 1) =
      ((-1) ^ (j : ℕ) * ((t ^ ((m : ℤ) - 2 * (j : ℕ)) : Rˣ) : R)) •
        Finsupp.single (Fin.rev j) 1 := by
  have hz : t ^ ((m : ℤ) - 2 * (j : ℕ)) = t ^ (m - (j : ℕ)) * t⁻¹ ^ (j : ℕ) := by
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast [Nat.cast_sub (Nat.le_of_lt_succ j.2)]
    ring
  simp only [binomN_eq, Module.End.mul_apply, torusOp_single, map_smul, revOp_single, smul_smul]
  congr 1
  rw [hz, Fin.val_rev, show m + 1 - ((j : ℕ) + 1) = m - j by omega, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  ring

private theorem revOp_mul_binomX (c : R) : revOp m * binomX m c = binomY m c * revOp m := by
  rw [binomY_eq, mul_assoc, mul_assoc, revOp_mul_revOp, mul_one]

private theorem revOp_mul_binomY (c : R) : revOp m * binomY m c = binomX m c * revOp m := by
  rw [binomY_eq, ← mul_assoc, ← mul_assoc, revOp_mul_revOp, one_mul]

private theorem mul_mul_eq_of_mul_eq {M : Type*} [Semigroup M] {a b c d : M} (h : a * b = c * d)
    (f : M) : a * (b * f) = c * (d * f) := by
  rw [← mul_assoc, h, mul_assoc]

theorem binomN_mul_binomX (t : Rˣ) (c : R) :
    binomN m t * binomX m c = binomY m (-c * ((t⁻¹ ^ 2 : Rˣ) : R)) * binomN m t := by
  have hc : ((t⁻¹ : Rˣ) : R) * (((-1 : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * c)) =
      -c * ((t⁻¹ ^ 2 : Rˣ) : R) := by
    rw [Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val]
    ring
  have h4 := torusOp_mul_binomY (m := m) t (((-1 : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * c))
  rw [hc] at h4
  rw [binomN_eq]
  simp only [mul_assoc, torusOp_mul_binomX t⁻¹ c,
    mul_mul_eq_of_mul_eq (torusOp_mul_binomX (-1) (((t⁻¹ : Rˣ) : R) * c)),
    mul_mul_eq_of_mul_eq (revOp_mul_binomX (((-1 : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * c))),
    mul_mul_eq_of_mul_eq h4]

theorem binomN_mul_binomY (t : Rˣ) (c : R) :
    binomN m t * binomY m c = binomX m (-c * ((t ^ 2 : Rˣ) : R)) * binomN m t := by
  have hc : (t : R) * ((((-1 : Rˣ)⁻¹ : Rˣ) : R) * ((((t⁻¹)⁻¹ : Rˣ) : R) * c)) =
      -c * ((t ^ 2 : Rˣ) : R) := by
    rw [inv_inv, inv_neg_one, Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val]
    ring
  have h4 := torusOp_mul_binomX (m := m) t
    ((((-1 : Rˣ)⁻¹ : Rˣ) : R) * ((((t⁻¹)⁻¹ : Rˣ) : R) * c))
  rw [hc] at h4
  rw [binomN_eq]
  simp only [mul_assoc, torusOp_mul_binomY t⁻¹ c,
    mul_mul_eq_of_mul_eq (torusOp_mul_binomY (-1) ((((t⁻¹)⁻¹ : Rˣ) : R) * c)),
    mul_mul_eq_of_mul_eq
      (revOp_mul_binomY ((((-1 : Rˣ)⁻¹ : Rˣ) : R) * ((((t⁻¹)⁻¹ : Rˣ) : R) * c))),
    mul_mul_eq_of_mul_eq h4]

theorem binomial_string_weyl_identities (m : ℕ) (t : Rˣ) :
    (∀ j : Fin (m + 1), binomN m t (Finsupp.single j 1) =
      ((-1) ^ (j : ℕ) * ((t ^ ((m : ℤ) - 2 * (j : ℕ)) : Rˣ) : R)) •
        Finsupp.single (Fin.rev j) 1) ∧
      (∀ c : R, binomN m t * binomX m c = binomY m (-c * ((t⁻¹ ^ 2 : Rˣ) : R)) * binomN m t) ∧
      ∀ c : R, binomN m t * binomY m c = binomX m (-c * ((t ^ 2 : Rˣ) : R)) * binomN m t :=
  ⟨binomN_single t, binomN_mul_binomX t, binomN_mul_binomY t⟩

end CFSG.Blueprint.Chevalley
