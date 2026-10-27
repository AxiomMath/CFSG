module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LieType.RootSystem.Cartan
public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Roots.Levels
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.RootSystem

abbrev bnRank (n : ℕ) : ℕ := n / 2

@[expose] def weight (n : ℕ) (i : Fin n) : Fin (n / 2) → ℤ :=
  if h : i.val < n / 2 then Pi.single ⟨i.val, h⟩ 1
  else if h' : n - 1 - i.val < n / 2 then -Pi.single ⟨n - 1 - i.val, h'⟩ 1 else 0

@[expose] def cartan (n : ℕ) : Matrix (Fin (n / 2)) (Fin (n / 2)) ℤ :=
  if Even n then Symplectic.cartanC (n / 2) else (Symplectic.cartanC (n / 2))ᵀ

theorem isFiniteType_cartan (n : ℕ) : TauCeti.IsFiniteType (cartan n) := by
  unfold cartan
  split_ifs
  · exact Symplectic.isFiniteType_cartanC _
  · exact (Symplectic.isFiniteType_cartanC _).transpose

@[expose] def divisible (n : ℕ) : Set (Fin (n / 2)) :=
  if Even n then ∅ else {k | k.val + 1 = n / 2}

@[expose] def toStd (n : ℕ) (v : Fin (n / 2) → ℤ) : Fin (n / 2) → ℤ :=
  if Even n then Symplectic.toStd (n / 2) v
  else fun a => v a - (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0)

private def toStdLin (n : ℕ) : (Fin (n / 2) → ℤ) →ₗ[ℤ] (Fin (n / 2) → ℤ) where
  toFun := toStd n
  map_add' v w := by
    funext a
    by_cases h : Even n
    · simp only [toStd, h, ite_true, Symplectic.toStd, Pi.add_apply]
      split_ifs <;> ring
    · simp only [toStd, h, ite_false, Pi.add_apply]
      split_ifs <;> ring
  map_smul' c v := by
    funext a
    by_cases h : Even n
    · simp only [toStd, h, ite_true, Symplectic.toStd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;> ring
    · simp only [toStd, h, ite_false, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs <;> ring

private theorem toStdLin_apply (n : ℕ) (v : Fin (n / 2) → ℤ) : toStdLin n v = toStd n v := rfl

private theorem toStd_sub (n : ℕ) (v w : Fin (n / 2) → ℤ) :
    toStd n (v - w) = toStd n v - toStd n w :=
  map_sub (toStdLin n) v w

private theorem toStd_neg (n : ℕ) (v : Fin (n / 2) → ℤ) : toStd n (-v) = -toStd n v :=
  map_neg (toStdLin n) v

private theorem toStd_zsmul (n : ℕ) (c : ℤ) (v : Fin (n / 2) → ℤ) :
    toStd n (c • v) = c • toStd n v :=
  map_zsmul (toStdLin n) c v

private theorem toStd_nsmul (n : ℕ) (c : ℕ) (v : Fin (n / 2) → ℤ) :
    toStd n (c • v) = c • toStd n v :=
  map_nsmul (toStdLin n) c v

private theorem toStd_apply_of_even {n : ℕ} (h : Even n) (v : Fin (n / 2) → ℤ) (a : Fin (n / 2)) :
    toStd n v a = (if a.val + 1 = n / 2 then 2 else 1) * v a -
      (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) := by
  simp only [toStd, h, ite_true, Symplectic.toStd]

private theorem toStd_apply_of_odd {n : ℕ} (h : ¬Even n) (v : Fin (n / 2) → ℤ) (a : Fin (n / 2)) :
    toStd n v a = v a - (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) := by
  simp only [toStd, h, ite_false]

private theorem toStd_single_of_lt (n : ℕ) {k : Fin (n / 2)} (h : k.val + 1 < n / 2) :
    toStd n (Pi.single k 1) = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 := by
  funext a
  by_cases he : Even n
  · rw [toStd_apply_of_even he]
    simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  · rw [toStd_apply_of_odd he]
    simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

private theorem toStd_single_of_even {n : ℕ} (he : Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) : toStd n (Pi.single k 1) = 2 • Pi.single k 1 := by
  funext a
  rw [toStd_apply_of_even he]
  simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs <;> omega

private theorem toStd_single_of_odd {n : ℕ} (he : ¬Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) : toStd n (Pi.single k 1) = Pi.single k 1 := by
  funext a
  rw [toStd_apply_of_odd he]
  simp only [Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem toStd_injective (n : ℕ) : Function.Injective (toStd n) := by
  intro v w h
  have key : ∀ d (k : Fin (n / 2)), k.val = d → v k = w k := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hk
      have hk' := congrFun h k
      have hprev : (if h : 0 < k.val then v ⟨k.val - 1, by omega⟩ else 0) =
          (if h : 0 < k.val then w ⟨k.val - 1, by omega⟩ else 0) := by
        split_ifs with h0
        · exact ih (k.val - 1) (by omega) _ rfl
        · rfl
      by_cases he : Even n
      · rw [toStd_apply_of_even he, toStd_apply_of_even he, hprev] at hk'
        have hc : (if k.val + 1 = n / 2 then (2 : ℤ) else 1) ≠ 0 := by split_ifs <;> norm_num
        exact mul_left_cancel₀ hc (by linarith)
      · rw [toStd_apply_of_odd he, toStd_apply_of_odd he, hprev] at hk'
        linarith
  funext k
  exact key k.val k rfl

private def stdRefl {m : ℕ} (k : Fin m) (e : Fin m → ℤ) : Fin m → ℤ :=
  if h : k.val + 1 < m then e ∘ Equiv.swap k ⟨k.val + 1, h⟩
  else fun a => (if a = k then -1 else 1) * e a

private theorem stdRefl_of_lt {m : ℕ} {k : Fin m} (h : k.val + 1 < m) (e : Fin m → ℤ) :
    stdRefl k e = e ∘ Equiv.swap k ⟨k.val + 1, h⟩ := dite_eq_left h

private theorem stdRefl_of_not_lt {m : ℕ} {k : Fin m} (h : ¬k.val + 1 < m) (e : Fin m → ℤ) :
    stdRefl k e = fun a => (if a = k then -1 else 1) * e a := dite_eq_right h

private theorem stdRefl_sub {m : ℕ} (k : Fin m) (e f : Fin m → ℤ) :
    stdRefl k (e - f) = stdRefl k e - stdRefl k f := by
  by_cases h : k.val + 1 < m
  · simp only [stdRefl_of_lt h]
    rfl
  · simp only [stdRefl_of_not_lt h]
    funext a
    simp only [Pi.sub_apply]
    ring

private theorem stdRefl_nsmul {m : ℕ} (k : Fin m) (c : ℕ) (e : Fin m → ℤ) :
    stdRefl k (c • e) = c • stdRefl k e := by
  by_cases h : k.val + 1 < m
  · simp only [stdRefl_of_lt h]
    rfl
  · simp only [stdRefl_of_not_lt h]
    funext a
    simp only [Pi.smul_apply]
    ring

private theorem coroot_cartan_of_lt (n : ℕ) {k : Fin (n / 2)} (h : k.val + 1 < n / 2)
    (v : Fin (n / 2) → ℤ) :
    coroot (cartan n) k v = toStd n v k - toStd n v ⟨k.val + 1, h⟩ := by
  have key : coroot (cartan n) k =
      ((LinearMap.proj k : (Fin (n / 2) → ℤ) →ₗ[ℤ] ℤ) -
        LinearMap.proj (⟨k.val + 1, h⟩ : Fin (n / 2))).comp (toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdLin_apply]
    by_cases he : Even n
    · rw [toStd_apply_of_even he, toStd_apply_of_even he]
      simp only [cartan, he, ite_true, Symplectic.cartanC, Matrix.of_apply, Pi.single_apply,
        Fin.ext_iff]
      split_ifs <;> omega
    · rw [toStd_apply_of_odd he, toStd_apply_of_odd he]
      simp only [cartan, he, ite_false, Matrix.transpose_apply, Symplectic.cartanC,
        Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem coroot_cartan_of_even {n : ℕ} (he : Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) (v : Fin (n / 2) → ℤ) :
    coroot (cartan n) k v = toStd n v k := by
  have key : coroot (cartan n) k =
      (LinearMap.proj k : (Fin (n / 2) → ℤ) →ₗ[ℤ] ℤ).comp (toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single, coroot_single,
      toStdLin_apply]
    rw [toStd_apply_of_even he]
    simp only [cartan, he, ite_true, Symplectic.cartanC, Matrix.of_apply, Pi.single_apply,
      Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem coroot_cartan_of_odd {n : ℕ} (he : ¬Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) (v : Fin (n / 2) → ℤ) :
    coroot (cartan n) k v = 2 * toStd n v k := by
  have key : coroot (cartan n) k =
      (2 : ℤ) • (LinearMap.proj k : (Fin (n / 2) → ℤ) →ₗ[ℤ] ℤ).comp (toStdLin n) := by
    ext l
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdLin_apply, smul_eq_mul]
    rw [toStd_apply_of_odd he]
    simp only [cartan, he, ite_false, Matrix.transpose_apply, Symplectic.cartanC,
      Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  have := LinearMap.congr_fun key v
  simpa [toStdLin_apply] using this

private theorem toStd_reflection (n : ℕ) (k : Fin (n / 2)) (v : Fin (n / 2) → ℤ) :
    toStd n (reflection (cartan n) k v) = stdRefl k (toStd n v) := by
  rw [reflection_apply_coroot, toStd_sub, toStd_zsmul]
  by_cases h : k.val + 1 < n / 2
  · rw [coroot_cartan_of_lt n h, toStd_single_of_lt n h, stdRefl_of_lt h]
    have hne : (⟨k.val + 1, h⟩ : Fin (n / 2)) ≠ k := Fin.ne_of_val_ne (by simp)
    funext a
    by_cases ha : a = k
    · subst ha
      simp [Ne.symm hne]
    by_cases ha' : a = ⟨k.val + 1, h⟩
    · subst ha'
      simp [hne]
    · simp [ha, ha', Equiv.swap_apply_of_ne_of_ne ha ha']
  · by_cases he : Even n
    · rw [coroot_cartan_of_even he h, toStd_single_of_even he h, stdRefl_of_not_lt h]
      funext a
      by_cases ha : a = k
      · subst ha
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, ite_true]
        ring
      · simp [ha]
    · rw [coroot_cartan_of_odd he h, toStd_single_of_odd he h, stdRefl_of_not_lt h]
      funext a
      by_cases ha : a = k
      · subst ha
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, ite_true]
        ring
      · simp [ha]

private theorem weight_apply (n : ℕ) (i : Fin n) (a : Fin (n / 2)) :
    weight n i a = (if i.val = a.val then 1 else 0) - (if n - 1 - i.val = a.val then 1 else 0) := by
  unfold weight
  by_cases h : i.val < n / 2
  · rw [dite_eq_left h, Pi.single_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [dite_eq_right h]
    by_cases h' : n - 1 - i.val < n / 2
    · rw [dite_eq_left h', Pi.neg_apply, Pi.single_apply]
      simp only [Fin.ext_iff]
      split_ifs <;> omega
    · rw [dite_eq_right h']
      simp only [Pi.zero_apply]
      split_ifs <;> omega

private theorem weight_rev (n : ℕ) (i : Fin n) : weight n (Fin.rev i) = -weight n i := by
  funext a
  rw [Pi.neg_apply, weight_apply, weight_apply, Fin.val_rev]
  split_ifs <;> omega

private theorem weight_lowIdx {n : ℕ} (a : Fin (n / 2)) : weight n (lowIdx a) = Pi.single a 1 := by
  funext b
  rw [weight_apply, Pi.single_apply]
  simp only [lowIdx, Fin.ext_iff]
  split_ifs <;> omega

private theorem weight_rev_lowIdx {n : ℕ} (a : Fin (n / 2)) :
    weight n (Fin.rev (lowIdx a)) = -Pi.single a 1 := by
  rw [weight_rev, weight_lowIdx]

private theorem single_comp_swap {m : ℕ} (x p q : Fin m) (c : ℤ) :
    Pi.single x c ∘ Equiv.swap p q = Pi.single (Equiv.swap p q x) c := by
  rw [Pi.single_comp_equiv, Equiv.symm_swap]

private theorem weight_comp_swap {n : ℕ} (i : Fin n) (p q : Fin (n / 2))
    (hp : weight n i p = 0) (hq : weight n i q = 0) : weight n i ∘ Equiv.swap p q = weight n i := by
  funext a
  rw [Function.comp_apply]
  by_cases hap : a = p
  · subst hap
    rw [Equiv.swap_apply_left, hp, hq]
  by_cases haq : a = q
  · subst haq
    rw [Equiv.swap_apply_right, hp, hq]
  rw [Equiv.swap_apply_of_ne_of_ne hap haq]

private theorem weight_levelPerm {n : ℕ} (k : Fin (n / 2)) (i : Fin n) :
    weight n (levelPerm k i) = stdRefl k (weight n i) := by
  by_cases h : k.val + 1 < n / 2
  · set k' : Fin (n / 2) := ⟨k.val + 1, h⟩ with hk'
    have hkk' : k ≠ k' := Fin.ne_of_val_ne (by simp [hk'])
    have e1 : lowIdx k ≠ lowIdx k' := Fin.ne_of_val_ne (by simp [lowIdx, hk'])
    have e2 : lowIdx k ≠ Fin.rev (lowIdx k) := Fin.ne_of_val_ne (by simp [lowIdx]; omega)
    have e3 : lowIdx k ≠ Fin.rev (lowIdx k') := Fin.ne_of_val_ne (by simp [lowIdx, hk']; omega)
    have e4 : lowIdx k' ≠ Fin.rev (lowIdx k) := Fin.ne_of_val_ne (by simp [lowIdx, hk']; omega)
    have e5 : lowIdx k' ≠ Fin.rev (lowIdx k') := Fin.ne_of_val_ne (by simp [lowIdx, hk']; omega)
    have e6 : Fin.rev (lowIdx k) ≠ Fin.rev (lowIdx k') := fun h => e1 (Fin.rev_injective h)
    rw [levelPerm, dite_eq_left h, stdRefl_of_lt h, Equiv.Perm.mul_apply]
    by_cases hi1 : i = lowIdx k
    · subst hi1
      rw [Equiv.swap_apply_of_ne_of_ne e2 e3, Equiv.swap_apply_left, weight_lowIdx, weight_lowIdx,
        single_comp_swap, Equiv.swap_apply_left]
    by_cases hi2 : i = lowIdx k'
    · subst hi2
      rw [Equiv.swap_apply_of_ne_of_ne e4 e5, Equiv.swap_apply_right, weight_lowIdx, weight_lowIdx,
        single_comp_swap, Equiv.swap_apply_right]
    by_cases hi3 : i = Fin.rev (lowIdx k)
    · subst hi3
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm e3) (Ne.symm e5),
        weight_rev_lowIdx, weight_rev_lowIdx, Pi.neg_comp, single_comp_swap, Equiv.swap_apply_left]
    by_cases hi4 : i = Fin.rev (lowIdx k')
    · subst hi4
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm e2) (Ne.symm e4),
        weight_rev_lowIdx, weight_rev_lowIdx, Pi.neg_comp, single_comp_swap, Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne hi3 hi4, Equiv.swap_apply_of_ne_of_ne hi1 hi2]
    have hv1 : i.val ≠ k.val := fun e => hi1 (Fin.ext e)
    have hv2 : i.val ≠ k.val + 1 := fun e => hi2 (Fin.ext e)
    have hv3 : i.val ≠ n - 1 - k.val := fun e => hi3 (Fin.ext (by simp [lowIdx]; omega))
    have hv4 : i.val ≠ n - 1 - (k.val + 1) := fun e => hi4 (Fin.ext (by simp [lowIdx, hk']; omega))
    refine (weight_comp_swap i k k' ?_ ?_).symm
    · rw [weight_apply]
      split_ifs <;> omega
    · rw [weight_apply]
      simp only [hk']
      split_ifs <;> omega
  · rw [levelPerm, dite_eq_right h, stdRefl_of_not_lt h]
    funext a
    rw [weight_apply, weight_apply, val_swap_apply]
    simp only [lowIdx, Fin.val_rev, Fin.ext_iff]
    by_cases hi1 : i.val = k.val
    · simp only [hi1, ite_true]
      split_ifs <;> omega
    by_cases hi2 : i.val = n - (k.val + 1)
    · simp only [hi2, ite_true]
      split_ifs <;> omega
    · simp only [hi1, hi2, ite_false]
      split_ifs <;> omega

private def IsRootVec (n : ℕ) (e : Fin (n / 2) → ℤ) : Prop :=
  (∃ i j : Fin n, i ≠ j ∧ i ≠ Fin.rev i ∧ j ≠ Fin.rev j ∧ j ≠ Fin.rev i ∧
      e = weight n i - weight n j) ∨
    (∃ i : Fin n, i ≠ Fin.rev i ∧ e = 2 • weight n i) ∨
    (¬Even n ∧ ∃ i : Fin n, i ≠ Fin.rev i ∧ e = weight n i)

private theorem levelPerm_ne_rev {n : ℕ} (k : Fin (n / 2)) {i : Fin n} (hi : i ≠ Fin.rev i) :
    levelPerm k i ≠ Fin.rev (levelPerm k i) := by
  rw [← levelPerm_rev]
  exact (levelPerm k).injective.ne hi

private theorem exists_weight_stdRefl {n : ℕ} (k : Fin (n / 2)) {e : Fin (n / 2) → ℤ}
    (h : ∃ i : Fin n, i ≠ Fin.rev i ∧ e = weight n i) :
    ∃ i : Fin n, i ≠ Fin.rev i ∧ stdRefl k e = weight n i := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨levelPerm k i, levelPerm_ne_rev k hi, (weight_levelPerm k i).symm⟩

private theorem isRootVec_stdRefl {n : ℕ} (k : Fin (n / 2)) {e : Fin (n / 2) → ℤ}
    (h : IsRootVec n e) : IsRootVec n (stdRefl k e) := by
  rcases h with ⟨i, j, hij, hi, hj, hji, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨ho, h3⟩
  · refine Or.inl ⟨levelPerm k i, levelPerm k j, (levelPerm k).injective.ne hij,
      levelPerm_ne_rev k hi,
      levelPerm_ne_rev k hj, ?_, ?_⟩
    · rw [← levelPerm_rev]
      exact (levelPerm k).injective.ne hji
    · rw [stdRefl_sub, weight_levelPerm, weight_levelPerm]
  · exact Or.inr (Or.inl ⟨levelPerm k i, levelPerm_ne_rev k hi, by
      rw [stdRefl_nsmul, weight_levelPerm]⟩)
  · exact Or.inr (Or.inr ⟨ho, exists_weight_stdRefl k h3⟩)

private theorem isRootVec_toStd_single {n : ℕ} (l : Fin (n / 2)) :
    IsRootVec n (toStd n (Pi.single l 1)) := by
  by_cases h : l.val + 1 < n / 2
  · refine Or.inl ⟨lowIdx l, lowIdx ⟨l.val + 1, h⟩, Fin.ne_of_val_ne (by simp [lowIdx]),
      lowIdx_ne_rev l l, lowIdx_ne_rev _ _, lowIdx_ne_rev _ _, ?_⟩
    rw [toStd_single_of_lt n h, weight_lowIdx, weight_lowIdx]
  · by_cases he : Even n
    · exact Or.inr (Or.inl ⟨lowIdx l, lowIdx_ne_rev l l, by
        rw [toStd_single_of_even he h, weight_lowIdx]⟩)
    · exact Or.inr (Or.inr ⟨he, lowIdx l, lowIdx_ne_rev l l, by
        rw [toStd_single_of_odd he h, weight_lowIdx]⟩)

private theorem isRootVec_toStd_weylAction {n : ℕ}
    (w : (coxeterMatrix (isFiniteType_cartan n)).Group) (l : Fin (n / 2)) :
    IsRootVec n (toStd n (weylAction (isFiniteType_cartan n) w (Pi.single l 1))) := by
  induction w using (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple_induction_left
    with
  | one =>
    rw [map_one, Module.End.one_apply]
    exact isRootVec_toStd_single l
  | mul_simple_left w k ih =>
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection]
    exact isRootVec_stdRefl k ih

private theorem exists_weight_toStd_weylAction {n : ℕ} (he : ¬Even n)
    (w : (coxeterMatrix (isFiniteType_cartan n)).Group) {l : Fin (n / 2)}
    (hl : ¬l.val + 1 < n / 2) :
    ∃ i : Fin n, i ≠ Fin.rev i ∧
      toStd n (weylAction (isFiniteType_cartan n) w (Pi.single l 1)) = weight n i := by
  induction w using (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple_induction_left
    with
  | one =>
    rw [map_one, Module.End.one_apply, toStd_single_of_odd he hl]
    exact ⟨lowIdx l, lowIdx_ne_rev l l, (weight_lowIdx l).symm⟩
  | mul_simple_left w k ih =>
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection]
    exact exists_weight_stdRefl k ih

section Reach

variable {m : ℕ} (P : (Fin m → ℤ) → Prop)

private theorem reach_sub_of_lt (hP : ∀ (k : Fin m) (e : Fin m → ℤ), P e → P (stdRefl k e))
    (h0 : ∀ (k : Fin m) (h : k.val + 1 < m), P (Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1)) :
    ∀ d (a b : Fin m), b.val = a.val + d + 1 → P (Pi.single a 1 - Pi.single b 1) := by
  intro d
  induction d with
  | zero =>
    intro a b hab
    have := h0 a (by omega)
    rwa [show (⟨a.val + 1, by omega⟩ : Fin m) = b from Fin.ext (by simp; omega)] at this
  | succ d ih =>
    intro a b hab
    set c : Fin m := ⟨a.val + d + 1, by omega⟩
    have hc : c.val + 1 < m := by simp [c]; omega
    have h := hP c _ (ih a c rfl)
    rw [stdRefl_of_lt hc, Pi.sub_comp, single_comp_swap, single_comp_swap,
      Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp [c]; omega))
        (Fin.ne_of_val_ne (by simp [c]; omega)), Equiv.swap_apply_left] at h
    rwa [show (⟨c.val + 1, hc⟩ : Fin m) = b from Fin.ext (by simp [c]; omega)] at h

private theorem reach_sub (hP : ∀ (k : Fin m) (e : Fin m → ℤ), P e → P (stdRefl k e))
    (hneg : ∀ e, P e → P (-e))
    (h0 : ∀ (k : Fin m) (h : k.val + 1 < m), P (Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1))
    {a b : Fin m} (hab : a ≠ b) : P (Pi.single a 1 - Pi.single b 1) := by
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact reach_sub_of_lt P hP h0 (b.val - a.val - 1) a b (by omega)
  · have := hneg _ (reach_sub_of_lt P hP h0 (a.val - b.val - 1) b a (by omega))
    rwa [neg_sub] at this

private theorem reach_add_of_lt (hP : ∀ (k : Fin m) (e : Fin m → ℤ), P e → P (stdRefl k e))
    (hneg : ∀ e, P e → P (-e))
    (h0 : ∀ (k : Fin m) (h : k.val + 1 < m), P (Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1)) :
    ∀ d (a b : Fin m), a.val < b.val → b.val + d + 1 = m →
      P (Pi.single a 1 + Pi.single b 1) := by
  intro d
  induction d with
  | zero =>
    intro a b hab hb
    have h := hP b _ (reach_sub P hP hneg h0 (Fin.ne_of_val_ne (by omega) : a ≠ b))
    rw [stdRefl_of_not_lt (by omega)] at h
    convert h using 1
    funext c
    by_cases hcb : c = b
    · subst hcb
      simp [Fin.ne_of_val_ne (by omega : a.val ≠ c.val)]
    · simp [hcb]
  | succ d ih =>
    intro a b hab hb
    set b' : Fin m := ⟨b.val + 1, by omega⟩
    have h := hP b _ (ih a b' (by simp [b']; omega) (by simp [b']; omega))
    have hb1 : b.val + 1 < m := by omega
    rw [stdRefl_of_lt hb1, Pi.add_comp, single_comp_swap, single_comp_swap,
      Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by simp; omega))] at h
    rwa [show (⟨b.val + 1, hb1⟩ : Fin m) = b' from rfl, Equiv.swap_apply_right] at h

private theorem reach_add (hP : ∀ (k : Fin m) (e : Fin m → ℤ), P e → P (stdRefl k e))
    (hneg : ∀ e, P e → P (-e))
    (h0 : ∀ (k : Fin m) (h : k.val + 1 < m), P (Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1))
    {a b : Fin m} (hab : a ≠ b) : P (Pi.single a 1 + Pi.single b 1) := by
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact reach_add_of_lt P hP hneg h0 (m - b.val - 1) a b h (by omega)
  · rw [add_comm]
    exact reach_add_of_lt P hP hneg h0 (m - a.val - 1) b a h (by omega)

private theorem reach_smul_single (hP : ∀ (k : Fin m) (e : Fin m → ℤ), P e → P (stdRefl k e))
    (c : ℕ)
    (hlast : ∀ k : Fin m, ¬k.val + 1 < m → P (c • Pi.single k 1)) :
    ∀ d (b : Fin m), b.val + d + 1 = m → P (c • Pi.single b 1) := by
  intro d
  induction d with
  | zero =>
    intro b hb
    exact hlast b (by omega)
  | succ d ih =>
    intro b hb
    have hb1 : b.val + 1 < m := by omega
    have h := hP b _ (ih ⟨b.val + 1, hb1⟩ (by simp; omega))
    rwa [stdRefl_of_lt hb1, Pi.smul_comp, single_comp_swap, Equiv.swap_apply_right] at h

end Reach

private def Orb (n : ℕ) (e : Fin (n / 2) → ℤ) : Prop :=
  ∃ (w : (coxeterMatrix (isFiniteType_cartan n)).Group) (l : Fin (n / 2)),
    toStd n (weylAction (isFiniteType_cartan n) w (Pi.single l 1)) = e

private theorem orb_stdRefl {n : ℕ} (k : Fin (n / 2)) {e : Fin (n / 2) → ℤ} (h : Orb n e) :
    Orb n (stdRefl k e) := by
  obtain ⟨w, l, rfl⟩ := h
  exact ⟨(coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple k * w, l, by
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection]⟩

private theorem orb_neg {n : ℕ} {e : Fin (n / 2) → ℤ} (h : Orb n e) : Orb n (-e) := by
  obtain ⟨w, l, rfl⟩ := h
  exact ⟨w * (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple l, l, by
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg, toStd_neg]⟩

private theorem orb_toStd_single {n : ℕ} (l : Fin (n / 2)) : Orb n (toStd n (Pi.single l 1)) :=
  ⟨1, l, by rw [map_one, Module.End.one_apply]⟩

private theorem orb_sub {n : ℕ} {a b : Fin (n / 2)} (hab : a ≠ b) :
    Orb n (Pi.single a 1 - Pi.single b 1) :=
  reach_sub (Orb n) (fun k _ h => orb_stdRefl k h) (fun _ h => orb_neg h)
    (fun k h => by rw [← toStd_single_of_lt n h]; exact orb_toStd_single k) hab

private theorem orb_add {n : ℕ} {a b : Fin (n / 2)} (hab : a ≠ b) :
    Orb n (Pi.single a 1 + Pi.single b 1) :=
  reach_add (Orb n) (fun k _ h => orb_stdRefl k h) (fun _ h => orb_neg h)
    (fun k h => by rw [← toStd_single_of_lt n h]; exact orb_toStd_single k) hab

private theorem orb_two_smul {n : ℕ} (he : Even n) (b : Fin (n / 2)) :
    Orb n (2 • Pi.single b 1) :=
  reach_smul_single (Orb n) (fun k _ h => orb_stdRefl k h) 2
    (fun k h => by rw [← toStd_single_of_even he h]; exact orb_toStd_single k)
    (n / 2 - b.val - 1) b (by omega)

private def OrbL (n : ℕ) (e : Fin (n / 2) → ℤ) : Prop :=
  ∃ (w : (coxeterMatrix (isFiniteType_cartan n)).Group) (l : Fin (n / 2)), ¬l.val + 1 < n / 2 ∧
    toStd n (weylAction (isFiniteType_cartan n) w (Pi.single l 1)) = e

private theorem orbL_single {n : ℕ} (he : ¬Even n) (b : Fin (n / 2)) :
    OrbL n (Pi.single b 1) := by
  have h := reach_smul_single (OrbL n) (fun k e h => by
      obtain ⟨w, l, hl, rfl⟩ := h
      exact ⟨(coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple k * w, l, hl, by
        rw [weylAction_mul_apply, weylAction_simple, toStd_reflection]⟩) 1
    (fun k h => ⟨1, k, h, by
      rw [map_one, Module.End.one_apply, toStd_single_of_odd he h, one_smul]⟩)
    (n / 2 - b.val - 1) b (by omega)
  rwa [one_smul] at h

private theorem orbL_neg {n : ℕ} {e : Fin (n / 2) → ℤ} (h : OrbL n e) : OrbL n (-e) := by
  obtain ⟨w, l, hl, rfl⟩ := h
  exact ⟨w * (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple l, l, hl, by
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg, toStd_neg]⟩

private theorem orb_weight_sub {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) : Orb n (weight n i - weight n j) := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi <;> obtain ⟨b, rfl | rfl⟩ := exists_lowIdx hj
  · rw [weight_lowIdx, weight_lowIdx]
    exact orb_sub (by rintro rfl; exact hij rfl)
  · rw [weight_lowIdx, weight_rev_lowIdx, sub_neg_eq_add]
    exact orb_add (by rintro rfl; exact hji rfl)
  · rw [weight_rev_lowIdx, weight_lowIdx, ← neg_add']
    exact orb_neg (orb_add (by rintro rfl; exact hji (Fin.rev_rev _).symm))
  · rw [weight_rev_lowIdx, weight_rev_lowIdx, neg_sub_neg]
    exact orb_sub (by rintro rfl; exact hij rfl)

private theorem orb_two_smul_weight {n : ℕ} (he : Even n) {i : Fin n} (hi : i ≠ Fin.rev i) :
    Orb n (2 • weight n i) := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · rw [weight_lowIdx]
    exact orb_two_smul he a
  · rw [weight_rev_lowIdx, smul_neg]
    exact orb_neg (orb_two_smul he a)

private theorem orbL_weight {n : ℕ} (he : ¬Even n) {i : Fin n} (hi : i ≠ Fin.rev i) :
    OrbL n (weight n i) := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · rw [weight_lowIdx]
    exact orbL_single he a
  · rw [weight_rev_lowIdx]
    exact orbL_neg (orbL_single he a)

variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)

@[expose] noncomputable def rootGroup (n : ℕ) (γ : Fin (n / 2) → ℤ) : Subgroup (SU σ n) :=
  (⨆ (i : Fin n) (j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j)
      (_ : j ≠ Fin.rev i) (_ : weight n i - weight n j = toStd n γ),
      (rootHom σ hσ hij hi hj).range) ⊔
    (⨆ (i : Fin n) (hi : i ≠ Fin.rev i) (_ : 2 • weight n i = toStd n γ),
      (longRootHom σ hi).range) ⊔
    (⨆ (i : Fin n) (k : Fin n) (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
      (_ : weight n i = toStd n γ), heisenbergSubgroup σ hσ hi hik hk)

theorem roots_eq (n : ℕ) : roots (isFiniteType_cartan n) (divisible n) =
    {γ | (∃ i j : Fin n, i ≠ j ∧ i ≠ Fin.rev i ∧ j ≠ Fin.rev j ∧ j ≠ Fin.rev i ∧
        toStd n γ = weight n i - weight n j) ∨
      (∃ i : Fin n, i ≠ Fin.rev i ∧ toStd n γ = 2 • weight n i) ∨
      (¬ Even n ∧ ∃ i : Fin n, i ≠ Fin.rev i ∧ toStd n γ = weight n i)} := by
  ext γ
  constructor
  · rintro (⟨w, l, rfl⟩ | ⟨w, l, hl, rfl⟩)
    · exact isRootVec_toStd_weylAction w l
    · have hdiv : ¬Even n ∧ l.val + 1 = n / 2 := by
        unfold divisible at hl
        split_ifs at hl with he
        · exact absurd hl (Set.notMem_empty l)
        · exact ⟨he, hl⟩
      obtain ⟨i, hi, hw⟩ := exists_weight_toStd_weylAction hdiv.1 w (l := l) (by omega)
      exact Or.inr (Or.inl ⟨i, hi, by rw [toStd_nsmul, hw]⟩)
  · rintro (⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩)
    · obtain ⟨w, l, hw⟩ := orb_weight_sub hij hi hj hji
      exact Or.inl ⟨w, l, toStd_injective n (h.trans hw.symm)⟩
    · by_cases he : Even n
      · obtain ⟨w, l, hw⟩ := orb_two_smul_weight he hi
        exact Or.inl ⟨w, l, toStd_injective n (h.trans hw.symm)⟩
      · obtain ⟨w, l, hl, hw⟩ := orbL_weight he hi
        refine Or.inr ⟨w, l, ?_, toStd_injective n ?_⟩
        · simp only [divisible, he, ite_false, Set.mem_ofPred_eq]
          omega
        · rw [h, toStd_nsmul, hw]
    · obtain ⟨w, l, -, hw⟩ := orbL_weight he hi
      exact Or.inl ⟨w, l, toStd_injective n (h.trans hw.symm)⟩

section RootGroups

open CFSG.LieType.Universal.SpecialLinear

variable {σ} {n : ℕ}

private theorem rootHom_mem_rootGroup {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) {γ : Fin (n / 2) → ℤ}
    (hw : weight n i - weight n j = toStd n γ) (c : Multiplicative F) :
    rootHom σ hσ hij hi hj c ∈ rootGroup σ hσ n γ := by
  unfold rootGroup
  refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
  refine Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hij
    (Subgroup.mem_iSup_of_mem hi (Subgroup.mem_iSup_of_mem hj (Subgroup.mem_iSup_of_mem hji
      (Subgroup.mem_iSup_of_mem hw ⟨c, rfl⟩))))))

private theorem longRootHom_mem_rootGroup {i : Fin n} (hi : i ≠ Fin.rev i)
    {γ : Fin (n / 2) → ℤ} (hw : 2 • weight n i = toStd n γ) (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c ∈ rootGroup σ hσ n γ := by
  unfold rootGroup
  refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
  exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi (Subgroup.mem_iSup_of_mem hw
    ⟨c, rfl⟩))

private theorem heisenberg_le_rootGroup {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) {γ : Fin (n / 2) → ℤ} (hw : weight n i = toStd n γ) :
    heisenbergSubgroup σ hσ hi hik hk ≤ rootGroup σ hσ n γ := by
  unfold rootGroup
  refine le_trans ?_ le_sup_right
  exact le_iSup_of_le i (le_iSup_of_le k (le_iSup_of_le hi (le_iSup_of_le hik
    (le_iSup_of_le hk (le_iSup_of_le hw le_rfl)))))

private theorem longRootHom_mem_heisenberg {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c ∈ heisenbergSubgroup σ hσ hi hik hk := by
  refine ⟨0, (c.toAdd : F), ?_, ?_⟩
  · rw [map_zero, zero_mul, add_zero]
    exact c.toAdd.2
  · rw [coe_longRootHom, longRootMatrix, heisenbergMatrix]
    simp

private theorem conj_eq_of_coe {g x y : SU σ n}
    (h : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((x : GL (Fin n) F) : Matrix _ _ F) =
      ((y : GL (Fin n) F) : Matrix _ _ F) * ((g : GL (Fin n) F) : Matrix _ _ F)) :
    g * x * g⁻¹ = y := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Subtype.ext (Units.ext (by simpa only [Subgroup.coe_mul, Units.val_mul] using h))

private theorem middle_unique {p q : Fin n} (hp : Fin.rev p = p) (hq : Fin.rev q = q) : p = q := by
  have h1 := congrArg Fin.val hp
  have h2 := congrArg Fin.val hq
  simp only [Fin.val_rev] at h1 h2
  exact Fin.ext (by omega)

private theorem conj_mem_rootGroup (g : SU σ n) {π : Equiv.Perm (Fin n)} {d : Fin n → F}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = signedPerm π d)
    (hπ : ∀ s, π (Fin.rev s) = Fin.rev (π s)) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    {T : (Fin (n / 2) → ℤ) → (Fin (n / 2) → ℤ)} (hT : ∀ i, weight n (π i) = T (weight n i))
    (hTsub : ∀ x y, T (x - y) = T x - T y) (hT2 : ∀ x, T (2 • x) = 2 • T x)
    {γ γ' : Fin (n / 2) → ℤ} (hγ : T (toStd n γ) = toStd n γ') :
    ∀ x ∈ rootGroup σ hσ n γ, g * x * g⁻¹ ∈ rootGroup σ hσ n γ' := by
  have hπne : ∀ {i : Fin n}, i ≠ Fin.rev i → π i ≠ Fin.rev (π i) := fun hi => by
    rw [← hπ]
    exact π.injective.ne hi
  suffices h : rootGroup σ hσ n γ ≤ (rootGroup σ hσ n γ').comap (MulAut.conj g).toMonoidHom from
    fun x hx => h hx
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi => iSup_le fun hj =>
      iSup_le fun hji => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    have hji' : π j ≠ Fin.rev (π i) := by
      rw [← hπ]
      exact π.injective.ne hji
    have key := rootHom_mem_rootGroup hσ (π.injective.ne hij) (hπne hi) (hπne hj) hji'
      (γ := γ') (by rw [hT, hT, ← hTsub, hw, hγ])
      (Multiplicative.ofAdd (d i * c.toAdd * (d j)⁻¹))
    have hconj : g * rootHom σ hσ hij hi hj c * g⁻¹ = rootHom σ hσ (π.injective.ne hij) (hπne hi)
        (hπne hj) (Multiplicative.ofAdd (d i * c.toAdd * (d j)⁻¹)) := conj_eq_of_coe (by
      rw [hg, coe_rootHom, coe_rootHom, toAdd_ofAdd, signedPerm_mul_rootMatrix hπ hd])
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [hconj]
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    have key := longRootHom_mem_rootGroup hσ (hπne hi) (γ := γ') (by rw [hT, ← hT2, hw, hγ])
      (Multiplicative.ofAdd ⟨d i * (c.toAdd : F) * (d (Fin.rev i))⁻¹,
        (mem_traceZero σ).mpr
          (mul_mem_traceZero_of_unitary hd i ((mem_traceZero σ).mp c.toAdd.2))⟩)
    have hconj : g * longRootHom σ hi c * g⁻¹ = longRootHom σ (hπne hi)
        (Multiplicative.ofAdd ⟨d i * (c.toAdd : F) * (d (Fin.rev i))⁻¹,
          (mem_traceZero σ).mpr
          (mul_mem_traceZero_of_unitary hd i ((mem_traceZero σ).mp c.toAdd.2))⟩) :=
      conj_eq_of_coe (by
        rw [hg, coe_longRootHom, coe_longRootHom, toAdd_ofAdd, signedPerm_mul_longRootMatrix hπ hd])
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [hconj]
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    rintro x ⟨a, b, hab, hx⟩
    have hπk : π k = k := middle_unique (by rw [← hπ, hk]) hk
    have hik' : π i ≠ k := by
      rw [← hπk]
      exact π.injective.ne hik
    have hle := heisenberg_le_rootGroup hσ (hπne hi) hik' hk (γ := γ') (by rw [hT, hw, hγ])
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine hle ⟨d i * a * (d k)⁻¹, d i * b * (d (Fin.rev i))⁻¹,
      heisenberg_rel_of_unitary hd i hk hab, ?_⟩
    change ((g * x * g⁻¹ : SU σ n) : GL (Fin n) F).val = _
    have hxm : ((g * x : SU σ n) : GL (Fin n) F).val =
        heisenbergMatrix σ (π i) k (d i * a * (d k)⁻¹) (d i * b * (d (Fin.rev i))⁻¹) *
          ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [Subgroup.coe_mul, Units.val_mul, hx, hg, signedPerm_mul_heisenbergMatrix hπ hd i hk hπk]
    rw [Subgroup.coe_mul, Units.val_mul, hxm, Matrix.mul_assoc, ← Units.val_mul,
      ← Subgroup.coe_mul, mul_inv_cancel]
    simp

end RootGroups

section Weyl

open CFSG.LieType.Universal.SpecialLinear

variable {σ} {n : ℕ}

private theorem toStd_single_eq_weight_sub {k : Fin (n / 2)} (h : k.val + 1 < n / 2) :
    weight n (lowIdx k) - weight n (lowIdx ⟨k.val + 1, h⟩) = toStd n (Pi.single k 1) := by
  rw [weight_lowIdx, weight_lowIdx, toStd_single_of_lt n h]

private theorem shortWeyl_mem_rankOne {k : Fin (n / 2)} (h : k.val + 1 < n / 2) (c : F) :
    shortWeyl σ hσ (lowIdx_ne_succ h) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) c ∈
      CurtisTits.rankOne (rootGroup σ hσ n) k := by
  rw [shortWeyl_def]
  have h1 := fun c => rootHom_mem_rootGroup hσ (lowIdx_ne_succ h) (lowIdx_ne_rev k k)
    (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (toStd_single_eq_weight_sub h) c
  have h2 := fun c => rootHom_mem_rootGroup hσ (lowIdx_ne_succ h).symm (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (γ := -Pi.single k 1)
    (by rw [toStd_neg, ← toStd_single_eq_weight_sub h, neg_sub]) c
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (h1 _)) (Subgroup.mem_sup_right (h2 _)))
    (Subgroup.mem_sup_left (h1 _))

private theorem longRootHom_mem_rankOne {k : Fin (n / 2)} (h : ¬k.val + 1 < n / 2)
    (c : Multiplicative (traceZero σ)) :
    longRootHom σ (lowIdx_ne_rev k k) c ∈ CurtisTits.rankOne (rootGroup σ hσ n) k ∧
      longRootHom σ (rev_ne_rev_rev (lowIdx_ne_rev k k)) c ∈
        CurtisTits.rankOne (rootGroup σ hσ n) k := by
  by_cases he : Even n
  · refine ⟨Subgroup.mem_sup_left (longRootHom_mem_rootGroup hσ _ ?_ c),
      Subgroup.mem_sup_right (longRootHom_mem_rootGroup hσ _ ?_ c)⟩
    · rw [weight_lowIdx, toStd_single_of_even he h]
    · rw [weight_rev_lowIdx, toStd_neg, toStd_single_of_even he h, smul_neg]
  · set p : Fin n := ⟨n / 2, by omega⟩
    have hp : Fin.rev p = p := Fin.ext (by
      simp only [Fin.val_rev, p]
      rw [Nat.not_even_iff_odd] at he
      obtain ⟨r, hr⟩ := he
      omega)
    have hk := k.isLt
    have h1 : lowIdx k ≠ p := Fin.ne_of_val_ne (by simp only [lowIdx, p]; omega)
    have h2 : Fin.rev (lowIdx k) ≠ p := Fin.ne_of_val_ne (by
      simp only [Fin.val_rev, lowIdx, p]
      rw [Nat.not_even_iff_odd] at he
      obtain ⟨r, hr⟩ := he
      omega)
    refine ⟨Subgroup.mem_sup_left (heisenberg_le_rootGroup hσ _ h1 hp ?_
        (longRootHom_mem_heisenberg hσ _ h1 hp c)),
      Subgroup.mem_sup_right (heisenberg_le_rootGroup hσ _ h2 hp ?_
        (longRootHom_mem_heisenberg hσ _ h2 hp c))⟩
    · rw [weight_lowIdx, toStd_single_of_odd he h]
    · rw [weight_rev_lowIdx, toStd_neg, toStd_single_of_odd he h]

private theorem longWeyl_mem_rankOne {k : Fin (n / 2)} (h : ¬k.val + 1 < n / 2)
    (z : traceZero σ) :
    longWeyl σ (lowIdx_ne_rev k k) z ∈ CurtisTits.rankOne (rootGroup σ hσ n) k := by
  rw [longWeyl_def]
  exact mul_mem (mul_mem (longRootHom_mem_rankOne hσ h _).1 (longRootHom_mem_rankOne hσ h _).2)
    (longRootHom_mem_rankOne hσ h _).1

private theorem levelWeyl_mem_rankOne (ζ : traceZero σ) (k : Fin (n / 2)) :
    levelWeyl hσ ζ k ∈ CurtisTits.rankOne (rootGroup σ hσ n) k := by
  unfold levelWeyl
  by_cases h : k.val + 1 < n / 2
  · simp only [h, dite_true]
    exact shortWeyl_mem_rankOne hσ h 1
  · simp only [h, dite_false]
    exact longWeyl_mem_rankOne hσ h ζ

private theorem levelWeyl_conj_mem {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (k : Fin (n / 2))
    (γ : Fin (n / 2) → ℤ) (x : SU σ n) (hx : x ∈ rootGroup σ hσ n γ) :
    levelWeyl hσ ζ k * x * (levelWeyl hσ ζ k)⁻¹ ∈ rootGroup σ hσ n
      (weylAction (isFiniteType_cartan n)
        ((coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple k) γ) :=
  conj_mem_rootGroup hσ _ (coe_levelWeyl hσ hζ k) (levelPerm_rev k) (levelSign_unitary hσ hζ k)
    (weight_levelPerm k) (stdRefl_sub k) (stdRefl_nsmul k 2)
    (by rw [weylAction_simple, toStd_reflection]) x hx

end Weyl

section Braid

open CFSG.LieType.Universal.SpecialLinear

variable {σ} {n : ℕ}

private theorem cartan_mul_cartan (i j : Fin (n / 2)) :
    cartan n i j * cartan n j i = if i = j then 4
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
        (if i.val + 1 = n / 2 ∨ j.val + 1 = n / 2 then 2 else 1)
      else 0 := by
  have h : cartan n i j * cartan n j i =
      Symplectic.cartanC (n / 2) i j * Symplectic.cartanC (n / 2) j i := by
    unfold cartan
    split_ifs
    · rfl
    · simp only [Matrix.transpose_apply]
      ring
  rw [h]
  simp only [Symplectic.cartanC, Matrix.of_apply, Fin.ext_iff]
  have := i.isLt
  have := j.isLt
  split_ifs <;> omega

private theorem coxeterMatrix_eq (i j : Fin (n / 2)) :
    coxeterMatrix (isFiniteType_cartan n) i j =
      TauCeti.coxeterOrder (cartan n i j * cartan n j i) :=
  TauCeti.coxeterMatrixOfCartanMatrix_apply _ _ _ i j

private theorem coxeterMatrix_far {i j : Fin (n / 2)} (hij : i ≠ j)
    (h : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    coxeterMatrix (isFiniteType_cartan n) i j = 2 := by
  rw [coxeterMatrix_eq, cartan_mul_cartan, ite_eq_right hij, ite_eq_right h,
    TauCeti.coxeterOrder_zero]

private theorem coxeterMatrix_short {i j : Fin (n / 2)} (h : i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (hs : ¬(i.val + 1 = n / 2 ∨ j.val + 1 = n / 2)) :
    coxeterMatrix (isFiniteType_cartan n) i j = 3 := by
  have hij : i ≠ j := fun e => by subst e; omega
  rw [coxeterMatrix_eq, cartan_mul_cartan, ite_eq_right hij, ite_eq_left h, ite_eq_right hs,
    TauCeti.coxeterOrder_one]

private theorem coxeterMatrix_long {i j : Fin (n / 2)} (h : i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (hl : i.val + 1 = n / 2 ∨ j.val + 1 = n / 2) :
    coxeterMatrix (isFiniteType_cartan n) i j = 4 := by
  have hij : i ≠ j := fun e => by subst e; omega
  rw [coxeterMatrix_eq, cartan_mul_cartan, ite_eq_right hij, ite_eq_left h, ite_eq_left hl,
    TauCeti.coxeterOrder_two]

private theorem levelWeyl_braid {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (i j : Fin (n / 2)) :
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartan n)) i j).map
        (levelWeyl hσ ζ)).prod =
      ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartan n)) j i).map
        (levelWeyl hσ ζ)).prod := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  refine Subtype.ext (Units.ext ?_)
  rw [coe_prod_levelWeyl hσ hζ, coe_prod_levelWeyl hσ hζ]
  have := i.isLt
  have := j.isLt
  by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · by_cases hl : i.val + 1 = n / 2 ∨ j.val + 1 = n / 2
    · rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterMatrix_long hadj hl,
        coxeterMatrix_long hadj.symm hl.symm]
      show ([i, j, i, j].map _).prod = ([j, i, j, i].map _).prod
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rcases hadj with h | h
      · exact levelSign_braid_long _ h (by omega)
      · exact (levelSign_braid_long _ h (by omega)).symm
    · rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterMatrix_short hadj hl,
        coxeterMatrix_short hadj.symm fun h => hl h.symm]
      show ([j, i, j].map _).prod = ([i, j, i].map _).prod
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rcases hadj with h | h
      · exact levelSign_braid_short _ h (by omega)
      · exact (levelSign_braid_short _ h (by omega)).symm
  · rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterMatrix_far hij hadj,
      coxeterMatrix_far hij.symm fun h => hadj h.symm]
    show ([i, j].map _).prod = ([j, i].map _).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    exact signedPerm_comm_of_disjoint (levelSupp i) (levelSupp j)
      (fun s hs => eq_of_not_levelSupp _ hs) (fun s hs => eq_of_not_levelSupp _ hs)
      (fun s hs => levelSupp_levelPerm hs) (fun s hs => levelSupp_levelPerm hs)
      (fun s hs hs' => by unfold levelSupp at hs hs'; omega)

end Braid

section Torus

open CFSG.LieType.Universal.SpecialLinear

variable {σ} {n : ℕ}

private noncomputable def heisRootElt {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) : SU σ n :=
  ⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a),
    by
      rw [heisenbergMatrix_mul σ hi hik hk, map_neg, add_neg_cancel,
        show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero],
    by
      rw [heisenbergMatrix_mul σ hi hik hk, neg_add_cancel,
        show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]⟩,
    det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩

private theorem heisRootElt_mem {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) :
    heisRootElt hσ hi hik hk a b hab ∈ heisenbergSubgroup σ hσ hi hik hk :=
  ⟨a, b, hab, rfl⟩

theorem exists_heisGen_mem_rankOne {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2)
    (hn : ¬Even n) (t : Fˣ) :
    ∃ g ∈ CurtisTits.rankOne (rootGroup σ hσ n) k,
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        diagonal (heisTorusFun σ (lowIdx k) (t : F)) := by
  have hkl := k.isLt
  set p : Fin n := lowIdx k with hpdef
  set mid : Fin n := ⟨n / 2, by omega⟩ with hmiddef
  have hmid : Fin.rev mid = mid := Fin.ext (by
    simp only [Fin.val_rev, mid]
    rw [Nat.not_even_iff_odd] at hn
    obtain ⟨r, hr⟩ := hn
    omega)
  have hp : p ≠ Fin.rev p := lowIdx_ne_rev k k
  have hp' : Fin.rev p ≠ Fin.rev (Fin.rev p) := rev_ne_rev_rev hp
  have hpm : p ≠ mid := Fin.ne_of_val_ne (by simp only [p, mid, lowIdx]; omega)
  have hp'm : Fin.rev p ≠ mid := Fin.ne_of_val_ne (by
    simp only [Fin.val_rev, p, mid, lowIdx]
    rw [Nat.not_even_iff_odd] at hn
    obtain ⟨r, hr⟩ := hn
    omega)
  have hX : heisenbergSubgroup σ hσ hp hpm hmid ≤ CurtisTits.rankOne (rootGroup σ hσ n) k :=
    (heisenberg_le_rootGroup hσ hp hpm hmid (by
      rw [hpdef, weight_lowIdx, toStd_single_of_odd hn hk])).trans le_sup_left
  have hY : heisenbergSubgroup σ hσ hp' hp'm hmid ≤ CurtisTits.rankOne (rootGroup σ hσ n) k :=
    (heisenberg_le_rootGroup hσ hp' hp'm hmid (by
      rw [hpdef, weight_rev_lowIdx, toStd_neg, toStd_single_of_odd hn hk])).trans le_sup_right
  have hW : ∀ a b : F, b + σ b + σ a * a = 0 → b ≠ 0 →
      ∃ w ∈ CurtisTits.rankOne (rootGroup σ hσ n) k,
        ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          signedPerm (Equiv.swap p (Fin.rev p)) (heisSign σ p mid b) := by
    intro a b hab hb
    have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hb
    have h1 : (σ b)⁻¹ + σ (σ b)⁻¹ + σ (-a * (σ b)⁻¹) * (-a * (σ b)⁻¹) = 0 := by
      simp only [map_mul, map_neg, map_inv₀, hσ]
      field_simp
      linear_combination hab
    have h2 : (σ b)⁻¹ + σ (σ b)⁻¹ + σ (-a * b⁻¹) * (-a * b⁻¹) = 0 := by
      simp only [map_mul, map_neg, map_inv₀, hσ]
      field_simp
      linear_combination hab
    refine ⟨heisRootElt hσ hp' hp'm hmid _ _ h1 * heisRootElt hσ hp hpm hmid a b hab *
      heisRootElt hσ hp' hp'm hmid _ _ h2,
      mul_mem (mul_mem (hY (heisRootElt_mem hσ _ _ _ _ _ h1))
        (hX (heisRootElt_mem hσ _ _ _ _ _ hab))) (hY (heisRootElt_mem hσ _ _ _ _ _ h2)), ?_⟩
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact heisenbergMatrix_weyl hσ hp hpm hmid hab hb
  have hσζ : σ (ζ : F) = -ζ := by
    have := (mem_traceZero σ).mp ζ.2
    linear_combination this
  set b : F := -((t : F) * ζ) with hbdef
  have hb : b ≠ 0 := neg_ne_zero.mpr (mul_ne_zero t.ne_zero hζ)
  have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  obtain ⟨a, ha⟩ := hnorm (-(b + σ b)) (by rw [map_neg, map_add, hσ, add_comm])
  obtain ⟨w₁, hw₁, hw₁m⟩ := hW a b (by rw [ha]; ring) hb
  obtain ⟨w₂, hw₂, hw₂m⟩ := hW 0 ζ (by rw [map_zero, zero_mul, add_zero]; exact ζ.2) hζ
  refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, hw₁m, hw₂m, signedPerm_mul_signedPerm,
      Equiv.swap_mul_self, signedPerm_one]
    congr 1
    funext s
    have hpm' := hpm.symm
    have hp'm' := hp'm.symm
    have hpp' := hp.symm
    have ht0 : (t : F) ≠ 0 := t.ne_zero
    by_cases h1 : s = p
    · rw [h1]
      simp only [heisTorusFun, heisSign, Equiv.swap_apply_left, ite_true, hpp', hp'm, ite_false,
        hσζ, hbdef]
      field_simp
    by_cases h2 : s = Fin.rev p
    · rw [h2]
      simp only [heisTorusFun, heisSign, Equiv.swap_apply_right, ite_true, hpp', hp'm, hpm,
        ite_false, Fin.rev_rev, hσζ, hbdef, map_mul, map_neg]
      field_simp
    by_cases h3 : s = mid
    · rw [h3]
      simp only [heisTorusFun, heisSign, Equiv.swap_apply_of_ne_of_ne hpm' hp'm', ite_true,
        hpm', hp'm', ite_false, hmid, hσζ, hbdef, map_mul, map_neg]
      field_simp
    · have h4 : Fin.rev s ≠ s := fun h => h3 (by
        have := congrArg Fin.val h
        simp only [Fin.val_rev] at this
        exact Fin.ext (by simp only [mid]; omega))
      simp only [heisTorusFun, heisSign, Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2, h3, h4,
        ite_false, mul_one]

private theorem heisGen_mem_rankOne {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2)
    (hn : ¬Even n) (t : Fˣ) {g : SU σ n}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (heisTorusFun σ (lowIdx k) (t : F))) :
    g ∈ CurtisTits.rankOne (rootGroup σ hσ n) k := by
  obtain ⟨w, hw, hwm⟩ := exists_heisGen_mem_rankOne hσ hζ hnorm hk hn t
  rwa [show g = w from Subtype.ext (Units.ext (hg.trans hwm.symm))]

private theorem levelTorus_le_rankOne {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) (k : Fin (n / 2)) :
    levelTorus σ k ≤ CurtisTits.rankOne (rootGroup σ hσ n) k := by
  unfold levelTorus
  by_cases h : k.val + 1 < n / 2
  · rw [dite_eq_left h, Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    have : g = shortTorus σ hσ (lowIdx_ne_succ h) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) c :=
      Subtype.ext (Units.ext (by rw [hc, coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero]))
    rw [this, shortTorus_def]
    exact mul_mem (shortWeyl_mem_rankOne hσ h _) (shortWeyl_mem_rankOne hσ h _)
  · rw [dite_eq_right h]
    by_cases hn : Even n
    · rw [ite_eq_left hn, Subgroup.closure_le]
      rintro g ⟨e, he, hg⟩
      have : g = longTorus σ (lowIdx_ne_rev k k) ζ he :=
        Subtype.ext (Units.ext (by rw [hg, coe_longTorus σ _ hζ he e.ne_zero]))
      rw [this, longTorus_def]
      exact mul_mem (longWeyl_mem_rankOne hσ h _) (longWeyl_mem_rankOne hσ h _)
    · rw [ite_eq_right hn, Subgroup.closure_le]
      rintro g ⟨t, hg⟩
      exact heisGen_mem_rankOne hσ hζ hnorm h hn t hg

private theorem diag_conj_mem {h : SU σ n} (hh : h ∈ diagSubgroup σ n) (γ : Fin (n / 2) → ℤ)
    (x : SU σ n) (hx : x ∈ rootGroup σ hσ n γ) : h * x * h⁻¹ ∈ rootGroup σ hσ n γ := by
  obtain ⟨t, ht⟩ := hh
  exact conj_mem_rootGroup hσ h (π := 1) (d := t) (by rw [ht, signedPerm_one])
    (fun _ => rfl) (unitary_of_coe_eq_diagonal ht) (T := id) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) rfl x hx

end Torus

section RankOne

variable {σ} {n : ℕ}

omit hσ in
private theorem weight_apply_mem (i : Fin n) (a : Fin (n / 2)) :
    weight n i a = 1 ∨ weight n i a = 0 ∨ weight n i a = -1 := by
  rw [weight_apply]
  split_ifs <;> simp

omit hσ in
private theorem weight_sub_apply_mem {p q : Fin n} (hqp : q ≠ Fin.rev p) (a : Fin (n / 2)) :
    (weight n p - weight n q) a = 1 ∨ (weight n p - weight n q) a = 0 ∨
      (weight n p - weight n q) a = -1 := by
  have hqp' : q.val ≠ n - 1 - p.val := fun h => hqp (Fin.ext (by simp only [Fin.val_rev]; omega))
  have := p.isLt
  have := q.isLt
  rw [Pi.sub_apply, weight_apply, weight_apply]
  split_ifs <;> omega

omit hσ in
private theorem eq_of_weight_ne_zero {p : Fin n} {a b : Fin (n / 2)} (ha : weight n p a ≠ 0)
    (hb : weight n p b ≠ 0) : a = b := by
  rw [weight_apply] at ha hb
  refine Fin.ext ?_
  split_ifs at ha hb <;> simp_all <;> omega

omit hσ in
private theorem eq_of_smul_mem_roots {i : Fin (n / 2)} {c : ℤ}
    (h : c • Pi.single i 1 ∈ roots (isFiniteType_cartan n) (divisible n)) :
    c = 1 ∨ c = -1 ∨ (¬Even n ∧ ¬i.val + 1 < n / 2 ∧ (c = 2 ∨ c = -2)) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ne_zero_of_mem_roots _ _ h (zero_smul _ _)
  rw [roots_eq] at h
  have he : ∀ a, toStd n (c • Pi.single i 1) a = c * toStd n (Pi.single i 1) a := fun a => by
    rw [toStd_zsmul]
    rfl
  by_cases hl : i.val + 1 < n / 2
  · set i' : Fin (n / 2) := ⟨i.val + 1, hl⟩
    have hii' : i ≠ i' := Fin.ne_of_val_ne (by simp [i'])
    have h1 : toStd n (c • Pi.single i 1) i = c := by
      rw [he, toStd_single_of_lt n hl]
      simp [Fin.ext_iff]
    have h2 : toStd n (c • Pi.single i 1) i' = -c := by
      rw [he, toStd_single_of_lt n hl]
      simp [Fin.ext_iff, i']
    rcases h with ⟨p, q, -, -, -, hqp, heq⟩ | ⟨p, -, heq⟩ | ⟨-, p, -, heq⟩
    · have := weight_sub_apply_mem hqp i
      rw [← heq, h1] at this
      omega
    · rw [heq] at h1 h2
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1 h2
      exact absurd (eq_of_weight_ne_zero (p := p) (fun h => hc0 (by rw [← h1, h, mul_zero]))
        (fun h => hc0 (by rw [← neg_eq_zero, ← h2, h, mul_zero]))) hii'
    · rw [heq] at h1 h2
      exact absurd (eq_of_weight_ne_zero (p := p) (fun h => hc0 (by rw [← h1, h]))
        (fun h => hc0 (by rw [← neg_eq_zero, ← h2, h]))) hii'
  · by_cases hev : Even n
    · have h1 : toStd n (c • Pi.single i 1) i = 2 * c := by
        rw [he, toStd_single_of_even hev hl]
        simp [mul_comm]
      rcases h with ⟨p, q, -, -, -, hqp, heq⟩ | ⟨p, -, heq⟩ | ⟨hne, -⟩
      · have := weight_sub_apply_mem hqp i
        rw [← heq, h1] at this
        omega
      · rw [heq] at h1
        simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        have := weight_apply_mem p i
        omega
      · exact absurd hev hne
    · have h1 : toStd n (c • Pi.single i 1) i = c := by
        rw [he, toStd_single_of_odd hev hl]
        simp
      rcases h with ⟨p, q, -, -, -, hqp, heq⟩ | ⟨p, -, heq⟩ | ⟨-, p, -, heq⟩
      · have := weight_sub_apply_mem hqp i
        rw [← heq, h1] at this
        omega
      · rw [heq] at h1
        simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        have := weight_apply_mem p i
        right; right
        exact ⟨hev, hl, by omega⟩
      · rw [heq] at h1
        have := weight_apply_mem p i
        omega

private theorem rootGroup_two_smul_le (he : ¬Even n) {γ₀ : Fin (n / 2) → ℤ} {p : Fin n}
    (hp : p ≠ Fin.rev p) (hγ₀ : toStd n γ₀ = weight n p) :
    rootGroup σ hσ n ((2 : ℤ) • γ₀) ≤ rootGroup σ hσ n γ₀ := by
  have h2 : toStd n ((2 : ℤ) • γ₀) = 2 • weight n p := by
    rw [toStd_zsmul, hγ₀, two_zsmul, two_nsmul]
  obtain ⟨a, ha⟩ : ∃ a, weight n p a ≠ 0 := by
    obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hp
    · exact ⟨a, by rw [weight_lowIdx]; simp⟩
    · exact ⟨a, by rw [weight_rev_lowIdx]; simp⟩
  have hpa := weight_apply_mem p a
  set mid : Fin n := ⟨n / 2, by omega⟩
  have hmid : Fin.rev mid = mid := Fin.ext (by
    simp only [Fin.val_rev, mid]
    rw [Nat.not_even_iff_odd] at he
    obtain ⟨r, hr⟩ := he
    omega)
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hji => iSup_le fun hw => ?_
    have := weight_sub_apply_mem hji a
    rw [hw, h2] at this
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
    omega
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rw [h2] at hw
    have hw' : weight n i = weight n p := by
      funext b
      have := congrFun hw b
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
      omega
    have hw0 : weight n mid a = 0 := by
      have hmv : mid.val = n / 2 := rfl
      have ho : n % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
      rw [weight_apply, hmv]
      have := a.isLt
      split_ifs <;> omega
    have hik : i ≠ mid := fun h => ha (by rw [← congrFun hw' a, h, hw0])
    rintro _ ⟨c, rfl⟩
    exact heisenberg_le_rootGroup hσ hi hik hmid (by rw [hw', hγ₀])
      (longRootHom_mem_heisenberg hσ hi hik hmid c)
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hw => ?_
    have := congrFun hw a
    rw [h2] at this
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
    have := weight_apply_mem i a
    omega

private theorem rootGroup_le_rankOne (i : Fin (n / 2)) (γ : Fin (n / 2) → ℤ)
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) (hsupp : ∀ k, k ≠ i → γ k = 0) :
    rootGroup σ hσ n γ ≤ CurtisTits.rankOne (rootGroup σ hσ n) i := by
  have hγi : γ = γ i • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hsupp k hk, hk]
  rw [hγi] at hγ
  rcases eq_of_smul_mem_roots hγ with h | h | ⟨he, hl, h | h⟩
  · rw [hγi, h, one_smul]
    exact le_sup_left
  · rw [hγi, h, neg_one_zsmul]
    exact le_sup_right
  · rw [hγi, h]
    exact (rootGroup_two_smul_le hσ he (lowIdx_ne_rev i i)
      (by rw [toStd_single_of_odd he hl, weight_lowIdx])).trans le_sup_left
  · rw [hγi, h, show (-2 : ℤ) • (Pi.single i 1 : Fin (n / 2) → ℤ) =
      (2 : ℤ) • -(Pi.single i 1 : Fin (n / 2) → ℤ) by rw [smul_neg, neg_smul]]
    exact (rootGroup_two_smul_le hσ he (rev_ne_rev_rev (lowIdx_ne_rev i i))
      (by rw [toStd_neg, toStd_single_of_odd he hl, weight_rev_lowIdx])).trans le_sup_right

end RankOne

section Generation

variable {σ} {n : ℕ}

private theorem mem_iSup_rootGroup {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n γ) :
    x ∈ ⨆ γ ∈ roots (isFiniteType_cartan n) (divisible n), rootGroup σ hσ n γ :=
  Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ hx)

private theorem iSup_rootGroup_eq_top (hζ : ∃ ζ : F, ζ ≠ 0 ∧ ζ + σ ζ = 0)
    (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x)
    (hn : 2 ≤ n) :
    ⨆ γ ∈ roots (isFiniteType_cartan n) (divisible n), rootGroup σ hσ n γ = ⊤ := by
  refine eq_top_of_rootElements_le hσ hζ htr hnorm hn _ ?_ ?_ ?_
  · intro i j hij hi hj hji c
    obtain ⟨w, l, hw⟩ := orb_weight_sub hij hi hj hji
    exact mem_iSup_rootGroup hσ (Or.inl ⟨w, l, rfl⟩)
      (rootHom_mem_rootGroup hσ hij hi hj hji hw.symm c)
  · intro i hi c
    by_cases he : Even n
    · obtain ⟨w, l, hw⟩ := orb_two_smul_weight he hi
      exact mem_iSup_rootGroup hσ (Or.inl ⟨w, l, rfl⟩)
        (longRootHom_mem_rootGroup hσ hi hw.symm c)
    · obtain ⟨w, l, hl, hw⟩ := orbL_weight he hi
      have hdiv : l ∈ divisible n := by
        simp only [divisible, he, ite_false, Set.mem_ofPred_eq]
        omega
      exact mem_iSup_rootGroup hσ (Or.inr ⟨w, l, hdiv, rfl⟩)
        (longRootHom_mem_rootGroup hσ hi (by rw [toStd_nsmul, hw]) c)
  · intro i k hi hik hk x hx
    have he : ¬Even n := by
      rintro ⟨r, hr⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_rev] at this
      omega
    obtain ⟨w, l, -, hw⟩ := orbL_weight he hi
    exact mem_iSup_rootGroup hσ (Or.inl ⟨w, l, rfl⟩)
      (heisenberg_le_rootGroup hσ hi hik hk hw.symm hx)

end Generation

section Finite

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] [CharP F p] in
private theorem one_lt_pow_of_card (hF : Nat.card F = (p ^ f) ^ 2) : 1 < p ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have : p ^ f ≤ 1 := not_lt.mp h
  nlinarith [Nat.zero_le (p ^ f)]

private theorem exists_norm_eq (hF : Nat.card F = (p ^ f) ^ 2) {x : F}
    (hx : unitaryInvolution F p f x = x) : ∃ a, unitaryInvolution F p f a * a = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  have hq := one_lt_pow_of_card hF
  have := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  set u := Units.mk0 x hx0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = u := (mem_powers_iff_mem_zpowers.mpr (hg u))
  have huq : u ^ (p ^ f) = u := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← unitaryInvolution_apply, hx])
  have h1 : g ^ (k * (p ^ f - 1)) = 1 := by
    rw [pow_mul, hk]
    have : u ^ (p ^ f - 1) * u = u := by rw [← pow_succ, Nat.sub_add_cancel hq.le, huq]
    exact mul_eq_right.mp this
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hord, show (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) by
    have h1 : 1 ≤ p ^ f := hq.le
    zify [h1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
    ring] at hdvd
  obtain ⟨j, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd
  refine ⟨((g ^ j : Fˣ) : F), ?_⟩
  rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm,
    hk, Units.val_mk0]

theorem isCTGroupDatum (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0) :
    CFSG.LieType.CurtisTits.IsCTGroupDatum
      (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem
      (weylAction (isFiniteType_cartan n)) (roots (isFiniteType_cartan n) (divisible n))
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n)
      (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F p f)) := by
  have hσ := unitaryInvolution_involutive hF
  exact
    { n_mem := levelWeyl_mem_rankOne hσ ζ
      conj_mem := fun k γ _ x hx => levelWeyl_conj_mem hσ hζ k γ x hx
      braid := levelWeyl_braid hσ hζ
      H_le := levelTorus_le_rankOne hσ hζ fun _ hx => exists_norm_eq hF hx
      sq_mem := levelWeyl_sq_mem hσ hζ
      H_conj_mem := fun k γ _ h hh x hx => diag_conj_mem hσ (levelTorus_le_diagSubgroup k hh) γ x hx
      conj_H_mem := fun j k h hh => levelWeyl_conj_levelTorus hσ hζ j k h hh
      le_rankOne := fun i γ hγ hsupp => rootGroup_le_rankOne hσ i γ hγ hsupp
      iSup_eq_top := iSup_rootGroup_eq_top hσ ⟨ζ, hζ, ζ.2⟩
        (fun _ hx => exists_add_unitaryInvolution_eq hF hx) (fun _ hx => exists_norm_eq hF hx)
        hn }

theorem exists_traceZero_ne_zero (hF : Nat.card F = (p ^ f) ^ 2) :
    ∃ ζ : traceZero (unitaryInvolution F p f), (ζ : F) ≠ 0 := by
  obtain ⟨z, hz0, hz⟩ := exists_unitaryInvolution_eq_neg hF
  exact ⟨⟨z, by rw [mem_traceZero, hz, add_neg_cancel]⟩, hz0⟩

theorem exists_isCTGroupDatum (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (w : Fin (n / 2) → SU (unitaryInvolution F p f) n)
      (H : Fin (n / 2) → Subgroup (SU (unitaryInvolution F p f) n)),
      CFSG.LieType.CurtisTits.IsCTGroupDatum
        (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem
        (weylAction (isFiniteType_cartan n)) (roots (isFiniteType_cartan n) (divisible n))
        (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) w H := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨z, hz0, hz⟩ := exists_unitaryInvolution_eq_neg hF
  have hzt : z + unitaryInvolution F p f z = 0 := by rw [hz, add_neg_cancel]
  set ζ : traceZero (unitaryInvolution F p f) := ⟨z, hzt⟩
  have hζ : (ζ : F) ≠ 0 := hz0
  exact ⟨levelWeyl hσ ζ, levelTorus (unitaryInvolution F p f),
    { n_mem := levelWeyl_mem_rankOne hσ ζ
      conj_mem := fun k γ _ x hx => levelWeyl_conj_mem hσ hζ k γ x hx
      braid := levelWeyl_braid hσ hζ
      H_le := levelTorus_le_rankOne hσ hζ fun _ hx => exists_norm_eq hF hx
      sq_mem := levelWeyl_sq_mem hσ hζ
      H_conj_mem := fun k γ _ h hh x hx => diag_conj_mem hσ (levelTorus_le_diagSubgroup k hh) γ x hx
      conj_H_mem := fun j k h hh => levelWeyl_conj_levelTorus hσ hζ j k h hh
      le_rankOne := fun i γ hγ hsupp => rootGroup_le_rankOne hσ i γ hγ hsupp
      iSup_eq_top := iSup_rootGroup_eq_top hσ ⟨z, hz0, hzt⟩
        (fun _ hx => exists_add_unitaryInvolution_eq hF hx) (fun _ hx => exists_norm_eq hF hx)
        hn }⟩

end Finite

end CFSG.LieType.Universal.Unitary
