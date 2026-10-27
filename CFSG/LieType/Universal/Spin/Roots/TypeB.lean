module

public import CFSG.LieType.RootSystem.Basic
public import CFSG.LieType.Steinberg.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

public section

namespace CFSG.LieType.Universal.Spin

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

@[expose] def cartanB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
  if i = j then 2
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
    (if i.val + 1 = n ∧ j.val + 2 = n then -2 else -1)
  else 0

theorem cartanB_eq (n : ℕ) : cartanB n = CartanMatrix.C n := by
  ext i j
  simp only [cartanB, CartanMatrix.C, Matrix.of_apply]
  split_ifs <;> omega

theorem cartanB_eq_transpose (n : ℕ) : cartanB n = (CartanMatrix.B n)ᵀ := by
  rw [cartanB_eq, CartanMatrix.B_transpose]

theorem isFiniteType_cartanB (n : ℕ) : TauCeti.IsFiniteType (cartanB n) := by
  rw [cartanB_eq]
  exact TauCeti.isFiniteType_cartanMatrix_C n

@[expose] def toStdB (n : ℕ) (v : Fin n → ℤ) : Fin n → ℤ := fun a =>
  v a - (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0)

@[expose] def ofStdB (n : ℕ) (e : Fin n → ℤ) : Fin n → ℤ := fun a =>
  ∑ b : Fin n, if b.val ≤ a.val then e b else 0

@[expose] def stdReflB (n : ℕ) (k : Fin n) (e : Fin n → ℤ) : Fin n → ℤ :=
  if h : k.val + 1 < n then e ∘ Equiv.swap k ⟨k.val + 1, h⟩
  else fun a => (if a = k then -1 else 1) * e a

variable (n : ℕ)

private def toStdBLin : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := toStdB n
  map_add' v w := by
    funext a
    simp only [toStdB, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext a
    simp only [toStdB, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private theorem toStdBLin_apply (v : Fin n → ℤ) : toStdBLin n v = toStdB n v := rfl

theorem toStdB_zero : toStdB n 0 = 0 :=
  map_zero (toStdBLin n)

theorem toStdB_add (v w : Fin n → ℤ) : toStdB n (v + w) = toStdB n v + toStdB n w :=
  map_add (toStdBLin n) v w

theorem toStdB_sub (v w : Fin n → ℤ) : toStdB n (v - w) = toStdB n v - toStdB n w :=
  map_sub (toStdBLin n) v w

theorem toStdB_neg (v : Fin n → ℤ) : toStdB n (-v) = -toStdB n v :=
  map_neg (toStdBLin n) v

theorem toStdB_smul (c : ℤ) (v : Fin n → ℤ) : toStdB n (c • v) = c • toStdB n v :=
  map_zsmul (toStdBLin n) c v

theorem toStdB_single_of_lt {k : Fin n} (h : k.val + 1 < n) :
    toStdB n (Pi.single k 1) = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 := by
  funext a
  simp only [toStdB, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem toStdB_single_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) :
    toStdB n (Pi.single k 1) = Pi.single k 1 := by
  funext a
  simp only [toStdB, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem toStdB_apply_eq (v : Fin n → ℤ) (k : Fin n) :
    toStdB n v k = v k - (if h : 0 < k.val then v ⟨k.val - 1, by omega⟩ else 0) := rfl

theorem toStdB_injective : Function.Injective (toStdB n) := by
  intro v w h
  have key : ∀ d (k : Fin n), k.val = d → v k = w k := by
    intro d
    induction d with
    | zero =>
      intro k hk
      have := congrFun h k
      rw [toStdB_apply_eq, toStdB_apply_eq, dite_eq_right (by omega),
        dite_eq_right (by omega)] at this
      linarith
    | succ d ih =>
      intro k hk
      have := congrFun h k
      rw [toStdB_apply_eq, toStdB_apply_eq, dite_eq_left (by omega), dite_eq_left (by omega),
        ih ⟨k.val - 1, by omega⟩ (by simp only; omega)] at this
      linarith
  funext k
  exact key k.val k rfl

theorem toStdB_ofStdB (e : Fin n → ℤ) : toStdB n (ofStdB n e) = e := by
  funext a
  rw [toStdB_apply_eq]
  by_cases ha : 0 < a.val
  · rw [dite_eq_left ha]
    simp only [ofStdB]
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single a]
    · rw [ite_eq_left (le_refl _), ite_eq_right (show ¬a.val ≤ a.val - 1 by omega), sub_zero]
    · intro b hb
      have hb' : b.val ≠ a.val := fun e => hb (Fin.ext e)
      split_ifs <;> omega
  · rw [dite_eq_right ha, sub_zero]
    simp only [ofStdB]
    rw [Fintype.sum_eq_single a]
    · rw [ite_eq_left (le_refl _)]
    · intro b hb
      have hb' : b.val ≠ a.val := fun e => hb (Fin.ext e)
      rw [ite_eq_right (by omega)]

theorem ofStdB_toStdB (v : Fin n → ℤ) : ofStdB n (toStdB n v) = v :=
  toStdB_injective n (toStdB_ofStdB n (toStdB n v))

theorem toStdB_eq_iff (v e : Fin n → ℤ) : toStdB n v = e ↔ v = ofStdB n e := by
  constructor
  · rintro rfl
    exact (ofStdB_toStdB n v).symm
  · rintro rfl
    exact toStdB_ofStdB n e

theorem stdReflB_of_lt {k : Fin n} (h : k.val + 1 < n) (e : Fin n → ℤ) :
    stdReflB n k e = e ∘ Equiv.swap k ⟨k.val + 1, h⟩ := dite_eq_left h

theorem stdReflB_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (e : Fin n → ℤ) :
    stdReflB n k e = fun a => (if a = k then -1 else 1) * e a := dite_eq_right h

theorem coroot_cartanB_of_lt {k : Fin n} (h : k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (cartanB n) k v = toStdB n v k - toStdB n v ⟨k.val + 1, h⟩ := by
  have key : coroot (cartanB n) k =
      ((LinearMap.proj k : (Fin n → ℤ) →ₗ[ℤ] ℤ) - LinearMap.proj (⟨k.val + 1, h⟩ : Fin n)).comp
        (toStdBLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdBLin_apply, toStdB, cartanB, Matrix.of_apply,
      Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

theorem coroot_cartanB_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (cartanB n) k v = 2 * toStdB n v k := by
  have key : coroot (cartanB n) k = (2 : ℤ) • (LinearMap.proj k).comp (toStdBLin n) := by
    ext l
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdBLin_apply, toStdB, cartanB, Matrix.of_apply,
      Pi.single_apply, Fin.ext_iff, smul_eq_mul]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

theorem toStdB_reflection (k : Fin n) (v : Fin n → ℤ) :
    toStdB n (reflection (cartanB n) k v) = stdReflB n k (toStdB n v) := by
  rw [reflection_apply_coroot, toStdB_sub, toStdB_smul]
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanB_of_lt n h, toStdB_single_of_lt n h, stdReflB_of_lt n h]
    have hne : (⟨k.val + 1, h⟩ : Fin n) ≠ k := Fin.ne_of_val_ne (by simp)
    funext a
    by_cases ha : a = k
    · subst ha
      simp [Ne.symm hne]
    by_cases ha' : a = ⟨k.val + 1, h⟩
    · subst ha'
      simp [hne]
    · simp [ha, ha', Equiv.swap_apply_of_ne_of_ne ha ha']
  · rw [coroot_cartanB_of_not_lt n h, toStdB_single_of_not_lt n h, stdReflB_of_not_lt n h]
    funext a
    by_cases ha : a = k
    · subst ha
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, ite_true]
      ring
    · simp [ha]

theorem toStdB_reflection_of_lt {k : Fin n} (h : k.val + 1 < n) (v : Fin n → ℤ) :
    toStdB n (reflection (cartanB n) k v) = toStdB n v ∘ Equiv.swap k ⟨k.val + 1, h⟩ := by
  rw [toStdB_reflection, stdReflB_of_lt n h]

theorem toStdB_reflection_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (v : Fin n → ℤ) :
    toStdB n (reflection (cartanB n) k v) = Function.update (toStdB n v) k (-toStdB n v k) := by
  rw [toStdB_reflection, stdReflB_of_not_lt n h]
  funext a
  by_cases ha : a = k
  · subst ha
    simp
  · simp [ha]

private theorem stdReflB_of_succ {k k' : Fin n} (h : k.val + 1 = k'.val) (e : Fin n → ℤ) :
    stdReflB n k e = e ∘ Equiv.swap k k' := by
  rw [stdReflB_of_lt n (by omega)]
  congr 3
  exact Fin.ext h

private theorem single_comp_swap (a p q : Fin n) (x : ℤ) :
    Pi.single a x ∘ Equiv.swap p q = Pi.single (Equiv.swap p q a) x := by
  rw [Pi.single_comp_equiv, Equiv.symm_swap]

private theorem mul_single (f : Fin n → ℤ) (a : Fin n) (x : ℤ) :
    (fun b => f b * (Pi.single a x : Fin n → ℤ) b) = Pi.single a (f a * x) := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [hb]

private theorem sign_mul {u : ℤ} (hu : u = 1 ∨ u = -1) (c : ℤ) (hc : c = 1 ∨ c = -1) :
    c * u = 1 ∨ c * u = -1 := by
  rcases hc with rfl | rfl <;> rcases hu with rfl | rfl <;> simp

private def IsStdRootB (e : Fin n → ℤ) : Prop :=
  (∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      e = Pi.single i s + Pi.single j t) ∨
    ∃ (i : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ e = Pi.single i s

private theorem isStdRootB_toStdB_single (k : Fin n) :
    IsStdRootB n (toStdB n (Pi.single k 1)) := by
  by_cases h : k.val + 1 < n
  · refine Or.inl ⟨k, ⟨k.val + 1, h⟩, 1, -1, Fin.ne_of_val_ne (by simp), Or.inl rfl, Or.inr rfl,
      ?_⟩
    rw [toStdB_single_of_lt n h, sub_eq_add_neg, Pi.single_neg]
  · exact Or.inr ⟨k, 1, Or.inl rfl, toStdB_single_of_not_lt n h⟩

private theorem isStdRootB_stdReflB (k : Fin n) {e : Fin n → ℤ} (he : IsStdRootB n e) :
    IsStdRootB n (stdReflB n k e) := by
  by_cases h : k.val + 1 < n
  · rw [stdReflB_of_lt n h]
    rcases he with ⟨a, b, s, t, hab, hs, ht, rfl⟩ | ⟨a, s, hs, rfl⟩
    · refine Or.inl ⟨Equiv.swap k ⟨k.val + 1, h⟩ a, Equiv.swap k ⟨k.val + 1, h⟩ b, s, t,
        (Equiv.swap _ _).injective.ne hab, hs, ht, ?_⟩
      rw [Pi.add_comp, single_comp_swap, single_comp_swap]
    · exact Or.inr ⟨Equiv.swap k ⟨k.val + 1, h⟩ a, s, hs, single_comp_swap n _ _ _ _⟩
  · rw [stdReflB_of_not_lt n h]
    have hsgn : ∀ c : Fin n, (if c = k then (-1 : ℤ) else 1) = 1 ∨
        (if c = k then (-1 : ℤ) else 1) = -1 := fun c => by
      split_ifs <;> simp
    rcases he with ⟨a, b, s, t, hab, hs, ht, rfl⟩ | ⟨a, s, hs, rfl⟩
    · refine Or.inl ⟨a, b, (if a = k then -1 else 1) * s, (if b = k then -1 else 1) * t, hab,
        sign_mul hs _ (hsgn a), sign_mul ht _ (hsgn b), ?_⟩
      funext x
      simp only [Pi.add_apply, mul_add]
      congr 1
      · exact congrFun (mul_single n (fun c => if c = k then -1 else 1) a s) x
      · exact congrFun (mul_single n (fun c => if c = k then -1 else 1) b t) x
    · exact Or.inr ⟨a, (if a = k then -1 else 1) * s, sign_mul hs _ (hsgn a),
        mul_single n (fun c => if c = k then -1 else 1) a s⟩

private theorem isStdRootB_toStdB_weylAction (w : (coxeterMatrix (isFiniteType_cartanB n)).Group)
    (k : Fin n) :
    IsStdRootB n (toStdB n (weylAction (isFiniteType_cartanB n) w (Pi.single k 1))) := by
  induction w using (coxeterMatrix (isFiniteType_cartanB n)).toCoxeterSystem.simple_induction_left
    with
  | one => simpa using isStdRootB_toStdB_single n k
  | mul_simple_left w l ih =>
    rw [weylAction_mul_apply, weylAction_simple, toStdB_reflection]
    exact isStdRootB_stdReflB n l ih

private def IsStdOrbitB (e : Fin n → ℤ) : Prop :=
  ∃ (w : (coxeterMatrix (isFiniteType_cartanB n)).Group) (k : Fin n),
    toStdB n (weylAction (isFiniteType_cartanB n) w (Pi.single k 1)) = e

private theorem isStdOrbitB_toStdB_single (k : Fin n) :
    IsStdOrbitB n (toStdB n (Pi.single k 1)) :=
  ⟨1, k, by rw [map_one, Module.End.one_apply]⟩

private theorem IsStdOrbitB.neg {e : Fin n → ℤ} (he : IsStdOrbitB n e) : IsStdOrbitB n (-e) := by
  obtain ⟨w, k, rfl⟩ := he
  refine ⟨w * (coxeterMatrix (isFiniteType_cartanB n)).toCoxeterSystem.simple k, k, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple_single, map_neg, toStdB_neg]

private theorem IsStdOrbitB.stdReflB {e : Fin n → ℤ} (he : IsStdOrbitB n e) (k : Fin n) :
    IsStdOrbitB n (stdReflB n k e) := by
  obtain ⟨w, l, rfl⟩ := he
  refine ⟨(coxeterMatrix (isFiniteType_cartanB n)).toCoxeterSystem.simple k * w, l, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple, toStdB_reflection]

private theorem isStdOrbitB_difference (d : ℕ) :
    ∀ i j : Fin n, j.val = i.val + 1 + d → IsStdOrbitB n (Pi.single i 1 - Pi.single j 1) := by
  induction d with
  | zero =>
    intro i j hij
    have h : i.val + 1 < n := by omega
    have e : (⟨i.val + 1, h⟩ : Fin n) = j := Fin.ext (by simp only; omega)
    simpa [toStdB_single_of_lt n h, e] using isStdOrbitB_toStdB_single n i
  | succ d ih =>
    intro i j hij
    have hj' : i.val + 1 + d < n := by omega
    have h := (ih i ⟨i.val + 1 + d, hj'⟩ rfl).stdReflB n ⟨i.val + 1 + d, hj'⟩
    rw [stdReflB_of_succ n (k' := j) (by simp only; omega), Pi.sub_comp, single_comp_swap,
      single_comp_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp only; omega))
        (Fin.ne_of_val_ne (by omega))] at h
    exact h

private theorem isStdOrbitB_short (d : ℕ) :
    ∀ a : Fin n, a.val + d + 1 = n → IsStdOrbitB n (Pi.single a 1) := by
  induction d with
  | zero =>
    intro a ha
    simpa [toStdB_single_of_not_lt n (show ¬a.val + 1 < n by omega)] using
      isStdOrbitB_toStdB_single n a
  | succ d ih =>
    intro a ha
    have ha' : a.val + 1 < n := by omega
    have h := (ih ⟨a.val + 1, ha'⟩ (by simp only; omega)).stdReflB n a
    rw [stdReflB_of_succ n (k' := ⟨a.val + 1, ha'⟩) rfl, single_comp_swap,
      Equiv.swap_apply_right] at h
    exact h

private theorem isStdOrbitB_positiveSum (d : ℕ) :
    ∀ i j : Fin n, i < j → j.val + d + 1 = n →
      IsStdOrbitB n (Pi.single i 1 + Pi.single j 1) := by
  induction d with
  | zero =>
    intro i j hij hj
    have h := (isStdOrbitB_difference n (j.val - i.val - 1) i j (by
      have : i.val < j.val := hij
      omega)).stdReflB n j
    rw [stdReflB_of_not_lt n (by omega)] at h
    convert h using 1
    have hij' : i ≠ j := hij.ne
    funext x
    by_cases hx : x = j
    · subst hx
      simp [hij'.symm]
    · by_cases hx' : x = i
      · subst hx'
        simp [hij']
      · simp [hx, hx']
  | succ d ih =>
    intro i j hij hj
    have hj' : j.val + 1 < n := by omega
    have h := (ih i ⟨j.val + 1, hj'⟩ (by
      change i.val < j.val + 1
      have : i.val < j.val := hij
      omega) (by simp only; omega)).stdReflB n j
    rw [stdReflB_of_succ n (k' := ⟨j.val + 1, hj'⟩) rfl, Pi.add_comp, single_comp_swap,
      single_comp_swap, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hij.ne (Fin.ne_of_val_ne (by
        have : i.val < j.val := hij
        simp only
        omega))] at h
    exact h

private theorem isStdOrbitB_sub {i j : Fin n} (hij : i ≠ j) :
    IsStdOrbitB n (Pi.single i 1 - Pi.single j 1) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact isStdOrbitB_difference n (j.val - i.val - 1) i j (by
      have : i.val < j.val := h
      omega)
  · have := (isStdOrbitB_difference n (i.val - j.val - 1) j i (by
      have : j.val < i.val := h
      omega)).neg n
    rwa [neg_sub] at this

private theorem isStdOrbitB_add {i j : Fin n} (hij : i ≠ j) :
    IsStdOrbitB n (Pi.single i 1 + Pi.single j 1) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact isStdOrbitB_positiveSum n (n - 1 - j.val) i j h (by omega)
  · rw [add_comm]
    exact isStdOrbitB_positiveSum n (n - 1 - i.val) j i h (by omega)

private theorem isStdOrbitB_of_isStdRootB {e : Fin n → ℤ} (he : IsStdRootB n e) :
    IsStdOrbitB n e := by
  rcases he with ⟨i, j, s, t, hij, hs, ht, rfl⟩ | ⟨i, s, hs, rfl⟩
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact isStdOrbitB_add n hij
    · rw [Pi.single_neg, ← sub_eq_add_neg]
      exact isStdOrbitB_sub n hij
    · rw [Pi.single_neg, add_comm, ← sub_eq_add_neg]
      exact isStdOrbitB_sub n hij.symm
    · rw [Pi.single_neg, Pi.single_neg, ← neg_add]
      exact (isStdOrbitB_add n hij).neg n
  · rcases hs with rfl | rfl
    · exact isStdOrbitB_short n (n - 1 - i.val) i (by omega)
    · rw [Pi.single_neg]
      exact (isStdOrbitB_short n (n - 1 - i.val) i (by omega)).neg n

theorem rootsB_eq : roots (isFiniteType_cartanB n) ∅ =
    {γ | (∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
        toStdB n γ = Pi.single i s + Pi.single j t) ∨
      ∃ (i : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ toStdB n γ = Pi.single i s} := by
  ext γ
  constructor
  · rintro (⟨w, k, rfl⟩ | ⟨w, k, hk, -⟩)
    · exact isStdRootB_toStdB_weylAction n w k
    · exact absurd hk (Set.notMem_empty k)
  · intro hγ
    obtain ⟨w, k, hw⟩ := isStdOrbitB_of_isStdRootB n (e := toStdB n γ) hγ
    exact Or.inl ⟨w, k, toStdB_injective n hw.symm⟩

theorem ofStdB_mem_rootsB {e : Fin n → ℤ}
    (he : (∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
        e = Pi.single i s + Pi.single j t) ∨
      ∃ (i : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ e = Pi.single i s) :
    ofStdB n e ∈ roots (isFiniteType_cartanB n) ∅ := by
  rw [rootsB_eq]
  change (∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      toStdB n (ofStdB n e) = Pi.single i s + Pi.single j t) ∨
    ∃ (i : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ toStdB n (ofStdB n e) = Pi.single i s
  rw [toStdB_ofStdB]
  exact he

theorem ht_eq_sum_toStdB (v : Fin n → ℤ) :
    ht v = ∑ a : Fin n, ((n : ℤ) - a) * toStdB n v a := by
  let f : (Fin n → ℤ) →+ ℤ :=
    { toFun := ht
      map_zero' := by simp [ht]
      map_add' := fun v w => by simp [ht, Finset.sum_add_distrib] }
  let g : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ a : Fin n, ((n : ℤ) - a) * toStdB n v a
      map_zero' := by simp [toStdB_zero]
      map_add' := fun v w => by simp [toStdB_add, mul_add, Finset.sum_add_distrib] }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun k x => ?_
    have hs : (Pi.single k x : Fin n → ℤ) = x • Pi.single k 1 := by
      funext j
      simp [Pi.single_apply]
    change ht (Pi.single k x) = ∑ a : Fin n, ((n : ℤ) - a) * toStdB n (Pi.single k x) a
    rw [hs, toStdB_smul]
    by_cases h : k.val + 1 < n
    · rw [toStdB_single_of_lt n h]
      simp [ht, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    · rw [toStdB_single_of_not_lt n h]
      simp only [ht, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have : (k.val : ℤ) + 1 = n := by omega
      linear_combination x * this
  exact DFunLike.congr_fun hfg v

theorem ht_of_toStdB_eq_add {γ : Fin n → ℤ} {i j : Fin n} {s t : ℤ}
    (h : toStdB n γ = Pi.single i s + Pi.single j t) :
    ht γ = s * ((n : ℤ) - i) + t * ((n : ℤ) - j) := by
  rw [ht_eq_sum_toStdB, h]
  simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_comm]

theorem ht_of_toStdB_eq_single {γ : Fin n → ℤ} {i : Fin n} {s : ℤ}
    (h : toStdB n γ = Pi.single i s) : ht γ = s * ((n : ℤ) - i) := by
  rw [ht_eq_sum_toStdB, h]
  simp [Pi.single_apply, mul_comm]

theorem ht_pos_iff_of_toStdB_eq_add {γ : Fin n → ℤ} {i j : Fin n} {s t : ℤ} (hij : i < j)
    (hs₁ : s = 1 ∨ s = -1) (ht₁ : t = 1 ∨ t = -1)
    (h : toStdB n γ = Pi.single i s + Pi.single j t) : 0 < ht γ ↔ s = 1 := by
  rw [ht_of_toStdB_eq_add n h]
  have hij' : i.val < j.val := hij
  have hj := j.isLt
  rcases hs₁ with rfl | rfl <;> rcases ht₁ with rfl | rfl <;> omega

theorem ht_pos_iff_of_toStdB_eq_single {γ : Fin n → ℤ} {i : Fin n} {s : ℤ}
    (hs₁ : s = 1 ∨ s = -1) (h : toStdB n γ = Pi.single i s) : 0 < ht γ ↔ s = 1 := by
  rw [ht_of_toStdB_eq_single n h]
  have hi := i.isLt
  rcases hs₁ with rfl | rfl <;> omega

end CFSG.LieType.Universal.Spin
