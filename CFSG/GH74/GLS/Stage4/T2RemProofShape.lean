module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel
import all CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel
public import Mathlib.Tactic.IntervalCases

public section

open CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel

namespace CFSG.GH74.GLS.Stage4.Rest.Rem.Shape

variable {n : ℕ}

@[expose] def mk (i j : ZMod (2 ^ n)) (e f : ZMod 2) : ShapeGrp n :=
  ⟨(Multiplicative.ofAdd i, Multiplicative.ofAdd j), (Multiplicative.ofAdd e, Multiplicative.ofAdd f)⟩

theorem mk_mul_00 (i j i' j' : ZMod (2 ^ n)) (e' f' : ZMod 2) :
    mk i j 0 0 * mk i' j' e' f' = mk (i + i') (j + j') e' f' := by
  unfold mk
  rw [SemidirectProduct.mul_def]; ext <;> simp [shapeAct]

theorem mk_mul_10 (i j i' j' : ZMod (2 ^ n)) (e' f' : ZMod 2) :
    mk i j 1 0 * mk i' j' e' f' = mk (i + j') (j + i') (1 + e') f' := by
  unfold mk
  rw [SemidirectProduct.mul_def]
  ext <;> simp [shapeAct, cycHom_ofAdd_one, swapAut_apply]

theorem mk_mul_01 (i j i' j' : ZMod (2 ^ n)) (e' f' : ZMod 2) :
    mk i j 0 1 * mk i' j' e' f' = mk (i - i') (j - j') e' (1 + f') := by
  unfold mk
  rw [SemidirectProduct.mul_def]
  ext <;> simp [shapeAct, cycHom_ofAdd_one, invAut_apply, sub_eq_add_neg]

theorem mk_mul_11 (i j i' j' : ZMod (2 ^ n)) (e' f' : ZMod 2) :
    mk i j 1 1 * mk i' j' e' f' = mk (i - j') (j - i') (1 + e') (1 + f') := by
  unfold mk
  rw [SemidirectProduct.mul_def]
  ext <;> simp [shapeAct, cycHom_ofAdd_one, swapAut_apply, invAut_apply, sub_eq_add_neg]

theorem zmod2_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by revert e; decide

theorem zmod2_add_self (e : ZMod 2) : e + e = 0 := by revert e; decide

theorem mk_inj {i j i' j' : ZMod (2 ^ n)} {e f e' f' : ZMod 2}
    (h : mk i j e f = mk i' j' e' f') : i = i' ∧ j = j' ∧ e = e' ∧ f = f' := by
  have h1 := congrArg (fun g : ShapeGrp n => g.left.1) h
  have h2 := congrArg (fun g : ShapeGrp n => g.left.2) h
  have h3 := congrArg (fun g : ShapeGrp n => g.right.1) h
  have h4 := congrArg (fun g : ShapeGrp n => g.right.2) h
  exact ⟨h1, h2, h3, h4⟩

theorem mk_surj (g : ShapeGrp n) : ∃ i j e f, g = mk i j e f :=
  ⟨Multiplicative.toAdd g.left.1, Multiplicative.toAdd g.left.2,
    Multiplicative.toAdd g.right.1, Multiplicative.toAdd g.right.2, rfl⟩

theorem mk_decomp (i j : ZMod (2 ^ n)) (e f : ZMod 2) :
    mk i j e f = mk i 0 0 0 * mk 0 j 0 0 * mk 0 0 e 0 * mk 0 0 0 f := by
  rw [mk_mul_00, mk_mul_00]
  rcases zmod2_cases e with rfl | rfl
  · rw [mk_mul_00]; simp only [add_zero, zero_add]
  · rw [mk_mul_10]; simp only [add_zero, zero_add]

theorem mk_pow_00 (i j : ZMod (2 ^ n)) (k : ℕ) :
    mk i j 0 0 ^ k = mk ((k : ZMod (2 ^ n)) * i) ((k : ZMod (2 ^ n)) * j) 0 0 := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; rfl
  | succ k ih =>
    rw [pow_succ, ih, mk_mul_00, Nat.cast_succ]
    simp only [add_mul, one_mul]

@[expose] def half (n : ℕ) : ZMod (2 ^ n) := ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))

theorem half_add_half (hn : n ≠ 0) : half n + half n = 0 := by
  unfold half
  rw [← Nat.cast_add, ← two_mul, ← pow_succ']
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
  exact ZMod.natCast_self _

theorem half_ne_zero (hn : n ≠ 0) : half n ≠ 0 := by
  unfold half
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h1 := Nat.le_of_dvd (pow_pos two_pos _) h
  have h2 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

section Chi

variable (hn : n ≠ 0)

@[expose] def par (hn : n ≠ 0) : ZMod (2 ^ n) →+* ZMod 2 := ZMod.castHom (dvd_pow_self 2 hn) (ZMod 2)

theorem par_natCast (k : ℕ) : par hn (k : ZMod (2 ^ n)) = (k : ZMod 2) := map_natCast _ k

theorem par_eq_val (i : ZMod (2 ^ n)) : par hn i = (i.val : ZMod 2) := by
  have : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  exact par_natCast hn i.val

theorem par_half (hn2 : 2 ≤ n) : par hn (half n) = 0 := by
  unfold half
  rw [par_natCast, Nat.cast_pow, Nat.cast_ofNat, show (2 : ZMod 2) = 0 by decide]
  exact zero_pow (by omega)

variable (χ : ShapeGrp n → ZMod 2) (hχ : ∀ g h, χ (g * h) = χ g + χ h)
include hχ

theorem chi_one : χ 1 = 0 := by
  have := hχ 1 1
  rw [mul_one] at this
  have h2 : χ 1 + χ 1 = χ 1 + 0 := by rw [add_zero]; exact this.symm
  exact add_left_cancel h2

theorem chi_mk_a (k : ℕ) : χ (mk (k : ZMod (2 ^ n)) 0 0 0) = (k : ZMod 2) * χ (mk 1 0 0 0) := by
  induction k with
  | zero => rw [Nat.cast_zero, Nat.cast_zero, zero_mul]; exact chi_one χ hχ
  | succ k ih =>
    have : mk ((k + 1 : ℕ) : ZMod (2 ^ n)) 0 0 0 = mk (k : ZMod (2 ^ n)) 0 0 0 * mk 1 0 0 0 := by
      rw [mk_mul_00, add_zero, Nat.cast_succ]
    rw [this, hχ, ih, Nat.cast_succ]
    ring

theorem chi_mk_b (k : ℕ) : χ (mk 0 (k : ZMod (2 ^ n)) 0 0) = (k : ZMod 2) * χ (mk 0 1 0 0) := by
  induction k with
  | zero => rw [Nat.cast_zero, Nat.cast_zero, zero_mul]; exact chi_one χ hχ
  | succ k ih =>
    have : mk 0 ((k + 1 : ℕ) : ZMod (2 ^ n)) 0 0 = mk 0 (k : ZMod (2 ^ n)) 0 0 * mk 0 1 0 0 := by
      rw [mk_mul_00, add_zero, Nat.cast_succ]
    rw [this, hχ, ih, Nat.cast_succ]
    ring

theorem chi_b : χ (mk 0 1 0 0) = χ (mk 1 0 0 0) := by
  have h1 : (mk 0 0 1 0 : ShapeGrp n) * mk 1 0 0 0 = mk 0 1 1 0 := by
    rw [mk_mul_10]; simp only [add_zero, zero_add]
  have h2 : (mk 0 1 1 0 : ShapeGrp n) * mk 0 0 1 0 = mk 0 1 0 0 := by
    rw [mk_mul_10]; simp only [add_zero, show (1 : ZMod 2) + 1 = 0 by decide]
  have h : (mk 0 1 0 0 : ShapeGrp n) = mk 0 0 1 0 * mk 1 0 0 0 * mk 0 0 1 0 := by
    rw [h1, h2]
  rw [h, hχ, hχ]
  have := zmod2_add_self (χ (mk 0 0 1 0))
  calc χ (mk 0 0 1 0) + χ (mk 1 0 0 0) + χ (mk 0 0 1 0)
      = χ (mk 1 0 0 0) + (χ (mk 0 0 1 0) + χ (mk 0 0 1 0)) := by ring
    _ = χ (mk 1 0 0 0) := by rw [this, add_zero]

theorem chi_mk (i j : ZMod (2 ^ n)) (e f : ZMod 2) : χ (mk i j e f) =
    (par hn i + par hn j) * χ (mk 1 0 0 0) + e * χ (mk 0 0 1 0) + f * χ (mk 0 0 0 1) := by
  rw [mk_decomp i j e f, hχ, hχ, hχ]
  have hnz : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  have h1 : χ (mk i 0 0 0) = par hn i * χ (mk 1 0 0 0) := by
    have := chi_mk_a χ hχ i.val
    rwa [ZMod.natCast_zmod_val i, ← par_eq_val hn i] at this
  have h2 : χ (mk 0 j 0 0) = par hn j * χ (mk 1 0 0 0) := by
    have := chi_mk_b χ hχ j.val
    rwa [ZMod.natCast_zmod_val j, ← par_eq_val hn j, chi_b χ hχ] at this
  have h3 : χ (mk 0 0 e 0) = e * χ (mk 0 0 1 0) := by
    rcases zmod2_cases e with rfl | rfl
    · rw [zero_mul]; exact chi_one χ hχ
    · rw [one_mul]
  have h4 : χ (mk 0 0 0 f) = f * χ (mk 0 0 0 1) := by
    rcases zmod2_cases f with rfl | rfl
    · rw [zero_mul]; exact chi_one χ hχ
    · rw [one_mul]
  rw [h1, h2, h3, h4]
  ring

end Chi

section Half

theorem neg_half (hn : n ≠ 0) : -half n = half n :=
  neg_eq_of_add_eq_zero_left (half_add_half hn)

theorem add_self_cases (hn : n ≠ 0) {m : ZMod (2 ^ n)} (h : m + m = 0) : m = 0 ∨ m = half n := by
  have hnz : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have h1 : (m + m).val = 0 := by rw [h]; exact ZMod.val_zero
  rw [ZMod.val_add] at h1
  have h2 : 2 ^ (n' + 1) ∣ m.val + m.val := Nat.dvd_of_mod_eq_zero h1
  have hlt : m.val < 2 ^ (n' + 1) := ZMod.val_lt m
  have h4 : m = (m.val : ZMod (2 ^ (n' + 1))) := (ZMod.natCast_zmod_val m).symm
  generalize m.val = v at h2 hlt h4
  have h3 : 2 ^ n' ∣ v := by
    rw [pow_succ', ← two_mul] at h2
    exact Nat.dvd_of_mul_dvd_mul_left two_pos h2
  obtain ⟨c, hc⟩ := h3
  rw [hc, pow_succ] at hlt
  have hc2 : c < 2 := Nat.lt_of_mul_lt_mul_left hlt
  interval_cases c
  · left
    rw [h4, hc]
    simp
  · right
    rw [h4, hc]
    simp [half]

theorem par_of_add_self (hn : 2 ≤ n) {m : ZMod (2 ^ n)} (h : m + m = 0) :
    par (by omega) m = 0 := by
  rcases add_self_cases (by omega) h with rfl | rfl
  · exact map_zero _
  · exact par_half _ hn

end Half

section Index

open Classical in
@[expose] noncomputable def chiOf (N : Subgroup (ShapeGrp n)) (g : ShapeGrp n) : ZMod 2 :=
  if g ∈ N then 0 else 1

theorem chiOf_mem (N : Subgroup (ShapeGrp n)) (g : ShapeGrp n) : g ∈ N ↔ chiOf N g = 0 := by
  classical
  unfold chiOf
  by_cases h : g ∈ N <;> simp [h]

theorem chiOf_mul (N : Subgroup (ShapeGrp n)) (hN : N.index = 2) (g h : ShapeGrp n) :
    chiOf N (g * h) = chiOf N g + chiOf N h := by
  classical
  have key := Subgroup.mul_mem_iff_of_index_two hN (a := g) (b := h)
  unfold chiOf
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases hg : g ∈ N <;> by_cases hh : h ∈ N <;> by_cases hgh : g * h ∈ N <;>
    simp_all

theorem pow_a_t (hn : n ≠ 0) : (mk 1 0 1 0 : ShapeGrp n) ^ (2 ^ n) = mk (half n) (half n) 0 0 := by
  have h2 : (mk 1 0 1 0 : ShapeGrp n) ^ 2 = mk 1 1 0 0 := by
    rw [pow_two, mk_mul_10]
    simp only [add_zero, zero_add, show (1 : ZMod 2) + 1 = 0 by decide]
  have h3 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    exact congrArg _ (by omega)
  have h4 : (mk 1 0 1 0 : ShapeGrp n) ^ (2 ^ n) = ((mk 1 0 1 0 : ShapeGrp n) ^ 2) ^ (2 ^ (n - 1)) := by
    rw [← pow_mul]
    exact congrArg _ h3
  rw [h4, h2, mk_pow_00]
  simp only [mul_one]
  rfl

theorem pow_a_t_y (hn : n ≠ 0) :
    (mk 1 0 1 1 : ShapeGrp n) ^ (2 ^ n) = mk (half n) (half n) 0 0 := by
  have h2 : (mk 1 0 1 1 : ShapeGrp n) ^ 2 = mk 1 (-1) 0 0 := by
    rw [pow_two, mk_mul_11]
    simp only [sub_zero, zero_sub, show (1 : ZMod 2) + 1 = 0 by decide]
  have h3 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    exact congrArg _ (by omega)
  have h4 : (mk 1 0 1 1 : ShapeGrp n) ^ (2 ^ n) = ((mk 1 0 1 1 : ShapeGrp n) ^ 2) ^ (2 ^ (n - 1)) := by
    rw [← pow_mul]
    exact congrArg _ h3
  rw [h4, h2, mk_pow_00]
  have hh : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = half n := rfl
  rw [hh, mul_neg_one, neg_half hn, mul_one]

theorem classify (hn : 2 ≤ n) (N : Subgroup (ShapeGrp n)) (hN : N.index = 2)
    (hexp : ∀ x ∈ N, x ^ (2 ^ n) = 1)
    (hZ : ∀ x ∈ N, (∀ w ∈ N, x * w = w * x) → ∀ x' ∈ N, (∀ w ∈ N, x' * w = w * x') →
      x = 1 ∨ x' = 1 ∨ x = x') (i j : ZMod (2 ^ n)) (e f : ZMod 2) :
    mk i j e f ∈ N ↔ par (by omega) i + par (by omega) j = 0 := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hχ := chiOf_mul N hN
  have hmem := chiOf_mem N
  have hne : (mk (half n) (half n) 0 0 : ShapeGrp n) ≠ 1 := fun h => half_ne_zero hn0 (mk_inj h).1
  have hc1 : chiOf N (mk 1 0 1 0) = 1 := by
    have : mk 1 0 1 0 ∉ N := fun h => hne (by rw [← pow_a_t hn0]; exact hexp _ h)
    rcases zmod2_cases (chiOf N (mk 1 0 1 0)) with h0 | h1
    · exact absurd ((hmem _).2 h0) this
    · exact h1
  have hc2 : chiOf N (mk 1 0 1 1) = 1 := by
    have : mk 1 0 1 1 ∉ N := fun h => hne (by rw [← pow_a_t_y hn0]; exact hexp _ h)
    rcases zmod2_cases (chiOf N (mk 1 0 1 1)) with h0 | h1
    · exact absurd ((hmem _).2 h0) this
    · exact h1
  have e1 := chi_mk hn0 (chiOf N) hχ 1 0 1 0
  have e2 := chi_mk hn0 (chiOf N) hχ 1 0 1 1
  simp only [map_one, map_zero, add_zero, one_mul, zero_mul] at e1 e2
  rw [hc1] at e1
  rw [hc2] at e2
  have hυ : chiOf N (mk 0 0 0 1) = 0 := by
    have : chiOf N (mk 1 0 0 0) + chiOf N (mk 0 0 1 0) + chiOf N (mk 0 0 0 1) =
        chiOf N (mk 1 0 0 0) + chiOf N (mk 0 0 1 0) + 0 := by rw [← e2, add_zero]; exact e1
    exact add_left_cancel this
  have hgen := chi_mk hn0 (chiOf N) hχ i j e f
  rcases zmod2_cases (chiOf N (mk 1 0 0 0)) with hα | hα
  · exfalso
    have hτ : chiOf N (mk 0 0 1 0) = 1 := by
      rw [hα, zero_add] at e1; exact e1.symm
    have hgen' : ∀ i j e f, chiOf N (mk i j e f) = e := by
      intro i j e f
      rw [chi_mk hn0 (chiOf N) hχ i j e f, hα, hτ, hυ]; ring
    have hmemN : ∀ i j e f, mk i j e f ∈ N ↔ e = 0 := by
      intro i j e f
      rw [hmem, hgen']
    have hsub : ∀ m : ZMod (2 ^ n), m - half n = m + half n := fun m => by
      rw [sub_eq_add_neg, neg_half hn0]
    have hu : (mk (half n) 0 0 0 : ShapeGrp n) ∈ N := (hmemN _ _ _ _).2 rfl
    have hu' : (mk 0 (half n) 0 0 : ShapeGrp n) ∈ N := (hmemN _ _ _ _).2 rfl
    have hcu : ∀ w ∈ N, (mk (half n) 0 0 0 : ShapeGrp n) * w = w * mk (half n) 0 0 0 := by
      intro w hw
      obtain ⟨i', j', e', f', rfl⟩ := mk_surj w
      have he' : e' = 0 := (hmemN _ _ _ _).1 hw
      subst he'
      rcases zmod2_cases f' with rfl | rfl
      · rw [mk_mul_00, mk_mul_00, add_comm (half n) i', zero_add, add_zero]
      · rw [mk_mul_00, mk_mul_01]
        simp only [sub_zero, add_zero, zero_add, hsub, add_comm (half n) i']
    have hcu' : ∀ w ∈ N, (mk 0 (half n) 0 0 : ShapeGrp n) * w = w * mk 0 (half n) 0 0 := by
      intro w hw
      obtain ⟨i', j', e', f', rfl⟩ := mk_surj w
      have he' : e' = 0 := (hmemN _ _ _ _).1 hw
      subst he'
      rcases zmod2_cases f' with rfl | rfl
      · rw [mk_mul_00, mk_mul_00, add_comm (half n) j', zero_add, add_zero]
      · rw [mk_mul_00, mk_mul_01]
        simp only [sub_zero, add_zero, zero_add, hsub, add_comm (half n) j']
    rcases hZ _ hu hcu _ hu' hcu' with h | h | h
    · exact half_ne_zero hn0 (mk_inj h).1
    · exact half_ne_zero hn0 (mk_inj h).2.1
    · exact half_ne_zero hn0 (mk_inj h).1
  · have hτ : chiOf N (mk 0 0 1 0) = 0 := by
      rw [hα] at e1
      have : (1 : ZMod 2) + chiOf N (mk 0 0 1 0) = 1 + 0 := by rw [add_zero]; exact e1.symm
      exact add_left_cancel this
    rw [hmem, hgen, hα, hτ, hυ]
    simp

end Index

section Centralizer

@[expose] def uA (n : ℕ) : ShapeGrp n := mk (half n) 0 0 0

@[expose] def uB (n : ℕ) : ShapeGrp n := mk 0 (half n) 0 0

theorem uA_mul_uA (hn : n ≠ 0) : uA n * uA n = 1 := by
  unfold uA
  rw [mk_mul_00, half_add_half hn, add_zero]
  rfl

theorem uB_mul_uB (hn : n ≠ 0) : uB n * uB n = 1 := by
  unfold uB
  rw [mk_mul_00, half_add_half hn, add_zero]
  rfl

theorem uAB_mul_uAB (hn : n ≠ 0) : (uA n * uB n) * (uA n * uB n) = 1 := by
  have h : uA n * uB n = mk (half n) (half n) 0 0 := by
    unfold uA uB
    rw [mk_mul_00, add_zero, zero_add]
  rw [h, mk_mul_00, half_add_half hn]
  rfl

theorem centralizer_outside (hn : 2 ≤ n) (N : Subgroup (ShapeGrp n)) (hN : N.index = 2)
    (hexp : ∀ x ∈ N, x ^ (2 ^ n) = 1)
    (hZ : ∀ x ∈ N, (∀ w ∈ N, x * w = w * x) → ∀ x' ∈ N, (∀ w ∈ N, x' * w = w * x') →
      x = 1 ∨ x' = 1 ∨ x = x')
    (s : ShapeGrp n) (hs : s ∉ N) (hs2 : s * s = 1) (x : ShapeGrp n) (hx : x ∈ N)
    (hxs : x * s = s * x) :
    x = 1 ∨ x = uA n ∨ x = uB n ∨ x = uA n * uB n := by
  have hn0 : n ≠ 0 := by omega
  have hcl := classify hn N hN hexp hZ
  obtain ⟨k, l, e, f, rfl⟩ := mk_surj s
  obtain ⟨i, j, e', f', rfl⟩ := mk_surj x
  have hkl : par hn0 k + par hn0 l = 1 := by
    rcases zmod2_cases (par hn0 k + par hn0 l) with h | h
    · exact absurd ((hcl k l e f).2 h) hs
    · exact h
  have hij : par hn0 i + par hn0 j = 0 := (hcl i j e' f').1 hx
  have hs2' : mk k l e f * mk k l e f = mk 0 0 0 0 := hs2
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hef : e = 0 ∧ f = 1 := by
    rcases zmod2_cases e with rfl | rfl <;> rcases zmod2_cases f with rfl | rfl
    · exfalso
      rw [mk_mul_00] at hs2'
      obtain ⟨h1, h2, -, -⟩ := mk_inj hs2'
      rw [par_of_add_self hn h1, par_of_add_self hn h2] at hkl
      exact absurd hkl (by decide)
    · exact ⟨rfl, rfl⟩
    · exfalso
      rw [mk_mul_10] at hs2'
      obtain ⟨h1, -, -, -⟩ := mk_inj hs2'
      rw [← map_add, h1, map_zero] at hkl
      exact absurd hkl (by decide)
    · exfalso
      rw [mk_mul_11] at hs2'
      obtain ⟨h1, -, -, -⟩ := mk_inj hs2'
      rw [sub_eq_zero.1 h1, zmod2_add_self] at hkl
      exact absurd hkl (by decide)
  obtain ⟨rfl, rfl⟩ := hef
  rcases zmod2_cases e' with rfl | rfl <;> rcases zmod2_cases f' with rfl | rfl
  · rw [mk_mul_00, mk_mul_01] at hxs
    obtain ⟨h1, h2, -, -⟩ := mk_inj hxs
    have hi : i + i = 0 := by
      calc i + i = (i + k) - (k - i) := by ring
        _ = 0 := by rw [h1, sub_self]
    have hj : j + j = 0 := by
      calc j + j = (j + l) - (l - j) := by ring
        _ = 0 := by rw [h2, sub_self]
    rcases add_self_cases hn0 hi with rfl | rfl <;> rcases add_self_cases hn0 hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr (Or.inr ?_))
      unfold uA uB
      rw [mk_mul_00, add_zero, zero_add]
  · exfalso
    rw [mk_mul_01, mk_mul_01] at hxs
    obtain ⟨h1, h2, -, -⟩ := mk_inj hxs
    have hi : (i - k) + (i - k) = 0 := by
      calc (i - k) + (i - k) = (i - k) - (k - i) := by ring
        _ = 0 := by rw [h1, sub_self]
    have hj : (j - l) + (j - l) = 0 := by
      calc (j - l) + (j - l) = (j - l) - (l - j) := by ring
        _ = 0 := by rw [h2, sub_self]
    have pi := par_of_add_self hn hi
    have pj := par_of_add_self hn hj
    rw [map_sub] at pi pj
    rw [sub_eq_zero.1 pi, sub_eq_zero.1 pj, hkl] at hij
    exact absurd hij (by decide)
  · exfalso
    rw [mk_mul_10, mk_mul_01] at hxs
    obtain ⟨h1, h2, -, -⟩ := mk_inj hxs
    have hi : i + i = k - l := by
      calc i + i = ((i + l) - (k - i)) + (k - l) := by ring
        _ = k - l := by rw [h1, sub_self, zero_add]
    have hp : par hn0 k - par hn0 l = 0 := by
      rw [← map_sub, ← hi, map_add, zmod2_add_self]
    rw [sub_eq_zero.1 hp, zmod2_add_self] at hkl
    exact absurd hkl (by decide)
  · exfalso
    rw [mk_mul_11, mk_mul_01] at hxs
    obtain ⟨h1, h2, -, -⟩ := mk_inj hxs
    have hi : i + i = k + l := by
      calc i + i = ((i - l) - (k - i)) + (k + l) := by ring
        _ = k + l := by rw [h1, sub_self, zero_add]
    have hp : par hn0 k + par hn0 l = 0 := by
      rw [← map_add, ← hi, map_add, zmod2_add_self]
    rw [hp] at hkl
    exact absurd hkl (by decide)

end Centralizer

section Iso

theorem centralizer_outside_iso {T : Type*} [Group T] (Ψ : ShapeGrp n ≃* T) (hn : 2 ≤ n)
    (N : Subgroup T) (hN : N.index = 2) (hexp : ∀ x ∈ N, x ^ (2 ^ n) = 1)
    (hZ : ∀ x ∈ N, (∀ w ∈ N, x * w = w * x) → ∀ x' ∈ N, (∀ w ∈ N, x' * w = w * x') →
      x = 1 ∨ x' = 1 ∨ x = x')
    (s : T) (hs : s ∉ N) (hs2 : s * s = 1) :
    ∃ U : Finset T, U.card ≤ 4 ∧ (∀ y ∈ U, y * y = 1) ∧ ∀ x ∈ N, x * s = s * x → x ∈ U := by
  classical
  have hn0 : n ≠ 0 := by omega
  let M : Subgroup (ShapeGrp n) := N.comap Ψ.toMonoidHom
  have hMi : M.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ Ψ.surjective]; exact hN
  have hmem : ∀ g, g ∈ M ↔ Ψ g ∈ N := fun g => Iff.rfl
  have hexpM : ∀ y ∈ M, y ^ (2 ^ n) = 1 := fun y hy =>
    Ψ.injective (by rw [map_pow, map_one]; exact hexp _ ((hmem y).1 hy))
  have hZM : ∀ x ∈ M, (∀ w ∈ M, x * w = w * x) → ∀ x' ∈ M, (∀ w ∈ M, x' * w = w * x') →
      x = 1 ∨ x' = 1 ∨ x = x' := by
    intro x hx hcx x' hx' hcx'
    have hc : ∀ (z : ShapeGrp n), (∀ w ∈ M, z * w = w * z) → ∀ w ∈ N, Ψ z * w = w * Ψ z := by
      intro z hz w hw
      have hw' : Ψ.symm w ∈ M := (hmem _).2 (by rw [MulEquiv.apply_symm_apply]; exact hw)
      have := congrArg Ψ (hz _ hw')
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    rcases hZ _ ((hmem x).1 hx) (hc x hcx) _ ((hmem x').1 hx') (hc x' hcx') with h | h | h
    · exact Or.inl (Ψ.injective (by rw [h, map_one]))
    · exact Or.inr (Or.inl (Ψ.injective (by rw [h, map_one])))
    · exact Or.inr (Or.inr (Ψ.injective h))
  refine ⟨{1, Ψ (uA n), Ψ (uB n), Ψ (uA n * uB n)}, Finset.card_le_four, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · rw [← map_mul, uA_mul_uA hn0, map_one]
    · rw [← map_mul, uB_mul_uB hn0, map_one]
    · rw [← map_mul, uAB_mul_uAB hn0, map_one]
  · intro x hx hxs
    have hs' : Ψ.symm s ∉ M := fun h => hs (by simpa [hmem] using h)
    have hs2' : Ψ.symm s * Ψ.symm s = 1 := by
      apply Ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hs2, map_one]
    have hx' : Ψ.symm x ∈ M := (hmem _).2 (by rw [MulEquiv.apply_symm_apply]; exact hx)
    have hxs' : Ψ.symm x * Ψ.symm s = Ψ.symm s * Ψ.symm x := by
      apply Ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hxs]
    have := centralizer_outside hn M hMi hexpM hZM _ hs' hs2' _ hx' hxs'
    have hxe : x = Ψ (Ψ.symm x) := (MulEquiv.apply_symm_apply Ψ x).symm
    rw [hxe]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases this with h | h | h | h
    · left; rw [h, map_one]
    · right; left; rw [h]
    · right; right; left; rw [h]
    · right; right; right; rw [h]

end Iso

end CFSG.GH74.GLS.Stage4.Rest.Rem.Shape
