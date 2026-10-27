module

public import Certificates.Data.Y2L.ClaimA
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Matrix

@[expose] def y2l_dec (l : List ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  Matrix.of fun i j => ((l.getD (3 * i.val + j.val) 0 : ℕ) : ZMod 4)

theorem y2l_dec_apply (l : List ℕ) (i j : Fin 3) :
    y2l_dec l i j = ((l.getD (3 * i.val + j.val) 0 : ℕ) : ZMod 4) := rfl

theorem y2l_dec_mul3 (m n : List ℕ) : y2l_dec (y2l_mul3 m n) = y2l_dec m * y2l_dec n := by
  ext i j
  have hlt : 3 * i.val + j.val < 9 := by omega
  have h1 : (3 * i.val + j.val) / 3 = i.val := by omega
  have h2 : (3 * i.val + j.val) % 3 = j.val := by omega
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [y2l_dec_apply, y2l_mul3, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some, h1, h2, hr, Matrix.mul_apply,
    Fin.sum_univ_three, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

theorem y2l_dec_one3 : y2l_dec y2l_one3 = 1 := by
  decide

theorem y2l_dec_pow3 (m : List ℕ) (k : ℕ) : y2l_dec (y2l_pow3 m k) = y2l_dec m ^ k := by
  induction k with
  | zero => rw [y2l_pow3, pow_zero, y2l_dec_one3]
  | succ k ih => rw [y2l_pow3, y2l_dec_mul3, ih, pow_succ]

theorem y2l_dec_perturb {m l : List ℕ} (hm : m.length = 9) (hl : l.length = 9) :
    y2l_dec (y2l_perturb m l) = y2l_dec m + (2 : ZMod 4) • y2l_dec l := by
  ext i j
  have hlt : 3 * i.val + j.val < 9 := by omega
  rw [Matrix.add_apply, Matrix.smul_apply, y2l_dec_apply, y2l_dec_apply, y2l_dec_apply,
    y2l_perturb, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 3 * i.val + j.val < m.length),
    List.getElem?_eq_getElem (by omega : 3 * i.val + j.val < l.length)]
  simp only [Option.getD_some, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    smul_eq_mul]

theorem y2l_length_mul3 (m n : List ℕ) : (y2l_mul3 m n).length = 9 := by
  simp [y2l_mul3]

theorem y2l_lt_mul3 (m n : List ℕ) : ∀ x ∈ y2l_mul3 m n, x < 4 := by
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  exact Nat.mod_lt _ (by norm_num)

theorem y2l_length_pow3 (m : List ℕ) : ∀ k, (y2l_pow3 m k).length = 9
  | 0 => by rw [y2l_pow3]; rfl
  | k + 1 => by rw [y2l_pow3]; exact y2l_length_mul3 _ _

theorem y2l_lt_pow3 (m : List ℕ) : ∀ k, ∀ x ∈ y2l_pow3 m k, x < 4
  | 0 => by rw [y2l_pow3]; decide
  | k + 1 => by rw [y2l_pow3]; exact y2l_lt_mul3 _ _

theorem y2l_dec_inj {m n : List ℕ} (hm : m.length = 9) (hn : n.length = 9)
    (hm4 : ∀ x ∈ m, x < 4) (hn4 : ∀ x ∈ n, x < 4) (h : y2l_dec m = y2l_dec n) : m = n := by
  refine List.ext_getElem (hm.trans hn.symm) fun t ht1 ht2 => ?_
  have e : 3 * (t / 3) + t % 3 = t := by omega
  have h1 := congrFun (congrFun h ⟨t / 3, by omega⟩) ⟨t % 3, by omega⟩
  rw [y2l_dec_apply, y2l_dec_apply] at h1
  simp only [Fin.val_mk, e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1,
    List.getElem?_eq_getElem ht2, Option.getD_some] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 4).mp h1
  rwa [Nat.mod_eq_of_lt (hm4 _ (List.getElem_mem ht1)),
    Nat.mod_eq_of_lt (hn4 _ (List.getElem_mem ht2))] at h2

theorem y2l_eq_of_dec {m n : List ℕ} (hm : m.length = 9 ∧ ∀ x ∈ m, x < 4)
    (hn : n.length = 9 ∧ ∀ x ∈ n, x < 4) (h : y2l_dec m = y2l_dec n) : m = n :=
  y2l_dec_inj hm.1 hn.1 hm.2 hn.2 h

theorem y2l_nf_one3 : y2l_one3.length = 9 ∧ ∀ x ∈ y2l_one3, x < 4 :=
  ⟨rfl, by decide⟩

theorem y2l_nf_pow3 (m : List ℕ) (k : ℕ) :
    (y2l_pow3 m k).length = 9 ∧ ∀ x ∈ y2l_pow3 m k, x < 4 :=
  ⟨y2l_length_pow3 m k, y2l_lt_pow3 m k⟩

theorem y2l_mem_bits : ∀ (k : ℕ) (l : List ℕ), l.length = k → (∀ x ∈ l, x < 2) → l ∈ y2l_bits k
  | 0, l, hl, _ => by
    rw [List.eq_nil_of_length_eq_zero hl, y2l_bits]
    exact List.mem_singleton_self _
  | k + 1, [], hl, _ => absurd hl (by simp)
  | k + 1, b :: l, hl, hb => by
    rw [y2l_bits, List.mem_flatMap]
    refine ⟨l, y2l_mem_bits k l (by simpa using hl) fun x hx => hb x (List.mem_cons_of_mem _ hx),
      ?_⟩
    have hb2 : b < 2 := hb b (by simp)
    interval_cases b <;> simp

theorem y2l_length_of_mem_bits : ∀ {k : ℕ} {l : List ℕ}, l ∈ y2l_bits k → l.length = k
  | 0, l, h => by
    rw [y2l_bits, List.mem_singleton] at h
    rw [h]
    rfl
  | k + 1, l, h => by
    rw [y2l_bits, List.mem_flatMap] at h
    obtain ⟨l', hl', hl⟩ := h
    have := y2l_length_of_mem_bits hl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp [this]

@[expose] def y2l_enc (D : Matrix (Fin 3) (Fin 3) (ZMod 4)) : List ℕ :=
  [(D 0 0).val, (D 0 1).val, (D 0 2).val, (D 1 0).val, (D 1 1).val, (D 1 2).val,
    (D 2 0).val, (D 2 1).val, (D 2 2).val]

theorem y2l_length_enc (D : Matrix (Fin 3) (Fin 3) (ZMod 4)) : (y2l_enc D).length = 9 := rfl

theorem y2l_dec_enc (D : Matrix (Fin 3) (Fin 3) (ZMod 4)) : y2l_dec (y2l_enc D) = D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y2l_dec_apply, y2l_enc, ZMod.natCast_zmod_val]

theorem y2l_enc_mem_bits {D : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (h : ∀ i j, D i j = 0 ∨ D i j = 1) : y2l_enc D ∈ y2l_bits 9 := by
  have hv : ∀ a : ZMod 4, a = 0 ∨ a = 1 → a.val < 2 := by decide
  refine y2l_mem_bits 9 _ rfl fun x hx => ?_
  simp only [y2l_enc, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hv _ (h _ _)

@[expose] def y2l_red : Matrix (Fin 3) (Fin 3) (ZMod 4) →+* Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).mapMatrix

theorem y2l_red_apply (A : Matrix (Fin 3) (Fin 3) (ZMod 4)) (i j : Fin 3) :
    y2l_red A i j = ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (A i j) := rfl

theorem y2l_sq_of_red {Q : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : y2l_red Q = 1) : Q * Q = 1 := by
  have hz : ∀ a : ZMod 4, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) a = 0 → a + a = 0 := by
    decide
  have hz' : ∀ a b : ZMod 4, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) a = 0 →
      ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) b = 0 → a * b = 0 := by
    decide
  have h0 : ∀ i j, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) ((Q - 1) i j) = 0 := fun i j => by
    rw [← y2l_red_apply, map_sub, h, map_one, sub_self, Matrix.zero_apply]
  generalize hD : Q - 1 = D at h0
  have hQ : Q = 1 + D := by rw [← hD]; abel
  have hDD : D * D = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => hz' _ _ (h0 i k) (h0 k j)
  have hD2 : D + D = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact hz _ (h0 i j)
  calc Q * Q = 1 + (D + D) + D * D := by rw [hQ]; noncomm_ring
    _ = 1 := by rw [hD2, hDD, add_zero, add_zero]

theorem y2l_exists_perturb {A R : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : y2l_red A = y2l_red R) :
    ∃ D : Matrix (Fin 3) (Fin 3) (ZMod 4), (∀ i j, D i j = 0 ∨ D i j = 1) ∧
      A = R + (2 : ZMod 4) • D := by
  have hz : ∀ a b : ZMod 4, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) a =
      ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) b → a = b + 2 * (if a = b then 0 else 1) := by
    decide
  refine ⟨Matrix.of fun i j => if A i j = R i j then 0 else 1, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply]
    split_ifs <;> simp
  · ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact hz _ _ (by rw [← y2l_red_apply, ← y2l_red_apply, h])

theorem y2l_sq_one_add_two (N : Matrix (Fin 3) (Fin 3) (ZMod 4)) :
    (1 + (2 : ZMod 4) • N) * (1 + (2 : ZMod 4) • N) = 1 := by
  have h2 : (2 + 2 : ZMod 4) = 0 := by decide
  have h4 : (2 * 2 : ZMod 4) = 0 := by decide
  have hN : (2 : ZMod 4) • N + (2 : ZMod 4) • N = 0 := by rw [← add_smul, h2, zero_smul]
  have hNN : ((2 : ZMod 4) • N) * ((2 : ZMod 4) • N) = 0 := by
    rw [smul_mul_smul_comm, h4, zero_smul]
  generalize (2 : ZMod 4) • N = D at hN hNN
  calc (1 + D) * (1 + D) = 1 + (D + D) + D * D := by noncomm_ring
    _ = 1 := by rw [hN, hNN, add_zero, add_zero]

end CFSG.OddStandard.HigherRank.G2Three.Sec2
