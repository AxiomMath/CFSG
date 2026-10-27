
module

public import CFSG.Certificates.Kernel.GH74Tab.Transport
public import Certificates.Data.Kernel.GH74Tab.WB
public import Certificates.Data.Kernel.GH74Tab.Adm
public import CFSG.GH74.GLS.C3.Layer2.L4ModelGen

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem bit_eq (m k : Nat) : bit m k = m.testBit k := by
  rw [bit, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m >>> k) with h | h <;> simp [h]

theorem g6_lt (T k : Nat) : g6 T k < 64 := Nat.mod_lt _ (by decide)

theorem testBit_g6 (T k b : Nat) : (g6 T k).testBit b = (decide (b < 6) && T.testBit (6 * k + b)) := by
  have e : g6 T k = (T >>> (6 * k)) % 2 ^ 6 := rfl
  rw [e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_lt64 {v b : Nat} (hv : v < 64) (hb : 6 ≤ b) : v.testBit b = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hb :
    2 ^ 6 ≤ 2 ^ b))

theorem g6_or (x y k : Nat) : g6 (x ||| y) k = g6 x k ||| g6 y k := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [testBit_g6, Nat.testBit_or, Bool.and_or_distrib_left]

theorem g6_shl {v : Nat} (hv : v < 64) (i j : Nat) :
    g6 (v <<< (6 * i)) j = if j = i then v else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_g6, Nat.testBit_shiftLeft]
  by_cases hji : j = i
  · subst hji
    simp only [if_true]
    by_cases hb : b < 6
    · simp [hb]
    · have := testBit_lt64 hv (b := b) (by omega)
      simp [hb, this]
  · simp only [hji, if_false, Nat.zero_testBit]
    by_cases hb : b < 6
    · by_cases hle : 6 * i ≤ 6 * j + b
      · have : 6 ≤ 6 * j + b - 6 * i := by omega
        simp [testBit_lt64 hv this]
      · simp [hle]
    · simp [hb]

theorem bit_or (x y k : Nat) : bit (x ||| y) k = (bit x k || bit y k) := by
  simp only [bit_eq, Nat.testBit_or]

theorem bit_and (x y k : Nat) : bit (x &&& y) k = (bit x k && bit y k) := by
  simp only [bit_eq, Nat.testBit_and]

theorem bit_shl1 (j k : Nat) : bit (1 <<< j) k = decide (k = j) := by
  rw [bit_eq, Nat.one_shiftLeft, Nat.testBit_two_pow]
  exact decide_eq_decide.2 eq_comm

theorem bit_ge {x k : Nat} (hx : x < 2 ^ 64) (hk : 64 ≤ k) : bit x k = false := by
  rw [bit_eq]
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hk))

theorem bit_lt {x k : Nat} (hx : ∀ j, bit x j = true → j < 64) (hk : bit x k = true) : k < 64 :=
  hx k hk

theorem shl1_lt {j : Nat} (hj : j < 64) : 1 <<< j < 2 ^ 64 := by
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by decide) hj

theorem gk_lt (k : Nat) : gk k < 64 := by
  unfold gk
  split <;> decide

theorem val_f64 {x : Nat} (hx : x < 64) : (f64 x).val = x := Nat.mod_eq_of_lt hx

theorem f64_val (i : Fin 64) : f64 i.val = i := Fin.ext (val_f64 i.2)

theorem mul_lt (D : Dat) (i j : Nat) : mul D i j < 64 := g6_lt _ _

theorem val_f64_mul (D : Dat) (i j : Nat) : (f64 (mul D i j)).val = mul D i j :=
  val_f64 (mul_lt D i j)

theorem val_f64_g6 (T k : Nat) : (f64 (g6 T k)).val = g6 T k := val_f64 (g6_lt T k)

variable (D : Dat)

theorem dataOK_spec (h : dataOK D = true) :
    D.one < 64 ∧ D.x0 < 64 ∧ mul D (gk 0) (gk 0) = D.x0 ∧
    D.rel.foldl (fun r k => mul D r (gk k)) D.one = D.one ∧
    D.Tr.foldl (fun (s : Option Nat) e =>
      match s, e with
      | some m, [i, p, k] =>
        bif i < 64 && !bit m i && bit m p && k < 4 && mul D p (gk k) == i then some (m ||| 1 <<< i)
        else none
      | _, _ => none) (some (1 <<< D.one)) = some (2 ^ 64 - 1) ∧
    (∀ k < 4, D.L.getD k [] = r64.filter fun h => cls3 D h == cls3 D (gk k)) ∧
    (∀ q < 6, ∀ x < 64,
      (D.NM.getD q []).getD x 0 < 2 ^ 64 ∧
      (D.NL.getD q []).getD x [] = r64.filter (bit ((D.NM.getD q []).getD x 0)) ∧
      ∀ y < 64, bit ((D.NM.getD q []).getD x 0) y =
        (cls3 D y == cls3 D (gk (prs.getD q (0, 0)).2) &&
          pairOK D x y (gk (prs.getD q (0, 0)).1) (gk (prs.getD q (0, 0)).2))) ∧
    (∀ i < 64, bit D.IV i = (i != D.one && mul D i i == D.one) ∧
      ∀ j < 64, bit (cm D i) j = (bit D.IV i && bit D.IV j && g6 D.C i == g6 D.C j)) := by
  simp only [dataOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, r64] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h6, h7, ?_, h9⟩
  intro q hq x hx
  have := h8 q hq
  rcases hp : prs.getD q (0, 0) with ⟨k, l⟩
  rw [hp] at this
  obtain ⟨-, hN⟩ := this
  obtain ⟨⟨hm, hl⟩, hy⟩ := hN x hx
  exact ⟨hm, hl, hy⟩

@[expose] def trStep (s : Option Nat) (e : List Nat) : Option Nat :=
  match s, e with
  | some m, [i, p, k] =>
    bif i < 64 && !bit m i && bit m p && k < 4 && mul D p (gk k) == i then some (m ||| 1 <<< i)
    else none
  | _, _ => none

@[expose] def ofStep (h0 h1 h2 h3 acc : Nat) (e : List Nat) : Nat :=
  match e with
  | [i, p, k] => acc ||| mul D (g6 acc p) (hk h0 h1 h2 h3 k) <<< (6 * i)
  | _ => acc

theorem trStep_nil (m : Nat) : trStep D (some m) [] = none := rfl

theorem trStep_one (m i : Nat) : trStep D (some m) [i] = none := rfl

theorem trStep_two (m i p : Nat) : trStep D (some m) [i, p] = none := rfl

theorem trStep_long (m i p k x : Nat) (r : List Nat) :
    trStep D (some m) (i :: p :: k :: x :: r) = none := rfl

theorem trStep_three (m i p k : Nat) : trStep D (some m) [i, p, k] =
    bif i < 64 && !bit m i && bit m p && k < 4 && mul D p (gk k) == i then some (m ||| 1 <<< i)
    else none := rfl

theorem trStep_none (e : List Nat) : trStep D none e = none := by
  rcases e with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

theorem foldl_trStep_none (l : List (List Nat)) : l.foldl (trStep D) none = none := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [List.foldl_cons, trStep_none, ih]

theorem ofStep_three (h0 h1 h2 h3 acc i p k : Nat) : ofStep D h0 h1 h2 h3 acc [i, p, k] =
    acc ||| mul D (g6 acc p) (hk h0 h1 h2 h3 k) <<< (6 * i) := rfl

theorem ofImg_eq (h0 h1 h2 h3 : Nat) :
    ofImg D h0 h1 h2 h3 = D.Tr.foldl (ofStep D h0 h1 h2 h3) (D.one <<< (6 * D.one)) := rfl

@[expose] def av (a : Tbl) (i : Nat) : Nat := (a.get (f64 i)).val

theorem av_lt (a : Tbl) (i : Nat) : av a i < 64 := (a.get (f64 i)).2

@[expose] def packA (a : Tbl) : Nat := ofImg D (av a (gk 0)) (av a (gk 1)) (av a (gk 2)) (av a (gk 3))

section Aut

variable {D} {n : ℕ} [NeZero n] (ht : transOK D n = true) {a : Tbl} (ha : (mkTab n).IsAutT a)
include ht ha

theorem av_mul {i j : Nat} (hi : i < 64) (hj : j < 64) :
    av a (mul D i j) = mul D (av a i) (av a j) := by
  have e1 : f64 (mul D i j) = (mkTab n).mulT (f64 i) (f64 j) := by
    rw [mulT_eq D ht, val_f64 hi, val_f64 hj]
  unfold av
  rw [e1, ha.hom, mulT_eq D ht, val_f64 (mul_lt D _ _)]

theorem av_one (hd1 : D.one < 64) : av a D.one = D.one := by
  unfold av
  have h := ha.one
  rw [one_eq D ht] at h
  rw [h, val_f64 hd1]

theorem av_inj {i j : Nat} (hi : i < 64) (hj : j < 64) (h : av a i = av a j) : i = j := by
  have h1 := congrArg Fin.val (ha.inj (f64 i) (f64 j) (Fin.ext h))
  rwa [val_f64 hi, val_f64 hj] at h1

theorem cls3_av (hd1 : D.one < 64) {i : Nat} (hi : i < 64) : cls3 D (av a i) = cls3 D i := by
  unfold cls3
  by_cases h1 : i = D.one
  · rw [h1, av_one ht ha hd1]
  · have h1' : av a i ≠ D.one := fun e =>
      h1 (av_inj ht ha hi hd1 (e.trans (av_one ht ha hd1).symm))
    by_cases h2 : mul D i i = D.one
    · have h2' : mul D (av a i) (av a i) = D.one := by
        rw [← av_mul ht ha hi hi, h2, av_one ht ha hd1]
      simp [h1, h1', h2, h2']
    · have h2' : mul D (av a i) (av a i) ≠ D.one := fun e =>
        h2 (av_inj ht ha (mul_lt _ _ _) hd1 (by rw [av_mul ht ha hi hi, e, av_one ht ha hd1]))
      simp [h1, h1', h2, h2']

theorem pairOK_av (hd1 : D.one < 64) {x y : Nat} (hx : x < 64) (hy : y < 64) :
    pairOK D (av a x) (av a y) x y = true := by
  unfold pairOK
  rw [← av_mul ht ha hx hy, ← av_mul ht ha hy hx, cls3_av ht ha hd1 (mul_lt _ _ _),
    cls3_av ht ha hd1 (mul_lt _ _ _)]
  simp

theorem rel_av (l : List Nat) {r : Nat} (hr : r < 64) :
    l.foldl (fun r k => mul D r (av a (gk k))) (av a r) =
      av a (l.foldl (fun r k => mul D r (gk k)) r) := by
  induction l generalizing r with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    rw [← av_mul ht ha hr (gk_lt k), ih (mul_lt _ _ _)]

theorem hk_av (k : Nat) :
    hk (av a (gk 0)) (av a (gk 1)) (av a (gk 2)) (av a (gk 3)) k = av a (gk k) := by
  rcases k with _ | _ | _ | k <;> rfl

theorem tree_inv (hd1 : D.one < 64) :
    ∀ (l : List (List Nat)) (acc m M : Nat), (∀ j, bit m j = true → j < 64) →
      (∀ j < 64, g6 acc j = if bit m j then av a j else 0) →
      l.foldl (trStep D) (some m) = some M →
      (∀ j, bit M j = true → j < 64) ∧
      ∀ j < 64, g6 (l.foldl (ofStep D (av a (gk 0)) (av a (gk 1)) (av a (gk 2)) (av a (gk 3)))
        acc) j = if bit M j then av a j else 0 := by
  intro l
  induction l with
  | nil =>
    intro acc m M hm hg h
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨hm, hg⟩
  | cons e l ih =>
    intro acc m M hm hg h
    rw [List.foldl_cons] at h
    rw [List.foldl_cons]
    rcases e with _ | ⟨i, _ | ⟨p, _ | ⟨k, _ | ⟨x, rest⟩⟩⟩⟩
    · rw [trStep_nil, foldl_trStep_none] at h
      exact absurd h (by simp)
    · rw [trStep_one, foldl_trStep_none] at h
      exact absurd h (by simp)
    · rw [trStep_two, foldl_trStep_none] at h
      exact absurd h (by simp)
    rotate_left
    · rw [trStep_long, foldl_trStep_none] at h
      exact absurd h (by simp)
    · cases hc : (decide (i < 64) && !bit m i && bit m p && decide (k < 4) && mul D p (gk k) == i)
      · rw [trStep_three, hc, cond_false, foldl_trStep_none] at h
        exact absurd h (by simp)
      · rw [trStep_three, hc, cond_true] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨hi, hmi⟩, hmp⟩, -⟩, hmul⟩ := hc
        have hp : p < 64 := hm p hmp
        refine ih _ _ _ ?_ ?_ h
        · intro j hj
          rw [bit_or, bit_shl1, Bool.or_eq_true, decide_eq_true_eq] at hj
          rcases hj with hj | hj
          · exact hm j hj
          · rw [hj]
            exact hi
        · intro j hj
          rw [ofStep_three, g6_or, g6_shl (mul_lt _ _ _) i j, bit_or, bit_shl1, hg p hp, if_pos hmp,
            hk_av ht ha, ← av_mul ht ha hp (gk_lt k), hmul, hg j hj]
          by_cases hji : j = i
          · subst hji
            simp [hmi]
          · simp [hji]

theorem packA_get (hd : dataOK D = true) {i : Nat} (hi : i < 64) : g6 (packA D a) i = av a i := by
  obtain ⟨hd1, -, -, -, htr, -⟩ := dataOK_spec D hd
  have htr' : D.Tr.foldl (trStep D) (some (1 <<< D.one)) = some (2 ^ 64 - 1) := htr
  have h1 : ∀ j, bit (1 <<< D.one) j = true → j < 64 := by
    intro j hj
    rw [bit_shl1, decide_eq_true_eq] at hj
    rw [hj]
    exact hd1
  have h2 : ∀ j < 64, g6 (D.one <<< (6 * D.one)) j =
      if bit (1 <<< D.one) j then av a j else 0 := by
    intro j _
    rw [g6_shl hd1, bit_shl1]
    by_cases hj : j = D.one
    · simp [hj, av_one ht ha hd1]
    · simp [hj]
  have := (tree_inv ht ha hd1 D.Tr _ _ _ h1 h2 htr').2 i hi
  rw [packA, ofImg_eq, this, bit_eq, Nat.testBit_two_pow_sub_one, decide_eq_true hi, if_pos rfl]

theorem tblOf_packA (hd : dataOK D = true) : tblOf (packA D a) = a := by
  apply Vector.ext
  intro i hi
  rw [tblOf, Vector.getElem_ofFn, packA_get ht ha hd hi, av, f64_val]
  have e : f64 i = ⟨i, hi⟩ := Fin.ext (val_f64 hi)
  rw [e]
  rfl

end Aut

@[expose] def lo (m : Nat) : Prop := ∀ j, bit m j = true → j < 64

theorem bit_foldl_cond (c : Nat → Bool) (v : Nat → Nat) (l : List Nat) (acc j : Nat) :
    bit (l.foldl (fun acc i => bif c i then acc ||| v i else acc) acc) j =
      (bit acc j || l.any fun i => c i && bit (v i) j) := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih, List.any_cons]
    cases c i <;> simp [bit_or, Bool.or_assoc]

theorem bit_cond (b : Bool) (x j : Nat) : bit (bif b then x else 0) j = (b && bit x j) := by
  cases b <;> simp [bit]

theorem stepK_eq (A S : Nat) : stepK D A S = r64.foldl (fun acc i =>
    bif bit S i && bit D.IV i then
      acc ||| (cm D i ||| (bif bit D.IV (g6 A i) then 1 <<< g6 A i else 0))
    else acc) S := by
  unfold stepK
  congr 1
  funext acc i
  cases bit S i && bit D.IV i <;> simp [Nat.or_assoc]

theorem bit_stepK (A S j : Nat) : bit (stepK D A S) j = (bit S j || r64.any fun i =>
    (bit S i && bit D.IV i) &&
      (bit (cm D i) j || (bit D.IV (g6 A i) && decide (j = g6 A i)))) := by
  rw [stepK_eq, bit_foldl_cond]
  congr 1
  congr 1
  funext i
  rw [bit_or, bit_cond, bit_shl1]

theorem cm_lt (i : Nat) : cm D i < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem lo_stepK (A S : Nat) (hS : lo S) : lo (stepK D A S) := by
  intro j hj
  rw [bit_stepK, Bool.or_eq_true, List.any_eq_true] at hj
  rcases hj with hj | ⟨i, -, hi⟩
  · exact hS j hj
  · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hi
    rcases hi.2 with h | ⟨-, h⟩
    · by_contra hge
      rw [bit_ge (cm_lt D i) (by omega)] at h
      exact absurd h (by decide)
    · rw [h]
      exact g6_lt _ _

theorem any_r64 {f : Fin 64 → Bool} {g : Nat → Bool} (hfg : ∀ i : Fin 64, f i = g i.val) :
    (List.finRange 64).any f = r64.any g := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_finRange, true_and, r64, List.mem_range]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i.val, i.2, by rw [← hfg]; exact h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, by rw [hfg]; exact h⟩

theorem vget_mk {α : Type} {m : Nat} (xs : Vector α m) {i : Nat} (hi : i < m) :
    xs.get ⟨i, hi⟩ = xs[i] := rfl

theorem tblOf_get (A : Nat) (i : Fin 64) : g6 A i.val = ((tblOf A).get i).val := by
  rw [tblOf, vget_ofFn, val_f64_g6]

@[expose] def Agree (S : Vector Bool 64) (m : Nat) : Prop :=
  lo m ∧ ∀ i : Fin 64, S.get i = bit m i.val

section Reach

variable {D} {n : ℕ} [NeZero n] (ht : transOK D n = true) (hd : dataOK D = true)
include ht hd

theorem isInv_eq (i : Fin 64) : (mkTab n).isInv i = bit D.IV i.val := by
  obtain ⟨hd1, -, -, -, -, -, -, hIV⟩ := dataOK_spec D hd
  rw [(hIV i.val i.2).1, Tab.isInv, one_eq D ht, mulT_eq D ht, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq, Fin.ext_iff,
    val_f64 hd1, val_f64 (mul_lt D _ _)]

theorem agree_step (A : Nat) {S : Vector Bool 64} {m : Nat} (h : Agree S m) :
    Agree ((mkTab n).step (tblOf A) S) (stepK D A m) := by
  obtain ⟨-, -, -, -, -, -, -, hIV⟩ := dataOK_spec D hd
  refine ⟨lo_stepK D _ m h.1, fun j => ?_⟩
  rw [Tab.step, vget_ofFn, bit_stepK, h.2 j]
  refine congrArg (fun b => bit m j.val || b) (any_r64 fun i => ?_)
  rw [h.2 i, Tab.edge, isInv_eq ht hd, isInv_eq ht hd, cls_eq D ht, cls_eq D ht,
    (hIV i.val i.2).2 j.val j.2, tblOf_get A i]
  generalize tblOf A = a
  have e : (a.get i == j) = decide ((a.get i).val = j.val) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]
  rw [e]
  by_cases hij : (a.get i).val = j.val
  · rw [hij]
    cases bit m i.val <;> cases bit D.IV i.val <;> cases bit D.IV j.val <;> simp
  · have hij' : ¬ j.val = (a.get i).val := fun h => hij h.symm
    simp only [hij, hij', decide_false, Bool.and_false, Bool.or_false]
    cases bit m i.val <;> cases bit D.IV i.val <;> simp

theorem agree_reachK (A : Nat) : ∀ (f : Nat) {S : Vector Bool 64} {m : Nat}, Agree S m →
    Agree (((mkTab n).step (tblOf A))^[f] S) (reachK D A f m) := by
  intro f
  induction f with
  | zero => intro S m h; exact h
  | succ f ih =>
    intro S m h
    rw [Function.iterate_succ_apply, reachK]
    have h1 := agree_step ht hd A h
    by_cases hfix : stepK D A m = m
    · have hS : (mkTab n).step (tblOf A) S = S := by
        apply Vector.ext
        intro i hi
        have e1 := h1.2 ⟨i, hi⟩
        have e2 := h.2 ⟨i, hi⟩
        rw [hfix] at e1
        rw [← vget_mk, ← vget_mk]
        exact e1.trans e2.symm
      rw [hS, Function.iterate_fixed hS]
      simp [hfix, h]
    · have e : (stepK D A m == m) = false := by simpa using hfix
      rw [e, cond_false]
      exact ih h1

theorem agree_reach (A : Nat) (s : Fin 64) :
    Agree ((mkTab n).reach (tblOf A) s) (reachK D A 12 (1 <<< s.val)) := by
  rw [Tab.reach]
  apply agree_reachK ht hd A 12
  refine ⟨fun j hj => ?_, fun i => ?_⟩
  · rw [bit_shl1, decide_eq_true_eq] at hj
    rw [hj]
    exact s.2
  · rw [vget_ofFn, bit_shl1, Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]

theorem reach_tblOf (A : Nat) (s i : Fin 64) :
    ((mkTab n).reach (tblOf A) s).get i = bit (reachK D A 12 (1 <<< s.val)) i.val :=
  (agree_reach ht hd A s).2 i

theorem reachK_lo (A : Nat) (s : Fin 64) : lo (reachK D A 12 (1 <<< s.val)) :=
  (agree_reach ht hd A s).1

end Reach

theorem mask_disj {X V : Nat} (hX : lo X) (h : ∀ i < 64, bit X i = true → bit V i = false) :
    X &&& V = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, ← bit_eq, ← bit_eq]
  cases hXi : bit X i
  · rfl
  · rw [h i (hX i hXi) hXi]
    rfl

theorem mask_Q {V Q o : Nat} (hV : lo V)
    (h : ∀ i < 64, bit Q i = true → i ≠ o → bit V i = false) :
    ((V &&& Q) ||| 1 <<< o) = 1 <<< o := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_and, ← bit_eq, ← bit_eq, ← bit_eq, bit_shl1]
  by_cases hio : i = o
  · simp [hio]
  · simp only [hio, decide_false, Bool.or_false]
    cases hVi : bit V i
    · rfl
    · cases hQi : bit Q i
      · rfl
      · exact absurd ((h i (hV i hVi) hQi hio).symm.trans hVi) (by decide)

theorem nl_mem (hd : dataOK D = true) (q : Nat) (hq : q < 6) {x y : Nat} (hx : x < 64)
    (hy : y < 64) (hc : cls3 D y = cls3 D (gk (prs.getD q (0, 0)).2))
    (hp : pairOK D x y (gk (prs.getD q (0, 0)).1) (gk (prs.getD q (0, 0)).2) = true) :
    y ∈ (D.NL.getD q []).getD x [] ∧ bit ((D.NM.getD q []).getD x 0) y = true := by
  obtain ⟨-, -, -, -, -, -, hN, -⟩ := dataOK_spec D hd
  obtain ⟨-, hl, hb⟩ := hN q hq x hx
  have hbit : bit ((D.NM.getD q []).getD x 0) y = true := by
    rw [hb y hy, hc, hp, beq_self_eq_true, Bool.true_and]
  refine ⟨?_, hbit⟩
  rw [hl, r64, List.mem_filter, List.mem_range]
  exact ⟨hy, hbit⟩

theorem packA_def (a : Tbl) :
    ofImg D (av a (gk 0)) (av a (gk 1)) (av a (gk 2)) (av a (gk 3)) = packA D a := rfl

theorem pairsOf_mem {A U : Nat}
    (hU : U ∈ r64.filter fun u => g6 A u == u && ((List.range 4).all fun k => sqAt D A u (gk k)) &&
      r64.all (sqAt D A u))
    (hc : (reachK D A 12 (1 <<< D.x0) &&& reachK D A 12 (1 <<< mul D D.x0 (g6 A D.x0)) == 0 &&
      ((reachK D A 12 (1 <<< mul D D.x0 (g6 A D.x0)) &&& D.Q) ||| 1 <<< D.one) == 1 <<< D.one)
      = true) :
    (A, U) ∈ pairsOf D A := by
  unfold pairsOf
  dsimp only
  split
  · next h =>
    rw [h] at hU
    exact absurd hU (List.not_mem_nil)
  · rw [hc, cond_true]
    exact List.mem_map.2 ⟨U, hU, rfl⟩

section Main

variable {D} {n : ℕ} [NeZero n] (ht : transOK D n = true) (hd : dataOK D = true)
  (hs : searchOK D = true)
include ht hd hs

theorem mem_adm {a : Tbl} (ha : (mkTab n).IsAutT a) (hx : a.get (mkTab n).x0i ≠ (mkTab n).x0i)
    (u : Fin 64) (hu : a.get u = u)
    (hsq : ∀ i, a.get (a.get i) = (mkTab n).mulT ((mkTab n).mulT u i) ((mkTab n).inv.get u))
    (hdisj : ∀ i, ((mkTab n).reach a (mkTab n).x0i).get i = true →
      ((mkTab n).reach a ((mkTab n).mulT (mkTab n).x0i (a.get (mkTab n).x0i))).get i = false)
    (hQ : ∀ i, (mkTab n).isQ.get i = true → i ≠ (mkTab n).one →
      ((mkTab n).reach a ((mkTab n).mulT (mkTab n).x0i (a.get (mkTab n).x0i))).get i = false) :
    (packA D a, u.val) ∈ D.adm := by
  obtain ⟨hd1, hx0, hg0, hrel, -, hL, -, -⟩ := dataOK_spec D hd
  unfold searchOK at hs
  rw [← beq_iff_eq.1 hs]
  have hA : ∀ i < 64, g6 (packA D a) i = av a i := fun i hi => packA_get ht ha hd hi
  have hx' : av a D.x0 ≠ D.x0 := by
    intro e
    apply hx
    rw [x0i_eq D ht]
    exact Fin.ext (by rw [val_f64 hx0]; exact e)
  have hsq0 : mul D (av a (gk 0)) (av a (gk 0)) = av a D.x0 := by
    rw [← av_mul ht ha (gk_lt 0) (gk_lt 0), hg0]
  have hcut : (mul D (av a (gk 0)) (av a (gk 0)) == D.x0) = false := by
    rw [hsq0]
    simpa using hx'
  have m0 : av a (gk 0) ∈ D.L.getD 0 [] := by
    rw [hL 0 (by decide), r64, List.mem_filter, List.mem_range, cls3_av ht ha hd1 (gk_lt 0)]
    exact ⟨av_lt _ _, beq_self_eq_true _⟩
  have m1 := nl_mem D hd 0 (by decide) (av_lt a (gk 0)) (av_lt a (gk 1))
    (cls3_av ht ha hd1 (gk_lt 1)) (pairOK_av ht ha hd1 (gk_lt 0) (gk_lt 1))
  have m2 := nl_mem D hd 2 (by decide) (av_lt a (gk 1)) (av_lt a (gk 2))
    (cls3_av ht ha hd1 (gk_lt 2)) (pairOK_av ht ha hd1 (gk_lt 1) (gk_lt 2))
  have m2' := nl_mem D hd 1 (by decide) (av_lt a (gk 0)) (av_lt a (gk 2))
    (cls3_av ht ha hd1 (gk_lt 2)) (pairOK_av ht ha hd1 (gk_lt 0) (gk_lt 2))
  have m3 := nl_mem D hd 5 (by decide) (av_lt a (gk 2)) (av_lt a (gk 3))
    (cls3_av ht ha hd1 (gk_lt 3)) (pairOK_av ht ha hd1 (gk_lt 2) (gk_lt 3))
  have m3a := nl_mem D hd 3 (by decide) (av_lt a (gk 0)) (av_lt a (gk 3))
    (cls3_av ht ha hd1 (gk_lt 3)) (pairOK_av ht ha hd1 (gk_lt 0) (gk_lt 3))
  have m3b := nl_mem D hd 4 (by decide) (av_lt a (gk 1)) (av_lt a (gk 3))
    (cls3_av ht ha hd1 (gk_lt 3)) (pairOK_av ht ha hd1 (gk_lt 1) (gk_lt 3))
  have hr : (D.rel.foldl (fun r k =>
      mul D r (hk (av a (gk 0)) (av a (gk 1)) (av a (gk 2)) (av a (gk 3)) k)) D.one == D.one)
      = true := by
    have e1 : (fun r k =>
        mul D r (hk (av a (gk 0)) (av a (gk 1)) (av a (gk 2)) (av a (gk 3)) k)) =
        (fun r k => mul D r (av a (gk k))) := by
      funext r k
      rw [hk_av ht ha]
    have h1 := rel_av ht ha D.rel hd1
    rw [av_one ht ha hd1, hrel, av_one ht ha hd1] at h1
    rw [e1, h1]
    exact beq_self_eq_true _
  have hne : (g6 (packA D a) D.x0 != D.x0) = true := by
    rw [hA D.x0 hx0]
    simpa using hx'
  have aX := agree_reach ht hd (packA D a) (mkTab n).x0i
  have aV := agree_reach ht hd (packA D a) ((mkTab n).mulT (mkTab n).x0i (a.get (mkTab n).x0i))
  rw [tblOf_packA ht ha hd] at aX aV
  have ex : ((mkTab n).x0i).val = D.x0 := by rw [x0i_eq D ht, val_f64 hx0]
  have ev : ((mkTab n).mulT (mkTab n).x0i (a.get (mkTab n).x0i)).val =
      mul D D.x0 (g6 (packA D a) D.x0) := by
    rw [mulT_eq D ht, val_f64_mul, ex, hA D.x0 hx0, x0i_eq D ht]
    rfl
  rw [ex] at aX
  rw [ev] at aV
  have hdm := mask_disj aX.1 (V := reachK D (packA D a) 12 (1 <<< mul D D.x0 (g6 (packA D a) D.x0)))
    (fun i hi hXi => by
      rw [← aV.2 ⟨i, hi⟩]
      exact hdisj ⟨i, hi⟩ (by rw [aX.2 ⟨i, hi⟩]; exact hXi))
  have hqm := mask_Q aV.1 (Q := D.Q) (o := D.one) (fun i hi hQi hio => by
      rw [← aV.2 ⟨i, hi⟩]
      refine hQ ⟨i, hi⟩ (by rw [isQ_eq D ht]; exact hQi) ?_
      intro e
      apply hio
      have e' := congrArg Fin.val e
      rwa [one_eq D ht, val_f64 hd1] at e')
  have hc : (reachK D (packA D a) 12 (1 <<< D.x0) &&&
      reachK D (packA D a) 12 (1 <<< mul D D.x0 (g6 (packA D a) D.x0)) == 0 &&
      ((reachK D (packA D a) 12 (1 <<< mul D D.x0 (g6 (packA D a) D.x0)) &&& D.Q) |||
        1 <<< D.one) == 1 <<< D.one) = true := by
    rw [hdm, hqm, beq_self_eq_true, beq_self_eq_true, Bool.and_self]
  have hsqA : ∀ i < 64, sqAt D (packA D a) u.val i = true := by
    intro i hi
    unfold sqAt
    rw [hA i hi, hA _ (av_lt _ _), beq_iff_eq, av, av, f64_val, hsq, mulT_eq D ht, mulT_eq D ht,
      inv_eq D ht, val_f64_mul, val_f64_g6, val_f64 hi, val_f64_mul]
  have hU : u.val ∈ r64.filter fun v => g6 (packA D a) v == v &&
      ((List.range 4).all fun k => sqAt D (packA D a) v (gk k)) &&
      r64.all (sqAt D (packA D a) v) := by
    rw [r64, List.mem_filter, List.mem_range]
    refine ⟨u.2, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨?_, fun k _ => hsqA _ (gk_lt k)⟩, fun i hi => hsqA i hi⟩
    rw [hA _ u.2, av, f64_val, hu]
  have hpair := pairsOf_mem D hU hc
  unfold search
  refine List.mem_flatMap.2 ⟨av a (gk 0), m0, ?_⟩
  rw [hcut, cond_false]
  refine List.mem_flatMap.2 ⟨av a (gk 1), m1.1, ?_⟩
  refine List.mem_flatMap.2 ⟨av a (gk 2), m2.1, ?_⟩
  rw [m2'.2, cond_true]
  refine List.mem_flatMap.2 ⟨av a (gk 3), m3.1, ?_⟩
  rw [bit_and, m3a.2, m3b.2, Bool.and_self, cond_true]
  unfold leaf
  rw [hr, cond_true, packA_def]
  dsimp only
  rw [hne, cond_true]
  exact hpair

end Main

theorem admP_of_mem {L : List (Nat × Nat)} {p : Nat × Nat} (hp : p ∈ L) :
    admP L (tblOf p.1) (f64 p.2) = true :=
  List.any_eq_true.2 ⟨p, hp, by simp⟩

section Generic

variable {n : ℕ} [NeZero n] (t : Tab n)

theorem finalG_of (P : Tbl → Fin 64 → Bool) (a : Tbl)
    (h : a.get t.x0i ≠ t.x0i → ∀ u, a.get u = u →
      (∀ i, a.get (a.get i) = t.mulT (t.mulT u i) (t.inv.get u)) →
      (∀ i, (t.reach a t.x0i).get i = true →
        (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = false) →
      (∀ i, t.isQ.get i = true → i ≠ t.one →
        (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = false) →
      t.wB a = true → P a u = true) :
    t.finalG P a = true := by
  unfold Tab.finalG
  rw [imp_eq_true]
  intro hx
  rw [List.all_eq_true]
  intro u _
  rw [imp_eq_true]
  intro h2
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
  rw [imp_eq_true]
  intro h3
  rw [imp_eq_true]
  intro h4
  rw [imp_eq_true]
  intro h5
  rw [List.all_eq_true] at h3 h4
  refine h (by simpa using hx) u h2.1 (fun i => by simpa using h2.2 i (List.mem_finRange i))
    (fun i hX => ?_) (fun i hq h1 => ?_) h5
  · have := h3 i (List.mem_finRange i)
    simpa [hX] using this
  · have := h4 i (List.mem_finRange i)
    rw [imp_eq_true] at this
    simpa using this (by simp [hq, h1])

theorem claimG_of_aut (P : Tbl → Fin 64 → Bool) (h : ∀ a, t.IsAutT a → t.finalG P a = true) :
    t.claimG P = true := by
  unfold Tab.claimG
  simp only [List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true]
  intro h0 _ h1 _ h2 _ h3 _ ha
  exact h _ ((Tab.isAutB_iff t _).1 ha)

end Generic

section Claims

variable {D}

theorem claimG_adm {n : ℕ} [NeZero n] (ht : transOK D n = true) (hd : dataOK D = true)
    (hs : searchOK D = true) : (mkTab n).claimG (admP D.adm) = true := by
  apply claimG_of_aut
  intro a ha
  apply finalG_of
  intro hx u hu hsq hdj hq _
  have hm := admP_of_mem (mem_adm ht hd hs ha hx u hu hsq hdj hq)
  rwa [tblOf_packA ht ha hd, f64_val] at hm

theorem claimG_adm7 (ht : transOK D 7 = true) (hd : dataOK D = true) (hs : searchOK D = true)
    (hw : wbOK D 7 = true) : (mkTab 7).claimG (admP D.adm7) = true := by
  apply claimG_of_aut
  intro a ha
  apply finalG_of
  intro hx u hu hsq hdj hq hW
  have hm := mem_adm ht hd hs ha hx u hu hsq hdj hq
  unfold wbOK at hw
  have hm7 : (packA D a, u.val) ∈ D.adm7 := by
    rw [← beq_iff_eq.1 hw, List.mem_filter]
    refine ⟨hm, ?_⟩
    rw [tblOf_packA ht ha hd]
    exact hW
  have h := admP_of_mem hm7
  rwa [tblOf_packA ht ha hd, f64_val] at h

end Claims

end CFSG.KC.GH74Tab

end
