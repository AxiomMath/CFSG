module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Dyadic
public import CFSG.Certificates.Kernel.BabyMonster.Native.F2n
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Bound.Init
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.BM.Dy

open CFSG.KC.BM CFSG.KC.BM.Lat CFSG.KC.BM.B64 CFSG.KC.YModel

@[expose] def fld (x t : Nat) : Nat := x / 2 ^ (16 * t) % 65536

@[expose] noncomputable def ent (Bs : List (List Nat)) (j c : Nat) : Nat :=
  if c < j then 0 else fld (recOf Bs j) (c - j)

@[expose] noncomputable def blocksOK (Bs : List (List Nat)) : Bool :=
  andB (Nat.beq (lenLL Bs) (nat_lit 69))
    (Nat.rec (motive := fun _ => Bool) true
      (fun s ih => andB ih (Nat.beq (lenL (lgetL Bs s)) (rowsSn (nat_lit 4371) s))) (nat_lit 69))

@[expose] noncomputable def contV (Bs : List (List Nat)) (i : Nat) : Nat :=
  Nat.shiftRight (Nat.land (Nat.mul (Nat.div (nat_lit 128) (Nat.land (recOf Bs i) (nat_lit 65535)))
    (recOf Bs i)) (dyMask (nat_lit 128))) (nat_lit 16)

@[expose] noncomputable def contOK (Bs : List (List Nat)) (i : Nat) : Bool :=
  Nat.blt (dyElim (nat_lit 128) Bs (Nat.succ i) (contV Bs i)) dyFail

theorem contOK_of {Bs : List (List Nat)} {s k v : Nat}
    (h : Nat.blt (dyElim (nat_lit 128) Bs k v) dyFail = true) (hk : k = Nat.succ s)
    (hv : v = contV Bs s) : contOK Bs s = true := by
  subst hk hv
  exact h

theorem andB_true {b c : Bool} (h : andB b c = true) : b = true ∧ c = true := by
  cases b
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem recAnd_sound {X : Nat → Bool} : ∀ {n : Nat},
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (X i)) n = true →
      ∀ i < n, X i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have e : Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (X i)) (n + 1) =
        andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (X i)) n) (X n) := rfl
    obtain ⟨h1, h2⟩ := andB_true (e ▸ h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact recAnd_sound h1 i hi
    · exact h2

theorem fld_zero (x : Nat) : fld x 0 = x % 65536 := by
  simp [fld]

theorem fld_succ (x t : Nat) : fld x (t + 1) = fld (x / 65536) t := by
  rw [fld, fld, Nat.div_div_eq_div_mul, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (16 * t))]

theorem fld_lt (x t : Nat) : fld x t < 65536 := Nat.mod_lt _ (by decide)

theorem fld_testBit (x t i : Nat) :
    (fld x t).testBit i = (decide (i < 16) && x.testBit (16 * t + i)) := by
  rw [fld, show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.add_comm i]

theorem testBit_of_fld (x i : Nat) : x.testBit i = (fld x (i / 16)).testBit (i % 16) := by
  rw [fld_testBit, decide_eq_true (Nat.mod_lt i (by decide)), Bool.true_and, Nat.div_add_mod]

theorem fld_land (x y t : Nat) : fld (x &&& y) t = fld x t &&& fld y t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, fld_testBit, fld_testBit, fld_testBit, Nat.testBit_and]
  cases decide (i < 16) <;> rfl

theorem fld_shr16 (x t : Nat) : fld (x >>> 16) t = fld x (t + 1) := by
  rw [fld_succ, Nat.shiftRight_eq_div_pow]

theorem eq_zero_of_fld {x : Nat} (h : ∀ t, fld x t = 0) : x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_of_fld, h, Nat.zero_testBit, Nat.zero_testBit]

theorem lt_of_fld {x n : Nat} (h : ∀ t, n ≤ t → fld x t = 0) : x < 2 ^ (16 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_of_fld, h _ (by omega), Nat.zero_testBit]

theorem fld_of_lt {x n t : Nat} (hx : x < 2 ^ (16 * n)) (ht : n ≤ t) : fld x t = 0 := by
  rw [fld, Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem fld_cons_zero {a : Nat} (b : Nat) (ha : a < 65536) : fld (a + 65536 * b) 0 = a := by
  rw [fld_zero]
  omega

theorem fld_cons_succ {a : Nat} (b t : Nat) (ha : a < 65536) :
    fld (a + 65536 * b) (t + 1) = fld b t := by
  rw [fld_succ]
  congr 1
  omega

theorem fld_add : ∀ (t : Nat) {a b : Nat}, (∀ t, fld a t + fld b t < 65536) →
    fld (a + b) t = fld a t + fld b t
  | 0, a, b, h => by
    have := h 0
    simp only [fld_zero] at this ⊢
    omega
  | t + 1, a, b, h => by
    have h0 := h 0
    simp only [fld_zero] at h0
    have e : (a + b) / 65536 = a / 65536 + b / 65536 := by omega
    rw [fld_succ, fld_succ, fld_succ, e, fld_add t (fun t' => by
      have := h (t' + 1)
      rwa [fld_succ, fld_succ] at this)]

theorem fld_mul : ∀ (t : Nat) {c b : Nat}, (∀ t, c * fld b t < 65536) →
    fld (c * b) t = c * fld b t
  | 0, c, b, h => by
    have h0 := h 0
    rw [fld_zero] at h0 ⊢
    rw [fld_zero]
    conv_lhs => rw [← Nat.mod_add_div b 65536]
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  | t + 1, c, b, h => by
    have h0 := h 0
    rw [fld_zero] at h0
    have e : c * b / 65536 = c * (b / 65536) := by
      conv_lhs => rw [← Nat.mod_add_div b 65536]
      rw [Nat.mul_add, Nat.mul_left_comm, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt h0, Nat.zero_add]
    rw [fld_succ, fld_succ, e, fld_mul t (fun t' => by
      have := h (t' + 1)
      rwa [fld_succ] at this)]

theorem shl1 (n : Nat) : Nat.shiftLeft (nat_lit 1) n = 2 ^ n := by
  rw [Nat.shiftLeft_eq']
  exact Nat.one_shiftLeft n

theorem rep_eq (x p c : Nat) : rep x p c = x * ((2 ^ (p * c) - 1) / (2 ^ p - 1)) := by
  unfold rep
  rw [shl1, shl1]
  rfl

theorem geom16 (c : Nat) :
    (2 ^ (16 * (c + 1)) - 1) / (2 ^ 16 - 1) = 1 + 65536 * ((2 ^ (16 * c) - 1) / (2 ^ 16 - 1)) := by
  have hdvd : ∀ c : Nat, ∃ g, 2 ^ (16 * c) - 1 = 65535 * g := by
    intro c
    induction c with
    | zero => exact ⟨0, rfl⟩
    | succ c ih =>
      obtain ⟨g, hg⟩ := ih
      have hp : 1 ≤ 2 ^ (16 * c) := Nat.one_le_two_pow
      refine ⟨65536 * g + 1, ?_⟩
      rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 16 = 65536 from rfl]
      omega
  obtain ⟨g, hg⟩ := hdvd c
  have hp : 1 ≤ 2 ^ (16 * c) := Nat.one_le_two_pow
  have e16 : (2 : Nat) ^ 16 - 1 = 65535 := rfl
  have h3 : 2 ^ (16 * (c + 1)) - 1 = 65535 * (1 + 65536 * g) := by
    rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 16 = 65536 from rfl]
    omega
  rw [e16, h3, hg, Nat.mul_div_cancel_left _ (by decide), Nat.mul_div_cancel_left _ (by decide)]

theorem rep_succ (x c : Nat) : rep x 16 (c + 1) = x + 65536 * rep x 16 c := by
  rw [rep_eq, rep_eq, geom16, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

theorem rep_zero (x : Nat) : rep x 16 0 = 0 := by
  rw [rep_eq]
  simp

theorem fld_rep {x : Nat} (hx : x < 65536) : ∀ (c t : Nat), fld (rep x 16 c) t = if t < c then x else 0
  | 0, t => by
    rw [rep_zero, ite_eq_right (Nat.not_lt_zero t)]
    simp [fld]
  | c + 1, 0 => by
    rw [rep_succ, fld_cons_zero _ hx, ite_eq_left (Nat.succ_pos c)]
  | c + 1, t + 1 => by
    rw [rep_succ, fld_cons_succ _ _ hx, fld_rep hx c t]
    simp only [Nat.add_lt_add_iff_right]

theorem fld_dyMask {m : Nat} (h0 : 0 < m) (hm : m ≤ 65536) (t : Nat) :
    fld (dyMask m) t = if t < 4371 then m - 1 else 0 := by
  change fld (rep (m - 1) 16 4371) t = _
  exact fld_rep (by omega) 4371 t

theorem fld_land_dyMask {e : Nat} (he : e ≤ 16) (y t : Nat) :
    fld (y &&& dyMask (2 ^ e)) t = if t < 4371 then fld y t % 2 ^ e else 0 := by
  have h1 : 0 < 2 ^ e := Nat.two_pow_pos e
  have h2 : 2 ^ e ≤ 65536 := Nat.pow_le_pow_right (by decide) he
  rw [fld_land, fld_dyMask h1 h2]
  split
  · exact Nat.and_two_pow_sub_one_eq_mod _ _
  · exact Nat.and_zero _

theorem diagOK_sound {p : Nat × Nat} {Bs : List (List Nat)} (h : diagOK p Bs = true) :
    ∀ i < 4371, (48 ≤ chAt p.1 i ∧ chAt p.1 i ≤ 55) ∧
      fld (recOf Bs i) 0 = 2 ^ (chAt p.1 i - 48) := by
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  generalize hn : nat_lit 4371 = n at h
  intro i hi
  have hi' : i < n := hi
  obtain ⟨h1, h2⟩ := andB_true (recAnd_sound h i hi')
  obtain ⟨h3, h4⟩ := andB_true h1
  refine ⟨⟨Nat.le_of_ble_eq_true h3, Nat.le_of_ble_eq_true h4⟩, ?_⟩
  have e := Nat.eq_of_beq_eq_true h2
  have e1 : Nat.land (recOf Bs i) 65535 = recOf Bs i % 2 ^ 16 :=
    Nat.and_two_pow_sub_one_eq_mod _ 16
  have e2 : Nat.shiftLeft 1 (Nat.sub (chAt p.1 i) 48) = 2 ^ (chAt p.1 i - 48) := by
    change 1 <<< (chAt p.1 i - 48) = _
    rw [Nat.one_shiftLeft]
  rw [fld, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  rw [e1, e2] at e
  exact e

theorem contain_of {Bs : List (List Nat)} {ex : Nat → Nat}
    (hp : ∀ i < 4371, ex i ≤ 7 ∧ fld (recOf Bs i) 0 = 2 ^ ex i)
    (hq : ∀ i < 4371, ∃ q : ℕ → ℤ, ∀ c < 4371, i < c →
      ((128 / fld (recOf Bs i) 0 * ent Bs i c : ℕ) : ℤ) ≡
        ∑ j ∈ Finset.Ico (i + 1) 4371, q j * (ent Bs j c : ℤ) [ZMOD 128]) :
    ∀ i : Fin 4371, Pi.single i (128 : ℤ) ∈
      Submodule.span ℤ (Set.range fun t : Fin 4371 => fun c : Fin 4371 => (ent Bs t c : ℤ)) := by
  set L := Submodule.span ℤ (Set.range fun t : Fin 4371 => fun c : Fin 4371 => (ent Bs t c : ℤ))
  have row : ∀ t (ht : t < 4371), (fun c : Fin 4371 => (ent Bs t c : ℤ)) ∈ L :=
    fun t ht => Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩
  suffices H : ∀ d, ∀ i : Fin 4371, 4370 - (i : ℕ) ≤ d → Pi.single i (128 : ℤ) ∈ L from
    fun i => H _ i le_rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro i hid
  obtain ⟨he, hpiv⟩ := hp i i.2
  obtain ⟨q, hqc⟩ := hq i i.2
  have ha : 128 / 2 ^ ex i * 2 ^ ex i = 128 :=
    Nat.div_mul_cancel (Nat.pow_dvd_pow 2 he : 2 ^ ex i ∣ 2 ^ 7)
  set u : Fin 4371 → ℤ := ((128 / 2 ^ ex i : ℕ) : ℤ) • (fun c : Fin 4371 => (ent Bs i c : ℤ)) -
    ∑ j ∈ Finset.Ico ((i : ℕ) + 1) 4371, q j • fun c : Fin 4371 => (ent Bs j c : ℤ) with hu
  have uc : ∀ c : Fin 4371, u c = ((128 / 2 ^ ex i : ℕ) : ℤ) * ent Bs i c -
      ∑ j ∈ Finset.Ico ((i : ℕ) + 1) 4371, q j * (ent Bs j c : ℤ) := by
    intro c
    rw [hu, Pi.sub_apply, Finset.sum_apply]
    rfl
  have hlow : ∀ c : Fin 4371, (c : ℕ) ≤ i →
      ∑ j ∈ Finset.Ico ((i : ℕ) + 1) 4371, q j * (ent Bs j c : ℤ) = 0 := by
    intro c hc
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [ent, ite_eq_left (by omega)]
    simp
  have hdiv : ∀ c : Fin 4371, i < c → (128 : ℤ) ∣ u c := by
    intro c hc
    have := (Int.modEq_iff_dvd.1 (hqc c c.2 (Fin.lt_def.1 hc)))
    rw [uc, ← hpiv]
    have e : ((128 / fld (recOf Bs i) 0 : ℕ) : ℤ) * (ent Bs i c : ℤ) -
        ∑ j ∈ Finset.Ico ((i : ℕ) + 1) 4371, q j * (ent Bs j c : ℤ) =
        -(∑ j ∈ Finset.Ico ((i : ℕ) + 1) 4371, q j * (ent Bs j c : ℤ) -
          ((128 / fld (recOf Bs i) 0 * ent Bs i c : ℕ) : ℤ)) := by
      push_cast
      ring
    rw [e]
    exact (Int.dvd_neg).2 this
  have key : Pi.single i (128 : ℤ) = u - ∑ c ∈ Finset.univ.filter (fun c : Fin 4371 => i < c),
      (u c / 128) • Pi.single c (128 : ℤ) := by
    funext c
    rw [Pi.sub_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_trichotomy c i with h | h | h
    · have h' := Fin.lt_def.1 h
      rw [ite_eq_right (Fin.ne_of_lt h), ite_eq_right (lt_asymm h), uc, hlow c h'.le, ent,
        ite_eq_left h']
      simp
    · rw [h, ite_eq_left rfl, ite_eq_right (lt_irrefl _), uc, hlow i le_rfl, ent,
        ite_eq_right (lt_irrefl _), Nat.sub_self, hpiv, sub_zero, sub_zero]
      exact_mod_cast ha.symm
    · rw [ite_eq_right (Fin.ne_of_gt h), ite_eq_left h, Int.ediv_mul_cancel (hdiv c h), sub_self]
  rw [key]
  refine L.sub_mem ?_ (L.sum_mem fun c hc => L.smul_mem _ ?_)
  · refine L.sub_mem (L.smul_mem _ (row i i.2)) (L.sum_mem fun j hj => L.smul_mem _ (row j ?_))
    rw [Finset.mem_Ico] at hj
    exact hj.2
  · rw [Finset.mem_filter] at hc
    have hc2 := hc.2
    rw [Fin.lt_def] at hc2
    have := c.2
    exact ih (4370 - c) (by omega) c le_rfl

theorem getD_lt {α : Type} (l : List α) (d : α) {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem getD_app_left (l l' : List Nat) {n : Nat} (h : n < l.length) :
    (l ++ l').getD n 0 = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right (l l' : List Nat) {n : Nat} (h : l.length ≤ n) :
    (l ++ l').getD n 0 = l'.getD (n - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem dyLgetL_eq : ∀ (l : List (List Nat)) (i : Nat), lgetL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    change lgetL l i = _
    rw [dyLgetL_eq l i, List.getD_cons_succ]

theorem dyLget_eq : ∀ (l : List Nat) (i : Nat), lget l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    change lget l i = _
    rw [dyLget_eq l i, List.getD_cons_succ]

theorem dyLenL_eq : ∀ l : List Nat, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [dyLenL_eq l]
    rfl

theorem dyLenLL_eq : ∀ l : List (List Nat), lenLL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenLL l) = _
    rw [dyLenLL_eq l]
    rfl

theorem dyRecOf_eq (Bs : List (List Nat)) (i : Nat) :
    recOf Bs i = (Bs.getD (i / 64) []).getD (i % 64) 0 := by
  unfold recOf
  rw [dyLgetL_eq, dyLget_eq]
  rfl

theorem flatten_getElem : ∀ (L : List (List Nat)),
    (∀ s, s + 1 < L.length → (L.getD s []).length = 64) →
    (∀ s < L.length, (L.getD s []).length ≤ 64) →
    ∀ idx (h : idx < L.flatten.length), L.flatten[idx] = (L.getD (idx / 64) []).getD (idx % 64) 0
  | [], _, _, idx, h => absurd h (by simp)
  | b :: L, h64, hle, idx, h => by
    simp only [List.flatten_cons] at h ⊢
    have hb : b.length ≤ 64 := by simpa using hle 0 (by simp)
    by_cases hi : idx < b.length
    · rw [List.getElem_append_left hi, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        List.getD_cons_zero, getD_lt _ _ hi]
    · rw [List.length_append] at h
      have hL : 0 < L.length := by
        rcases L with _ | ⟨c, L'⟩
        · simp at h
          omega
        · simp
      have hb64 : b.length = 64 := by simpa using h64 0 (by simp; omega)
      rw [List.getElem_append_right (by omega),
        flatten_getElem L (fun s hs => by simpa using h64 (s + 1) (by simp; omega))
          (fun s hs => by simpa using hle (s + 1) (by simp; omega))]
      have e1 : idx / 64 = (idx - b.length) / 64 + 1 := by omega
      have e2 : idx % 64 = (idx - b.length) % 64 := by omega
      rw [e1, e2, List.getD_cons_succ]

theorem rowsSn_64 : ∀ s < 68, rowsSn 4371 s = 64 := by decide

theorem rowsSn_le : ∀ s < 69, rowsSn 4371 s ≤ 64 := by decide

theorem rowsSn_sum : ((List.range 69).map (rowsSn 4371)).sum = 4371 := by decide

theorem blocks_flatten {Bs : List (List Nat)} (hB : blocksOK Bs = true) :
    Bs.flatten.length = 4371 ∧
      ∀ idx (h : idx < Bs.flatten.length), Bs.flatten[idx] = recOf Bs idx := by
  obtain ⟨h1, h2⟩ := andB_true hB
  have hlen : Bs.length = 69 := by
    rw [← dyLenLL_eq]
    exact Nat.eq_of_beq_eq_true h1
  generalize hn : nat_lit 69 = n at h2
  have hs : ∀ s < 69, (Bs.getD s []).length = rowsSn 4371 s := by
    intro s hs
    have := Nat.eq_of_beq_eq_true (recAnd_sound h2 s (hn ▸ hs))
    rwa [dyLenL_eq, dyLgetL_eq] at this
  refine ⟨?_, fun idx h => ?_⟩
  · rw [List.length_flatten, ← rowsSn_sum]
    congr 1
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    have hi : i < 69 := by simpa [hlen] using h1
    rw [← hs i hi, getD_lt _ _ (by omega)]
  · rw [flatten_getElem Bs (fun s h => by rw [hs s (by omega)]; exact rowsSn_64 s (by omega))
      (fun s h => by rw [hs s (by omega)]; exact rowsSn_le s (by omega)), dyRecOf_eq]

theorem land65535 (x : Nat) : Nat.land x (nat_lit 65535) = fld x 0 := by
  change x &&& (2 ^ 16 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, fld_zero]

theorem dyRowOK_facts {n j b : Nat} (hn : n ≤ 4372) (h : dyRowOK n j b = true) :
    (∃ e, e ≤ 7 ∧ fld b 0 = 2 ^ e) ∧ b < 2 ^ (16 * (n - j)) ∧ ∀ t, 1 ≤ t → fld b t < 128 := by
  obtain ⟨hp, hr⟩ := andB_true h
  obtain ⟨hp0, hp⟩ := andB_true hp
  obtain ⟨hp1, hp2⟩ := andB_true hp
  obtain ⟨hs, hm⟩ := andB_true hr
  rw [land65535] at hp0 hp1 hp2
  have hp0' := Nat.le_of_ble_eq_true hp0
  have hp1' := Nat.le_of_ble_eq_true hp1
  have hp2' := Nat.eq_of_beq_eq_true hp2
  have hb : b < 2 ^ (16 * (n - j)) := by
    have e := Nat.eq_of_beq_eq_true hs
    change b >>> (16 * (n - j)) = 0 at e
    rw [Nat.shiftRight_eq_div_pow] at e
    have := Nat.div_add_mod b (2 ^ (16 * (n - j)))
    rw [e, Nat.mul_zero, Nat.zero_add] at this
    rw [← this]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨?_, hb, fun t ht => ?_⟩
  · have key : ∀ p : Nat, p < 129 → (p == 0 || p &&& (p - 1) != 0 ||
        (List.range 8).any fun e => p == 2 ^ e) = true := by decide
    have h := key _ (Nat.lt_succ_of_le hp1')
    have h0 : (fld b 0 == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    have h2 : (fld b 0 &&& (fld b 0 - 1) != 0) = false := by
      rw [bne_eq_false_iff_eq]
      exact hp2'
    rw [h0, h2, Bool.false_or, Bool.false_or, List.any_eq_true] at h
    obtain ⟨e, he, hpe⟩ := h
    exact ⟨e, by rw [List.mem_range] at he; omega, beq_iff_eq.1 hpe⟩
  · by_cases ht' : t < 4372
    · have e := congrArg (fun x => fld x (t - 1)) (Nat.eq_of_beq_eq_true hm)
      simp only at e
      change fld ((b >>> 16) &&& dyMask 65536) (t - 1) =
        fld ((b >>> 16) &&& dyMask 128) (t - 1) at e
      rw [show (65536 : Nat) = 2 ^ 16 from rfl, show (128 : Nat) = 2 ^ 7 from rfl] at e
      rw [fld_land_dyMask (le_refl 16), fld_land_dyMask (by decide), ite_eq_left (by omega),
        ite_eq_left (by omega), Nat.mod_eq_of_lt (b := 2 ^ 16) (fld_lt _ _), fld_shr16,
        Nat.sub_add_cancel ht] at e
      rw [e]
      exact Nat.mod_lt _ (by decide)
    · have hb' : b < 2 ^ (16 * (n - j)) := hb
      rw [fld_of_lt (t := t) hb' (by omega)]
      decide

theorem dyRowOK_sound {n j b : Nat} (hn : n ≤ 4372) (h : dyRowOK n j b = true) :
    ∀ t, 1 ≤ t → t < n - j → fld b t < 128 :=
  fun t ht _ => (dyRowOK_facts hn h).2.2 t ht

@[expose] noncomputable def dyStep (m M b : Nat) (K : Nat → Nat → Nat → Nat → Nat)
    (v out j bad : Nat) : Nat :=
  (fun x => Bool.rec (motive := fun _ => Nat)
      ((fun p => (fun q => K
          (Nat.shiftRight (Nat.land (Nat.add v (Nat.mul (Nat.sub m q) b)) M) (nat_lit 16))
          (Nat.lor out (Nat.shiftLeft (Nat.land q (nat_lit 1)) j))
          (Nat.succ j)
          (Nat.lor bad (Nat.land x (Nat.sub p (nat_lit 1)))))
        (Nat.div x p)) (Nat.land b (nat_lit 65535)))
      (K (Nat.shiftRight v (nat_lit 16)) out (Nat.succ j) bad)
      (Nat.beq x (nat_lit 0)))
    (Nat.land v (nat_lit 65535))

@[expose] noncomputable def dyInSkip (m M k : Nat) (K : Nat → Nat → Nat → Nat → Nat)
    (blk : List Nat) : Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun v out j bad => K v out j bad)
    (fun b _ ih2 v out j bad => Bool.rec (motive := fun _ => Nat) (ih2 v out (Nat.succ j) bad)
      (dyStep m M b ih2 v out j bad) (Nat.ble k j)) blk

@[expose] noncomputable def dyInNo (m M : Nat) (K : Nat → Nat → Nat → Nat → Nat)
    (blk : List Nat) : Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun v out j bad => K v out j bad)
    (fun b _ ih2 v out j bad => dyStep m M b ih2 v out j bad) blk

@[expose] noncomputable def dyFin (v out _j bad : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) dyFail
    (Bool.rec (motive := fun _ => Nat) dyFail out (Nat.beq bad (nat_lit 0))) (Nat.beq v (nat_lit 0))

@[expose] noncomputable def dyOuter (m M k : Nat) (Bs : List (List Nat)) :
    Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) dyFin
    (fun blk _ ih v out j bad => Bool.rec (motive := fun _ => Nat)
      (dyInSkip m M k ih blk v out j bad) (dyInNo m M ih blk v out j bad) (Nat.ble k j)) Bs

theorem dyElim_eq (m : Nat) (Bs : List (List Nat)) (k v : Nat) :
    dyElim m Bs k v = dyOuter m (dyMask m) k Bs v 0 0 0 := rfl

@[irreducible] noncomputable def comb (Bs : List (List Nat)) (Q : ℕ → ℕ) (c : ℕ) : ℤ :=
  ∑ j' ∈ Finset.range 4371, (Q j' : ℤ) * (ent Bs j' c : ℤ)

theorem comb_eq (Bs : List (List Nat)) (Q : ℕ → ℕ) (c : ℕ) :
    comb Bs Q c = ∑ j' ∈ Finset.range 4371, (Q j' : ℤ) * (ent Bs j' c : ℤ) := by
  unfold comb
  rfl

@[expose] def DyGood (m k v0 : Nat) (Bs : List (List Nat)) (j v out : Nat) : Prop :=
  ∃ Q : ℕ → ℕ, (∀ j', Q j' ≠ 0 → k ≤ j' ∧ j' < j) ∧
    (∀ j', out.testBit j' = decide (Q j' % 2 = 1)) ∧
    v < 2 ^ (16 * (4371 - j)) ∧ (∀ t, fld v t < m) ∧
    ∀ c, k ≤ c → c < 4371 →
      ((fld v0 (c - k) : ℕ) : ℤ) - comb Bs Q c ≡
        ((if j ≤ c then fld v (c - j) else 0 : ℕ) : ℤ) [ZMOD m]

@[expose] def DyInv (m k v0 : Nat) (Bs : List (List Nat)) (j v out bad : Nat) : Prop :=
  (j < k ∧ v = v0 ∧ out = 0 ∧ bad = 0) ∨ (k ≤ j ∧ j ≤ 4371 ∧ (bad = 0 → DyGood m k v0 Bs j v out))

@[expose] def DyRes (m k v0 : Nat) (Bs : List (List Nat)) (r : Nat) : Prop :=
  ∃ Q : ℕ → ℕ, (∀ j', Q j' ≠ 0 → k ≤ j' ∧ j' < 4371) ∧
    (∀ j', r.testBit j' = decide (Q j' % 2 = 1)) ∧
    ∀ c, k ≤ c → c < 4371 →
      ((fld v0 (c - k) : ℕ) : ℤ) ≡ comb Bs Q c [ZMOD m]

@[expose] def DyClaim (m k v0 : Nat) (Bs : List (List Nat)) (j : Nat)
    (F : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ v out bad, DyInv m k v0 Bs j v out bad → F v out j bad ≠ dyFail → DyRes m k v0 Bs (F v out j bad)

theorem good_init {m k v0 : Nat} {Bs : List (List Nat)} (hv : v0 < 2 ^ (16 * (4371 - k)))
    (hf : ∀ t, fld v0 t < m) : DyGood m k v0 Bs k v0 0 := by
  refine ⟨fun _ => 0, fun j' h => absurd rfl h, fun j' => by simp, hv, hf, fun c hkc _ => ?_⟩
  rw [ite_eq_left hkc, comb_eq]
  simp only [Nat.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  exact Int.ModEq.refl _

theorem comb_add (Bs : List (List Nat)) (Q : ℕ → ℕ) {j : ℕ} (hj : j < 4371) (q c : ℕ) :
    comb Bs (fun j' => Q j' + if j' = j then q else 0) c =
      comb Bs Q c + (q : ℤ) * (ent Bs j c : ℤ) := by
  rw [comb_eq, comb_eq]
  simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_zero,
    ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range 4371) j, ite_eq_left (Finset.mem_range.2 hj)]

theorem good_step0 {m k v0 : Nat} {Bs : List (List Nat)} {j v out : Nat} (hj : j < 4371)
    (hG : DyGood m k v0 Bs j v out) (hx : fld v 0 = 0) :
    DyGood m k v0 Bs (j + 1) (v >>> 16) out := by
  obtain ⟨Q, hQs, hQo, hvb, hvf, hres⟩ := hG
  refine ⟨Q, fun j' h => ⟨(hQs j' h).1, by have := (hQs j' h).2; omega⟩, hQo, ?_,
    fun t => by rw [fld_shr16]; exact hvf _, fun c hkc hc => ?_⟩
  · apply lt_of_fld
    intro t ht
    rw [fld_shr16]
    exact fld_of_lt hvb (by omega)
  · have h := hres c hkc hc
    by_cases hjc : j + 1 ≤ c
    · rw [ite_eq_left hjc, fld_shr16]
      rw [ite_eq_left (by omega)] at h
      have e : c - (j + 1) + 1 = c - j := by omega
      rwa [e]
    · rw [ite_eq_right hjc]
      by_cases hcj : c = j
      · subst hcj
        rwa [ite_eq_left le_rfl, Nat.sub_self, hx] at h
      · rwa [ite_eq_right (by omega)] at h

theorem testBit_mod2_shl (q j j' : Nat) :
    ((q % 2) <<< j).testBit j' = (decide (j' = j) && decide (q % 2 = 1)) := by
  rw [Nat.shiftLeft_eq, Nat.testBit_mul_two_pow]
  by_cases h : j' = j
  · subst h
    simp [Nat.testBit_zero]
  · rw [decide_eq_false h, Bool.false_and]
    by_cases h' : j ≤ j'
    · rw [decide_eq_true h', Bool.true_and]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt q (by decide))
        (Nat.le_self_pow (by omega) 2))
    · rw [decide_eq_false h', Bool.false_and]

theorem good_step1 {e : Nat} (he : e ≤ 8) {k v0 : Nat} {Bs : List (List Nat)} {j v out : Nat}
    (hkj : k ≤ j) (hj : j < 4371) (hrow : dyRowOK 4371 j (recOf Bs j) = true)
    (hG : DyGood (2 ^ e) k v0 Bs j v out) (hdiv : fld v 0 % fld (recOf Bs j) 0 = 0) :
    DyGood (2 ^ e) k v0 Bs (j + 1)
      (((v + (2 ^ e - fld v 0 / fld (recOf Bs j) 0) * recOf Bs j) &&& dyMask (2 ^ e)) >>> 16)
      (out ||| ((fld v 0 / fld (recOf Bs j) 0 % 2) <<< j)) := by
  obtain ⟨Q, hQs, hQo, hvb, hvf, hres⟩ := hG
  obtain ⟨⟨e', he', hp⟩, hb, hbf⟩ := dyRowOK_facts (by decide) hrow
  set b := recOf Bs j with hbdef
  set m := 2 ^ e with hmdef
  set x := fld v 0 with hxdef
  set q := x / fld b 0 with hqdef
  have hm0 : 0 < m := Nat.two_pow_pos e
  have hm256 : m ≤ 256 := Nat.pow_le_pow_right (by decide) he
  have hxm : x < m := hvf 0
  have hqm : q ≤ m := le_trans (Nat.div_le_self _ _) hxm.le
  have hp0 : 0 < fld b 0 := by rw [hp]; exact Nat.two_pow_pos e'
  have hqp : q * fld b 0 = x := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  have hb128 : ∀ t, fld b t ≤ 128 := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [hp]
      exact Nat.pow_le_pow_right (by decide) he'
    · exact (hbf t ht).le
  have hmul' : ∀ t, (m - q) * fld b t ≤ 256 * 128 := fun t =>
    Nat.mul_le_mul (le_trans (Nat.sub_le m q) hm256) (hb128 t)
  have hmul : ∀ t, (m - q) * fld b t < 65536 := fun t => lt_of_le_of_lt (hmul' t) (by decide)
  have hy : ∀ t, fld (v + (m - q) * b) t = fld v t + (m - q) * fld b t := by
    intro t
    rw [fld_add t (fun t => by
      rw [fld_mul t hmul]
      have := hvf t
      have := hmul' t
      omega), fld_mul t hmul]
  have hv' : ∀ t, fld (((v + (m - q) * b) &&& dyMask m) >>> 16) t =
      if t + 1 < 4371 then (fld v (t + 1) + (m - q) * fld b (t + 1)) % m else 0 := by
    intro t
    rw [fld_shr16, fld_land_dyMask (by omega), hy]
  refine ⟨fun j' => Q j' + if j' = j then q else 0, fun j' h => ?_, fun j' => ?_, ?_, fun t => ?_,
    fun c hkc hc => ?_⟩
  · by_cases hjj : j' = j
    · exact ⟨hjj ▸ hkj, by omega⟩
    · simp only [hjj, ite_false, Nat.add_zero] at h
      exact ⟨(hQs j' h).1, by have := (hQs j' h).2; omega⟩
  · rw [Nat.testBit_or, testBit_mod2_shl, hQo]
    by_cases hjj : j' = j
    · subst hjj
      have hQ0 : Q j' = 0 := by
        by_contra h
        have := (hQs j' h).2
        omega
      simp [hQ0]
    · simp [hjj]
  · apply lt_of_fld
    intro t ht
    rw [hv']
    split
    · rw [fld_of_lt (t := t + 1) hvb (by omega), fld_of_lt (t := t + 1) hb (by omega)]
      simp
    · rfl
  · rw [hv']
    split
    · exact Nat.mod_lt _ hm0
    · exact hm0
  · rw [comb_add Bs Q hj]
    have h := hres c hkc hc
    have hent : ent Bs j c = if c < j then 0 else fld b (c - j) := rfl
    by_cases hjc : j + 1 ≤ c
    · rw [ite_eq_left hjc, hv', ite_eq_left (by omega)]
      rw [ite_eq_left (by omega)] at h
      rw [hent, ite_eq_right (by omega)]
      have e1 : c - (j + 1) + 1 = c - j := by omega
      rw [e1]
      set E := fld b (c - j)
      set F := fld v (c - j)
      calc ((fld v0 (c - k) : ℕ) : ℤ) - (comb Bs Q c + (q : ℤ) * (E : ℤ))
          = (((fld v0 (c - k) : ℕ) : ℤ) - comb Bs Q c) - (q : ℤ) * (E : ℤ) := by ring
        _ ≡ (F : ℤ) - (q : ℤ) * (E : ℤ) [ZMOD m] := h.sub_right _
        _ ≡ ((F + (m - q) * E : ℕ) : ℤ) [ZMOD m] := by
          rw [Int.modEq_iff_dvd]
          refine ⟨(E : ℤ), ?_⟩
          push_cast [Nat.cast_sub hqm]
          ring
        _ ≡ (((F + (m - q) * E) % m : ℕ) : ℤ) [ZMOD m] := by
          rw [Int.natCast_emod]
          exact (Int.mod_modEq _ _).symm
    · rw [ite_eq_right hjc]
      by_cases hcj : c = j
      · subst hcj
        rw [ite_eq_left le_rfl, Nat.sub_self] at h
        rw [hent, ite_eq_right (lt_irrefl _), Nat.sub_self]
        calc ((fld v0 (c - k) : ℕ) : ℤ) - (comb Bs Q c + (q : ℤ) * (fld b 0 : ℤ))
            = (((fld v0 (c - k) : ℕ) : ℤ) - comb Bs Q c) - (q : ℤ) * (fld b 0 : ℤ) := by ring
          _ ≡ (x : ℤ) - (q : ℤ) * (fld b 0 : ℤ) [ZMOD m] := h.sub_right _
          _ = ((0 : ℕ) : ℤ) := by
            rw [← hqp]
            push_cast
            ring
      · rw [ite_eq_right (by omega)] at h
        rw [hent, ite_eq_left (by omega)]
        simpa using h

theorem dyStep_zero (m M b : Nat) (K : Nat → Nat → Nat → Nat → Nat) (v out j bad : Nat)
    (h : Nat.beq (Nat.land v (nat_lit 65535)) (nat_lit 0) = true) :
    dyStep m M b K v out j bad = K (Nat.shiftRight v (nat_lit 16)) out (Nat.succ j) bad := by
  unfold dyStep
  simp only
  rw [h]

theorem dyStep_ne (m M b : Nat) (K : Nat → Nat → Nat → Nat → Nat) (v out j bad : Nat)
    (h : Nat.beq (Nat.land v (nat_lit 65535)) (nat_lit 0) = false) :
    dyStep m M b K v out j bad =
      K (Nat.shiftRight (Nat.land (Nat.add v (Nat.mul (Nat.sub m
          (Nat.div (Nat.land v (nat_lit 65535)) (Nat.land b (nat_lit 65535)))) b)) M) (nat_lit 16))
        (Nat.lor out (Nat.shiftLeft (Nat.land
          (Nat.div (Nat.land v (nat_lit 65535)) (Nat.land b (nat_lit 65535))) (nat_lit 1)) j))
        (Nat.succ j)
        (Nat.lor bad (Nat.land (Nat.land v (nat_lit 65535))
          (Nat.sub (Nat.land b (nat_lit 65535)) (nat_lit 1)))) := by
  unfold dyStep
  simp only
  rw [h]

theorem step_claim {e : Nat} (he : e ≤ 8) {k v0 : Nat} {Bs : List (List Nat)} {j : Nat}
    (hkj : k ≤ j) (hj : j < 4371) (hrow : dyRowOK 4371 j (recOf Bs j) = true)
    {K : Nat → Nat → Nat → Nat → Nat} (hK : DyClaim (2 ^ e) k v0 Bs (j + 1) K) :
    DyClaim (2 ^ e) k v0 Bs j (dyStep (2 ^ e) (dyMask (2 ^ e)) (recOf Bs j) K) := by
  intro v out bad hI hne
  have hG : bad = 0 → DyGood (2 ^ e) k v0 Bs j v out := by
    rcases hI with ⟨hjk, -⟩ | ⟨-, -, hG⟩
    · omega
    · exact hG
  cases hx : Nat.beq (Nat.land v (nat_lit 65535)) (nat_lit 0)
  · rw [dyStep_ne _ _ _ _ _ _ _ _ hx] at hne ⊢
    refine hK _ _ _ (Or.inr ⟨by omega, by omega, fun hbad => ?_⟩) hne
    have hbad' := Nat.or_eq_zero_iff.1 hbad
    obtain ⟨⟨e', -, hp⟩, -, -⟩ := dyRowOK_facts (by decide) hrow
    have hdiv : fld v 0 % fld (recOf Bs j) 0 = 0 := by
      have := hbad'.2
      rw [land65535, land65535, hp] at this
      change fld v 0 &&& (2 ^ e' - 1) = 0 at this
      rw [Nat.and_two_pow_sub_one_eq_mod] at this
      rw [hp]
      exact this
    have := good_step1 he hkj hj hrow (hG hbad'.1) hdiv
    rw [land65535, land65535]
    have e1 : ∀ q : Nat, Nat.land q (nat_lit 1) = q % 2 := fun q => by
      change q &&& (2 ^ 1 - 1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod]
    rw [e1]
    exact this
  · rw [dyStep_zero _ _ _ _ _ _ _ _ hx] at hne ⊢
    refine hK _ _ _ (Or.inr ⟨by omega, by omega, fun hbad => ?_⟩) hne
    have hx' : fld v 0 = 0 := by
      rw [← land65535]
      exact Nat.eq_of_beq_eq_true hx
    exact good_step0 hj (hG hbad) hx'

theorem inNo_claim {e : Nat} (he : e ≤ 8) {k v0 : Nat} {Bs : List (List Nat)}
    (hr : ∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) {K : Nat → Nat → Nat → Nat → Nat} :
    ∀ (blk : List Nat) (j : Nat), k ≤ j → j + blk.length ≤ 4371 →
      (∀ idx < blk.length, blk.getD idx 0 = recOf Bs (j + idx)) →
      DyClaim (2 ^ e) k v0 Bs (j + blk.length) K →
      DyClaim (2 ^ e) k v0 Bs j (dyInNo (2 ^ e) (dyMask (2 ^ e)) K blk)
  | [], j, _, _, _, hK => by
    rw [List.length_nil, Nat.add_zero] at hK
    exact hK
  | b :: blk, j, hkj, hlen, hrec, hK => by
    rw [List.length_cons] at hlen hK
    have hb : b = recOf Bs j := by
      have := hrec 0 (by simp)
      rwa [List.getD_cons_zero, Nat.add_zero] at this
    have ih := inNo_claim (k := k) (v0 := v0) (K := K) he hr blk (j + 1) (by omega) (by omega)
      (fun idx h => by
        have := hrec (idx + 1) (by rw [List.length_cons]; omega)
        rw [List.getD_cons_succ] at this
        rw [this]
        congr 1
        omega)
      (by rwa [show j + 1 + blk.length = j + (blk.length + 1) by omega])
    have := step_claim he hkj (by omega) (hr j (by omega)) ih
    rw [← hb] at this
    exact this

theorem inSkip_claim {e : Nat} (he : e ≤ 8) {k v0 : Nat} {Bs : List (List Nat)}
    (hr : ∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) (hk : k ≤ 4371)
    (hv : v0 < 2 ^ (16 * (4371 - k))) (hf : ∀ t, fld v0 t < 2 ^ e)
    {K : Nat → Nat → Nat → Nat → Nat} :
    ∀ (blk : List Nat) (j : Nat), j + blk.length ≤ 4371 →
      (∀ idx < blk.length, blk.getD idx 0 = recOf Bs (j + idx)) →
      DyClaim (2 ^ e) k v0 Bs (j + blk.length) K →
      DyClaim (2 ^ e) k v0 Bs j (dyInSkip (2 ^ e) (dyMask (2 ^ e)) k K blk)
  | [], j, _, _, hK => by
    rw [List.length_nil, Nat.add_zero] at hK
    exact hK
  | b :: blk, j, hlen, hrec, hK => by
    rw [List.length_cons] at hlen hK
    have hb : b = recOf Bs j := by
      have := hrec 0 (by simp)
      rwa [List.getD_cons_zero, Nat.add_zero] at this
    have ih := inSkip_claim (K := K) he hr hk hv hf blk (j + 1) (by omega)
      (fun idx h => by
        have := hrec (idx + 1) (by rw [List.length_cons]; omega)
        rw [List.getD_cons_succ] at this
        rw [this]
        congr 1
        omega)
      (by rwa [show j + 1 + blk.length = j + (blk.length + 1) by omega])
    intro v out bad hI hne
    change Bool.rec (motive := fun _ => Nat)
      (dyInSkip (2 ^ e) (dyMask (2 ^ e)) k K blk v out (Nat.succ j) bad)
      (dyStep (2 ^ e) (dyMask (2 ^ e)) b (dyInSkip (2 ^ e) (dyMask (2 ^ e)) k K blk) v out j bad)
      (Nat.ble k j) ≠ dyFail at hne
    change DyRes (2 ^ e) k v0 Bs (Bool.rec (motive := fun _ => Nat)
      (dyInSkip (2 ^ e) (dyMask (2 ^ e)) k K blk v out (Nat.succ j) bad)
      (dyStep (2 ^ e) (dyMask (2 ^ e)) b (dyInSkip (2 ^ e) (dyMask (2 ^ e)) k K blk) v out j bad)
      (Nat.ble k j))
    cases hkj : Nat.ble k j
    · rw [hkj] at hne
      have hjk : j < k := Nat.lt_of_not_le fun h => by
        rw [Nat.ble_eq_true_of_le h] at hkj
        cases hkj
      refine ih v out bad ?_ hne
      rcases hI with ⟨-, rfl, rfl, rfl⟩ | ⟨h, -⟩
      · by_cases h1 : j + 1 < k
        · exact Or.inl ⟨h1, rfl, rfl, rfl⟩
        · have h2 : j + 1 = k := by omega
          refine Or.inr ⟨by omega, by omega, fun _ => ?_⟩
          rw [h2]
          exact good_init hv hf
      · omega
    · rw [hkj] at hne
      rw [hb] at hne ⊢
      exact step_claim he (Nat.le_of_ble_eq_true hkj) (by omega) (hr j (by omega)) ih v out bad hI hne

theorem fin_claim {e : Nat} {k v0 : Nat} {Bs : List (List Nat)} (hk : k ≤ 4371) :
    DyClaim (2 ^ e) k v0 Bs 4371 dyFin := by
  intro v out bad hI hne
  have hG : bad = 0 → DyGood (2 ^ e) k v0 Bs 4371 v out := by
    rcases hI with ⟨hjk, -⟩ | ⟨-, -, hG⟩
    · omega
    · exact hG
  unfold dyFin at hne ⊢
  cases hv : Nat.beq v (nat_lit 0)
  · rw [hv] at hne
    exact absurd rfl hne
  · cases hb : Nat.beq bad (nat_lit 0)
    · rw [hv, hb] at hne
      exact absurd rfl hne
    · simp only
      obtain ⟨Q, hQs, hQo, -, -, hres⟩ := hG (Nat.eq_of_beq_eq_true hb)
      refine ⟨Q, hQs, hQo, fun c hkc hc => ?_⟩
      have h := hres c hkc hc
      rw [ite_eq_right (by omega), Nat.cast_zero] at h
      simpa only [sub_add_cancel, zero_add] using h.add_right (comb Bs Q c)

theorem outer_claim {e : Nat} (he : e ≤ 8) {k v0 : Nat} {Bs : List (List Nat)}
    (hr : ∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) (hk : k ≤ 4371)
    (hv : v0 < 2 ^ (16 * (4371 - k))) (hf : ∀ t, fld v0 t < 2 ^ e) :
    ∀ (L : List (List Nat)) (j : Nat), j + L.flatten.length = 4371 →
      (∀ idx < L.flatten.length, L.flatten.getD idx 0 = recOf Bs (j + idx)) →
      DyClaim (2 ^ e) k v0 Bs j (dyOuter (2 ^ e) (dyMask (2 ^ e)) k L)
  | [], j, hlen, _ => by
    rw [List.flatten_nil, List.length_nil, Nat.add_zero] at hlen
    subst hlen
    exact fin_claim hk
  | blk :: L, j, hlen, hrec => by
    rw [List.flatten_cons, List.length_append] at hlen
    rw [List.flatten_cons, List.length_append] at hrec
    have ih := outer_claim he hr hk hv hf L (j + blk.length) (by omega)
      (fun idx h => by
        have := hrec (blk.length + idx) (by omega)
        rwa [getD_app_right _ _ (by omega), Nat.add_sub_cancel_left, ← Nat.add_assoc] at this)
    have hrb : ∀ idx < blk.length, blk.getD idx 0 = recOf Bs (j + idx) := fun idx h => by
      have := hrec idx (by omega)
      rwa [getD_app_left _ _ h] at this
    intro v out bad hI hne
    change Bool.rec (motive := fun _ => Nat)
      (dyInSkip (2 ^ e) (dyMask (2 ^ e)) k (dyOuter (2 ^ e) (dyMask (2 ^ e)) k L) blk v out j bad)
      (dyInNo (2 ^ e) (dyMask (2 ^ e)) (dyOuter (2 ^ e) (dyMask (2 ^ e)) k L) blk v out j bad)
      (Nat.ble k j) ≠ dyFail at hne
    change DyRes (2 ^ e) k v0 Bs (Bool.rec (motive := fun _ => Nat)
      (dyInSkip (2 ^ e) (dyMask (2 ^ e)) k (dyOuter (2 ^ e) (dyMask (2 ^ e)) k L) blk v out j bad)
      (dyInNo (2 ^ e) (dyMask (2 ^ e)) (dyOuter (2 ^ e) (dyMask (2 ^ e)) k L) blk v out j bad)
      (Nat.ble k j))
    cases hkj : Nat.ble k j
    · rw [hkj] at hne
      exact inSkip_claim he hr hk hv hf blk j (by omega) hrb ih v out bad hI hne
    · rw [hkj] at hne
      exact inNo_claim he hr blk j (Nat.le_of_ble_eq_true hkj) (by omega) hrb ih v out bad hI hne

theorem dyElim_sound {e : Nat} (he : e ≤ 8) {Bs : List (List Nat)} (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) {k v0 : Nat} (hk : k ≤ 4371)
    (hv : v0 < 2 ^ (16 * (4371 - k))) (hf : ∀ t, fld v0 t < 2 ^ e)
    (h : dyElim (2 ^ e) Bs k v0 ≠ dyFail) : DyRes (2 ^ e) k v0 Bs (dyElim (2 ^ e) Bs k v0) := by
  obtain ⟨hlen, hrec⟩ := blocks_flatten hB
  have hc := outer_claim he hr hk hv hf Bs 0 (by omega)
    (fun idx h => by rw [getD_lt _ _ h, hrec, Nat.zero_add])
  rw [dyElim_eq] at h ⊢
  refine hc v0 0 0 ?_ h
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Or.inr ⟨le_rfl, by omega, fun _ => good_init hv hf⟩
  · exact Or.inl ⟨hk0, rfl, rfl, rfl⟩

@[expose] noncomputable def basisIn (n : Nat) (K : Nat → Nat → Nat) (blk : List Nat) :
    Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun j ok => K j ok)
    (fun b _ ih2 j ok => forceB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) ok (dyRowOK n j b))
      (fun ok' => ih2 (Nat.succ j) ok')) blk

@[expose] noncomputable def basisOut (n : Nat) (Bs : List (List Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ ok => ok)
    (fun blk _ ih j ok => basisIn n ih blk j ok) Bs

theorem forceB_apply (v : Nat) (k : Nat → Nat) : forceB v k = k v := by
  unfold forceB
  cases Nat.beq v 0 <;> rfl

theorem basisIn_eq (n : Nat) (K : Nat → Nat → Nat) : ∀ (blk : List Nat) (j ok : Nat),
    basisIn n K blk j ok = K (j + blk.length)
      (if ∀ idx < blk.length, dyRowOK n (j + idx) (blk.getD idx 0) = true then ok else 0)
  | [], j, ok => by
    change K j ok = _
    rw [List.length_nil, Nat.add_zero, ite_eq_left (fun idx h => absurd h (Nat.not_lt_zero _))]
  | b :: blk, j, ok => by
    change forceB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) ok (dyRowOK n j b))
      (fun ok' => basisIn n K blk (Nat.succ j) ok') = _
    rw [forceB_apply, basisIn_eq n K blk, List.length_cons,
      show Nat.succ j + blk.length = j + (blk.length + 1) by omega]
    congr 1
    have hiff : (∀ idx < blk.length + 1, dyRowOK n (j + idx) ((b :: blk).getD idx 0) = true) ↔
        dyRowOK n j b = true ∧
          ∀ idx < blk.length, dyRowOK n (Nat.succ j + idx) (blk.getD idx 0) = true := by
      constructor
      · intro h
        refine ⟨by simpa using h 0 (by omega), fun idx hidx => ?_⟩
        have := h (idx + 1) (by omega)
        rwa [List.getD_cons_succ, show j + (idx + 1) = Nat.succ j + idx by omega] at this
      · intro ⟨h0, h⟩ idx hidx
        rcases idx with _ | idx
        · simpa using h0
        · rw [List.getD_cons_succ, show j + (idx + 1) = Nat.succ j + idx by omega]
          exact h idx (by omega)
    by_cases h1 : ∀ idx < blk.length, dyRowOK n (Nat.succ j + idx) (blk.getD idx 0) = true
    · rw [ite_eq_left h1]
      cases hb : dyRowOK n j b
      · rw [ite_eq_right (fun h => by have := (hiff.1 h).1; rw [hb] at this; cases this)]
      · rw [ite_eq_left (hiff.2 ⟨hb, h1⟩)]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (hiff.1 h).2)]

theorem basisOut_eq (n : Nat) : ∀ (L : List (List Nat)) (j ok : Nat),
    basisOut n L j ok =
      if ∀ idx < L.flatten.length, dyRowOK n (j + idx) (L.flatten.getD idx 0) = true then ok else 0
  | [], j, ok => by
    change ok = _
    rw [ite_eq_left (fun idx h => absurd h (by simp))]
  | blk :: L, j, ok => by
    change basisIn n (basisOut n L) blk j ok = _
    rw [basisIn_eq, basisOut_eq n L, List.flatten_cons, List.length_append]
    have hiff : (∀ idx < blk.length + L.flatten.length,
        dyRowOK n (j + idx) ((blk ++ L.flatten).getD idx 0) = true) ↔
        (∀ idx < blk.length, dyRowOK n (j + idx) (blk.getD idx 0) = true) ∧
          ∀ idx < L.flatten.length,
            dyRowOK n (j + blk.length + idx) (L.flatten.getD idx 0) = true := by
      constructor
      · intro h
        refine ⟨fun idx hidx => ?_, fun idx hidx => ?_⟩
        · have := h idx (by omega)
          rwa [getD_app_left _ _ hidx] at this
        · have := h (blk.length + idx) (by omega)
          rwa [getD_app_right _ _ (by omega), Nat.add_sub_cancel_left, ← Nat.add_assoc] at this
      · intro ⟨h1, h2⟩ idx hidx
        by_cases hi : idx < blk.length
        · rw [getD_app_left _ _ hi]
          exact h1 idx hi
        · rw [getD_app_right _ _ (by omega)]
          have := h2 (idx - blk.length) (by omega)
          rwa [Nat.add_assoc, Nat.add_sub_cancel' (by omega)] at this
    by_cases h1 : ∀ idx < blk.length, dyRowOK n (j + idx) (blk.getD idx 0) = true
    · rw [ite_eq_left h1]
      by_cases h2 : ∀ idx < L.flatten.length,
          dyRowOK n (j + blk.length + idx) (L.flatten.getD idx 0) = true
      · rw [ite_eq_left h2, ite_eq_left (hiff.2 ⟨h1, h2⟩)]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 (hiff.1 h).2)]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (hiff.1 h).1)]
      split <;> rfl

theorem dyBasisOK_sound {Bs : List (List Nat)} (hB : blocksOK Bs = true)
    (h : dyBasisOK (nat_lit 4371) Bs (nat_lit 0) = true) :
    ∀ j < 4371, dyRowOK (nat_lit 4371) j (recOf Bs j) = true := by
  obtain ⟨hlen, hrec⟩ := blocks_flatten hB
  have e : dyBasisOK 4371 Bs 0 = Nat.blt 0 (basisOut 4371 Bs 0 1) := rfl
  rw [e, basisOut_eq] at h
  intro j hj
  split at h
  · rename_i hall
    have := hall j (by omega)
    rwa [Nat.zero_add, getD_lt _ _ (by omega), hrec] at this
  · exact absurd h Bool.false_ne_true

theorem contOK_sound {Bs : List (List Nat)} (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK (nat_lit 4371) j (recOf Bs j) = true) {i : Nat} (hi : i < 4371)
    (h : contOK Bs i = true) :
    ∃ q : ℕ → ℤ, ∀ c < 4371, i < c →
      ((128 / fld (recOf Bs i) 0 * ent Bs i c : ℕ) : ℤ) ≡
        ∑ j ∈ Finset.Ico (i + 1) 4371, q j * (ent Bs j c : ℤ) [ZMOD 128] := by
  obtain ⟨⟨e', he', hp⟩, hb, hbf⟩ := dyRowOK_facts (by decide) (hr i hi)
  have hb : recOf Bs i < 2 ^ (16 * (4371 - i)) := hb
  set b := recOf Bs i
  set d := 128 / fld b 0
  have hd : d ≤ 128 := Nat.div_le_self _ _
  have hb128 : ∀ t, fld b t ≤ 128 := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [hp]
      exact Nat.pow_le_pow_right (by decide) he'
    · exact (hbf t ht).le
  have hmul : ∀ t, d * fld b t < 65536 := fun t =>
    lt_of_le_of_lt (Nat.mul_le_mul hd (hb128 t)) (by decide)
  have hv0 : contV Bs i = ((d * b) &&& dyMask (2 ^ 7)) >>> 16 := by
    unfold contV
    rw [land65535]
    rfl
  have hfv : ∀ t, fld (contV Bs i) t = if t + 1 < 4371 then d * fld b (t + 1) % 128 else 0 := by
    intro t
    rw [hv0, fld_shr16, fld_land_dyMask (by decide), fld_mul _ hmul]
    rfl
  have hlt : contV Bs i < 2 ^ (16 * (4371 - (i + 1))) := by
    apply lt_of_fld
    intro t ht
    rw [hfv]
    split
    · rw [fld_of_lt (t := t + 1) hb (by omega), Nat.mul_zero]
    · rfl
  have hf : ∀ t, fld (contV Bs i) t < 2 ^ 7 := by
    intro t
    rw [hfv]
    split
    · exact Nat.mod_lt _ (by decide)
    · decide
  have hne : dyElim (2 ^ 7) Bs (i + 1) (contV Bs i) ≠ dyFail := by
    intro e
    have h' : Nat.blt (dyElim 128 Bs (Nat.succ i) (contV Bs i)) dyFail = true := h
    rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.succ_eq_add_one, e] at h'
    exact absurd (Nat.le_of_ble_eq_true h') (Nat.not_succ_le_self _)
  obtain ⟨Q, hQs, -, hres⟩ := dyElim_sound (by decide) hB hr (by omega) hlt hf hne
  refine ⟨fun j => (Q j : ℤ), fun c hc hic => ?_⟩
  have h1 := hres c (by omega) hc
  rw [hfv, ite_eq_left (by omega), show c - (i + 1) + 1 = c - i by omega, comb_eq] at h1
  have hent : ent Bs i c = fld b (c - i) := by
    rw [ent, ite_eq_right (by omega)]
  have hsum : ∑ j' ∈ Finset.range 4371, (Q j' : ℤ) * (ent Bs j' c : ℤ) =
      ∑ j ∈ Finset.Ico (i + 1) 4371, (Q j : ℤ) * (ent Bs j c : ℤ) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_Ico] at hj
      exact Finset.mem_range.2 hj.2
    · intro j _ hj
      rw [Finset.mem_Ico] at hj
      have : Q j = 0 := by
        by_contra hQ
        have := hQs j hQ
        omega
      rw [this]
      simp
  rw [← hsum, hent]
  refine Int.ModEq.trans ?_ h1
  rw [Int.natCast_emod]
  exact (Int.mod_modEq _ _).symm

end CFSG.KC.BM.Dy

end
