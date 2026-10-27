module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.ClassTwo

@[expose] def corr (D : ℕ → ℕ → ℕ) (i : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | k, e :: a => e * D i k + corr D i (k + 1) a

@[expose] def bump (D : ℕ → ℕ → ℕ) (i : ℕ) : ℕ → List ℕ → List ℕ × ℕ
  | _, [] => ([], 0)
  | k, e :: a => if k = i then ((e + 1) :: a, corr D i (k + 1) a)
    else ((e :: (bump D i (k + 1) a).1), (bump D i (k + 1) a).2)

@[expose] def step (m p : ℕ) (D : ℕ → ℕ → ℕ) (s : List ℕ × ℕ) (l : ℕ) : List ℕ × ℕ :=
  if l < m then ((bump D l 0 s.1).1, s.2 + (p - 1) * (bump D l 0 s.1).2) else (s.1, s.2 + 1)

@[expose] def nf (m p : ℕ) (D : ℕ → ℕ → ℕ) (w : List ℕ) : List ℕ × ℕ :=
  ((w.foldl (step m p D) (List.replicate m 0, 0)).1.map (· % p),
    (w.foldl (step m p D) (List.replicate m 0, 0)).2 % p)

@[expose] def nfEq (m p : ℕ) (D : ℕ → ℕ → ℕ) (u v : List ℕ) : Bool :=
  u.all (· ≤ m) && v.all (· ≤ m) && decide (nf m p D u = nf m p D v)

theorem length_bump (D : ℕ → ℕ → ℕ) (i : ℕ) :
    ∀ (k : ℕ) (a : List ℕ), (bump D i k a).1.length = a.length
  | _, [] => rfl
  | k, e :: a => by
    unfold bump
    split
    · rfl
    · simp [length_bump D i (k + 1) a]

theorem length_step (m p : ℕ) (D : ℕ → ℕ → ℕ) (s : List ℕ × ℕ) (l : ℕ) :
    (step m p D s l).1.length = s.1.length := by
  unfold step
  split
  · exact length_bump _ _ _ _
  · rfl

theorem length_fold (m p : ℕ) (D : ℕ → ℕ → ℕ) :
    ∀ (w : List ℕ) (s : List ℕ × ℕ), (w.foldl (step m p D) s).1.length = s.1.length
  | [], _ => rfl
  | l :: w, s => by rw [List.foldl_cons, length_fold m p D w, length_step]

variable {G : Type*} [Monoid G]

@[expose] def ev (q : ℕ → G) : List ℕ → G
  | [] => 1
  | l :: w => q l * ev q w

@[expose] def pr (q : ℕ → G) : ℕ → List ℕ → G
  | _, [] => 1
  | k, e :: a => q k ^ e * pr q (k + 1) a

structure Cfg (m p : ℕ) (D : ℕ → ℕ → ℕ) (q : ℕ → G) : Prop where
  p_pos : 0 < p
  pow : ∀ i ≤ m, q i ^ p = 1
  cen : ∀ i < m, q i * q m = q m * q i
  rel : ∀ i j, i < j → j < m → q i * q j = q j * q i * q m ^ D i j

theorem ev_append (q : ℕ → G) (u v : List ℕ) : ev q (u ++ v) = ev q u * ev q v := by
  induction u with
  | nil => simp [ev]
  | cons l u ih => simp [ev, ih, mul_assoc]

theorem ev_flatten_replicate (q : ℕ → G) (u : List ℕ) (k : ℕ) :
    ev q (List.replicate k u).flatten = ev q u ^ k := by
  induction k with
  | zero => simp [ev]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ev_append, ih, pow_succ']

theorem map_ev {H : Type*} [Monoid H] (f : G →* H) (q : ℕ → G) (w : List ℕ) :
    f (ev q w) = ev (fun i => f (q i)) w := by
  induction w with
  | nil => simp [ev]
  | cons l w ih => simp [ev, ih]

@[expose] def subst (T : ℕ → List ℕ) (w : List ℕ) : List ℕ := w.flatMap T

theorem ev_subst (q : ℕ → G) (T : ℕ → List ℕ) (w : List ℕ) :
    ev q (subst T w) = ev (fun l => ev q (T l)) w := by
  induction w with
  | nil => simp [subst, ev]
  | cons l w ih =>
    simp only [subst, List.flatMap_cons] at ih ⊢
    rw [ev_append, ih]
    rfl

theorem conj_ev {G : Type*} [Group G] (g : G) (q : ℕ → G) (w : List ℕ) :
    g⁻¹ * ev q w * g = ev (fun l => g⁻¹ * q l * g) w := by
  induction w with
  | nil => simp [ev]
  | cons l w ih =>
    simp only [ev]
    rw [← ih]
    simp only [mul_assoc, mul_inv_cancel_left]

namespace Cfg

variable {m p : ℕ} {D : ℕ → ℕ → ℕ} {q : ℕ → G} (h : Cfg m p D q)
include h

theorem cenC {i : ℕ} (hi : i < m) : Commute (q m) (q i) := (h.cen i hi).symm

theorem cen_pr : ∀ (k : ℕ) (a : List ℕ), k + a.length ≤ m → Commute (q m) (pr q k a)
  | _, [], _ => Commute.one_right _
  | k, e :: a, hk => by
    simp only [List.length_cons] at hk
    exact ((h.cenC (by omega)).pow_right e).mul_right (cen_pr (k + 1) a (by omega))

theorem swap {i j : ℕ} (hij : i < j) (hj : j < m) :
    q j * q i = q i * q j * q m ^ ((p - 1) * D i j) := by
  have he : D i j + (p - 1) * D i j = p * D i j := by
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by have := h.p_pos; omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hz : q m ^ D i j * q m ^ ((p - 1) * D i j) = 1 := by
    rw [← pow_add, he, pow_mul, h.pow m le_rfl, one_pow]
  calc q j * q i = q j * q i * (q m ^ D i j * q m ^ ((p - 1) * D i j)) := by rw [hz, mul_one]
    _ = (q j * q i * q m ^ D i j) * q m ^ ((p - 1) * D i j) := by simp only [mul_assoc]
    _ = q i * q j * q m ^ ((p - 1) * D i j) := by rw [← h.rel i j hij hj]

theorem swap_pow {i j : ℕ} (hij : i < j) (hj : j < m) (e : ℕ) :
    q j ^ e * q i = q i * q j ^ e * q m ^ (e * ((p - 1) * D i j)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hc : Commute (q m ^ (e * ((p - 1) * D i j))) (q j) := ((h.cenC hj).pow_left _)
    calc q j ^ (e + 1) * q i = q j ^ e * (q j * q i) := by rw [pow_succ, mul_assoc]
      _ = q j ^ e * q i * q j * q m ^ ((p - 1) * D i j) := by rw [h.swap hij hj]; simp only [mul_assoc]
      _ = q i * q j ^ e * (q m ^ (e * ((p - 1) * D i j)) * q j) * q m ^ ((p - 1) * D i j) := by
          rw [ih]; simp only [mul_assoc]
      _ = q i * q j ^ e * q j * (q m ^ (e * ((p - 1) * D i j)) * q m ^ ((p - 1) * D i j)) := by
          rw [hc.eq]; simp only [mul_assoc]
      _ = q i * q j ^ (e + 1) * q m ^ ((e + 1) * ((p - 1) * D i j)) := by
          rw [← pow_add, pow_succ, add_mul, one_mul]; simp only [mul_assoc]

theorem move {i : ℕ} : ∀ (k : ℕ) (a : List ℕ), i < k → k + a.length ≤ m →
    pr q k a * q i = q i * pr q k a * q m ^ ((p - 1) * corr D i k a)
  | _, [], _, _ => by simp [pr, corr]
  | k, e :: a, hik, hk => by
    simp only [List.length_cons] at hk
    have ih := move (i := i) (k + 1) a (by omega) (by omega)
    have hc : Commute (q m ^ (e * ((p - 1) * D i k))) (pr q (k + 1) a) :=
      (h.cen_pr (k + 1) a (by omega)).pow_left _
    simp only [pr, corr]
    calc q k ^ e * pr q (k + 1) a * q i = q k ^ e * (pr q (k + 1) a * q i) := by rw [mul_assoc]
      _ = q k ^ e * q i * pr q (k + 1) a * q m ^ ((p - 1) * corr D i (k + 1) a) := by
          rw [ih]; simp only [mul_assoc]
      _ = q i * q k ^ e * (q m ^ (e * ((p - 1) * D i k)) * pr q (k + 1) a) *
            q m ^ ((p - 1) * corr D i (k + 1) a) := by
          rw [h.swap_pow hik (by omega)]; simp only [mul_assoc]
      _ = q i * (q k ^ e * pr q (k + 1) a) *
            (q m ^ (e * ((p - 1) * D i k)) * q m ^ ((p - 1) * corr D i (k + 1) a)) := by
          rw [hc.eq]; simp only [mul_assoc]
      _ = q i * (q k ^ e * pr q (k + 1) a) * q m ^ ((p - 1) * (e * D i k + corr D i (k + 1) a)) := by
          rw [← pow_add]; congr 2; ring

theorem ins {i : ℕ} : ∀ (k : ℕ) (a : List ℕ), k ≤ i → i < k + a.length → k + a.length ≤ m →
    pr q k a * q i = pr q k (bump D i k a).1 * q m ^ ((p - 1) * (bump D i k a).2)
  | _, [], _, hi, _ => by simp at hi; omega
  | k, e :: a, hki, hi, hk => by
    simp only [List.length_cons] at hi hk
    unfold bump
    split
    · next hk' =>
      have hm := h.move (i := i) (k + 1) a (by omega) (by omega)
      subst hk'
      simp only [pr]
      rw [mul_assoc, hm, pow_succ]
      simp only [mul_assoc]
    · next hk' =>
      have ih := ins (i := i) (k + 1) a (by omega) (by omega) (by omega)
      simp only [pr]
      rw [mul_assoc, ih, mul_assoc]

theorem step_eq {s : List ℕ × ℕ} (hs : s.1.length = m) {l : ℕ} (hl : l ≤ m) :
    pr q 0 s.1 * q m ^ s.2 * q l = pr q 0 (step m p D s l).1 * q m ^ (step m p D s l).2 := by
  unfold step
  split
  · next hlm =>
    have hc : Commute (q m ^ s.2) (q l) := (h.cenC hlm).pow_left _
    rw [mul_assoc, hc.eq, ← mul_assoc, h.ins (i := l) 0 s.1 (Nat.zero_le _) (by omega) (by omega),
      mul_assoc, ← pow_add, add_comm]
  · have e : l = m := by omega
    subst e
    rw [mul_assoc, ← pow_succ]

theorem fold_eq : ∀ (w : List ℕ) (s : List ℕ × ℕ), s.1.length = m → (∀ l ∈ w, l ≤ m) →
    pr q 0 s.1 * q m ^ s.2 * ev q w =
      pr q 0 (w.foldl (step m p D) s).1 * q m ^ (w.foldl (step m p D) s).2
  | [], s, _, _ => by simp [ev]
  | l :: w, s, hs, hw => by
    simp only [ev, List.foldl_cons]
    rw [← mul_assoc, h.step_eq hs (hw l List.mem_cons_self)]
    exact fold_eq w _ (by rw [length_step, hs]) fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')

theorem pr_zero : ∀ (k n : ℕ), pr q k (List.replicate n 0) = 1
  | _, 0 => rfl
  | k, n + 1 => by simp [List.replicate_succ, pr, pr_zero (k + 1) n]

theorem pr_mod : ∀ (k : ℕ) (a : List ℕ), k + a.length ≤ m + 1 →
    pr q k (a.map (· % p)) = pr q k a
  | _, [], _ => rfl
  | k, e :: a, hk => by
    simp only [List.length_cons] at hk
    simp only [List.map_cons, pr]
    rw [pr_mod (k + 1) a (by omega), ← pow_eq_pow_mod e (h.pow k (by omega))]

theorem ev_eq_nf {w : List ℕ} (hw : ∀ l ∈ w, l ≤ m) :
    ev q w = pr q 0 (nf m p D w).1 * q m ^ (nf m p D w).2 := by
  have := h.fold_eq w (List.replicate m 0, 0) (by simp) hw
  rw [h.pr_zero, pow_zero, one_mul, one_mul] at this
  rw [this, nf]
  simp only
  rw [h.pr_mod 0 _ (by rw [length_fold]; simp), ← pow_eq_pow_mod _ (h.pow m le_rfl)]

theorem ev_eq_of_nfEq {u v : List ℕ} (e : nfEq m p D u v = true) : ev q u = ev q v := by
  simp only [nfEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at e
  rw [h.ev_eq_nf e.1.1, h.ev_eq_nf e.1.2, e.2]

end Cfg

theorem test_pos : nfEq 2 3 (fun _ _ => 1) [0, 1] [1, 0, 2] = true := by decide

theorem test_neg : nfEq 2 3 (fun _ _ => 1) [0, 1] [1, 0] = false := by decide

end CFSG.KC.ClassTwo

end
