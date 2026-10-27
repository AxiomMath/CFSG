module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K

@[expose] def dg (p i : ℕ) : ℕ := (p / 64 ^ i) % 64

@[expose] def compAux (t u : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => compAux t u n + dg t (dg u n) * 64 ^ n

@[expose] def compP (t u : ℕ) : ℕ := compAux t u 36

@[expose] def oneAux : ℕ → ℕ
  | 0 => 0
  | n + 1 => oneAux n + n * 64 ^ n

@[expose] def oneP : ℕ := oneAux 36

theorem dg_lt (p i : ℕ) : dg p i < 64 := Nat.mod_lt _ (by norm_num)

theorem compAux_lt (t u : ℕ) : ∀ n, compAux t u n < 64 ^ n
  | 0 => by simp [compAux]
  | n + 1 => by
    have h1 := compAux_lt t u n
    have h2 := dg_lt t (dg u n)
    have h3 : dg t (dg u n) * 64 ^ n ≤ 63 * 64 ^ n :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [compAux, pow_succ]
    omega

theorem dg_add_mul {A d n i : ℕ} (hA : A < 64 ^ n) (hd : d < 64) (hi : i < n) :
    dg (A + d * 64 ^ n) i = dg A i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = i + 1 + k := ⟨n - i - 1, by omega⟩
  unfold dg
  have e : 64 ^ (i + 1 + k) = 64 ^ i * (64 * 64 ^ k) := by
    rw [pow_add, pow_add, pow_one]; ring
  have h64 : d * (64 * 64 ^ k) % 64 = 0 := by
    rw [show d * (64 * 64 ^ k) = 64 * (d * 64 ^ k) by ring]
    exact Nat.mul_mod_right _ _
  rw [e, show A + d * (64 ^ i * (64 * 64 ^ k)) = A + 64 ^ i * (d * (64 * 64 ^ k)) by ring,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mod, h64, add_zero, Nat.mod_mod]

theorem dg_add_mul_self {A d n : ℕ} (hA : A < 64 ^ n) (hd : d < 64) :
    dg (A + d * 64 ^ n) n = d := by
  unfold dg
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add]
  exact Nat.mod_eq_of_lt hd

theorem dg_compAux (t u : ℕ) : ∀ n i, i < n → dg (compAux t u n) i = dg t (dg u i)
  | 0, i, hi => absurd hi (by omega)
  | n + 1, i, hi => by
    simp only [compAux]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [dg_add_mul (compAux_lt t u n) (dg_lt t _) h]
      exact dg_compAux t u n i h
    · rw [h]
      exact dg_add_mul_self (compAux_lt t u n) (dg_lt t _)

theorem oneAux_lt : ∀ n, n ≤ 64 → oneAux n < 64 ^ n
  | 0, _ => by simp [oneAux]
  | n + 1, h => by
    have h1 := oneAux_lt n (by omega)
    have h3 : n * 64 ^ n ≤ 63 * 64 ^ n := Nat.mul_le_mul_right _ (by omega)
    simp only [oneAux, pow_succ]
    omega

theorem dg_oneAux : ∀ n i, n ≤ 64 → i < n → dg (oneAux n) i = i
  | 0, i, _, hi => absurd hi (by omega)
  | n + 1, i, hn, hi => by
    simp only [oneAux]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [dg_add_mul (oneAux_lt n (by omega)) (by omega) h]
      exact dg_oneAux n i (by omega) h
    · rw [h]
      exact dg_add_mul_self (oneAux_lt n (by omega)) (by omega)

@[expose] def PRep (p : ℕ) (g : Equiv.Perm (Fin 36)) : Prop :=
  p < 64 ^ 36 ∧ ∀ i : Fin 36, dg p i = (g i : ℕ)

theorem pack_inj {n : ℕ} : ∀ {x y : ℕ}, x < 64 ^ n → y < 64 ^ n → (∀ i < n, dg x i = dg y i) → x = y := by
  induction n with
  | zero => intro x y hx hy _; simp at hx hy; omega
  | succ n ih =>
    intro x y hx hy h
    have hx' : x / 64 < 64 ^ n := by
      rw [pow_succ] at hx
      exact Nat.div_lt_of_lt_mul (by linarith)
    have hy' : y / 64 < 64 ^ n := by
      rw [pow_succ] at hy
      exact Nat.div_lt_of_lt_mul (by linarith)
    have h0 : x % 64 = y % 64 := by simpa [dg] using h 0 (by omega)
    have h1 : x / 64 = y / 64 := by
      apply ih hx' hy'
      intro i hi
      have := h (i + 1) (by omega)
      simpa [dg, pow_succ, Nat.div_div_eq_div_mul, mul_comm] using this
    omega

theorem PRep.unique {p : ℕ} {g h : Equiv.Perm (Fin 36)} (hg : PRep p g) (hh : PRep p h) : g = h :=
  Equiv.ext fun i => Fin.ext ((hg.2 i).symm.trans (hh.2 i))

theorem PRep.inj {p q : ℕ} {g : Equiv.Perm (Fin 36)} (hp : PRep p g) (hq : PRep q g) : p = q :=
  pack_inj hp.1 hq.1 fun i hi => by
    rw [hp.2 ⟨i, hi⟩, hq.2 ⟨i, hi⟩]

theorem PRep.comp {t u : ℕ} {g h : Equiv.Perm (Fin 36)} (ht : PRep t g) (hu : PRep u h) :
    PRep (compP t u) (g * h) := by
  refine ⟨compAux_lt t u 36, fun i => ?_⟩
  rw [compP, dg_compAux t u 36 i i.2, hu.2 i]
  exact ht.2 (h i)

theorem PRep.one : PRep oneP 1 := by
  refine ⟨oneAux_lt 36 (by norm_num), fun i => ?_⟩
  rw [oneP, dg_oneAux 36 i (by norm_num) i.2]
  rfl

@[expose] def evalW (gl : List ℕ) : List ℕ → ℕ
  | [] => oneP
  | l :: w => compP (gl.getD l oneP) (evalW gl w)

theorem evalW_rep (gl : List ℕ) (G : ℕ → Equiv.Perm (Fin 36))
    (hG : ∀ l, PRep (gl.getD l oneP) (G l)) :
    ∀ w : List ℕ, PRep (evalW gl w) (w.map G).prod
  | [] => by simpa [evalW] using PRep.one
  | l :: w => by
    have := (hG l).comp (evalW_rep gl G hG w)
    simpa [evalW] using this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K
