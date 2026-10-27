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

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.PkG

@[expose] def dg (b p i : ℕ) : ℕ := (p / b ^ i) % b

@[expose] def compAux (b t u : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => compAux b t u n + dg b t (dg b u n) * b ^ n

@[expose] def comp (b n t u : ℕ) : ℕ := compAux b t u n

@[expose] def oneAux (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => oneAux b n + n * b ^ n

@[expose] def one (b n : ℕ) : ℕ := oneAux b n

theorem dg_lt {b : ℕ} (hb : 0 < b) (p i : ℕ) : dg b p i < b := Nat.mod_lt _ hb

theorem compAux_lt {b : ℕ} (hb : 0 < b) (t u : ℕ) : ∀ n, compAux b t u n < b ^ n
  | 0 => by simp [compAux]
  | n + 1 => by
    have h1 := compAux_lt hb t u n
    have h2 := dg_lt hb t (dg b u n)
    have h3 : dg b t (dg b u n) * b ^ n ≤ (b - 1) * b ^ n :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (b - 1) * b ^ n + b ^ n = b ^ (n + 1) := by
      rw [pow_succ]
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    simp only [compAux]
    omega

theorem dg_add_mul {b A d n i : ℕ} (hb : 0 < b) (hA : A < b ^ n) (hd : d < b) (hi : i < n) :
    dg b (A + d * b ^ n) i = dg b A i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = i + 1 + k := ⟨n - i - 1, by omega⟩
  unfold dg
  have e : b ^ (i + 1 + k) = b ^ i * (b * b ^ k) := by
    rw [pow_add, pow_add, pow_one]; ring
  have hb0 : d * (b * b ^ k) % b = 0 := by
    rw [show d * (b * b ^ k) = b * (d * b ^ k) by ring]
    exact Nat.mul_mod_right _ _
  have hpos : 0 < b ^ i := pow_pos hb i
  rw [e, show A + d * (b ^ i * (b * b ^ k)) = A + b ^ i * (d * (b * b ^ k)) by ring,
    Nat.add_mul_div_left _ _ hpos, Nat.add_mod, hb0, add_zero, Nat.mod_mod]

theorem dg_add_mul_self {b A d n : ℕ} (hb : 0 < b) (hA : A < b ^ n) (hd : d < b) :
    dg b (A + d * b ^ n) n = d := by
  unfold dg
  rw [Nat.add_mul_div_right _ _ (pow_pos hb n), Nat.div_eq_of_lt hA, zero_add]
  exact Nat.mod_eq_of_lt hd

theorem dg_compAux {b : ℕ} (hb : 0 < b) (t u : ℕ) :
    ∀ n i, i < n → dg b (compAux b t u n) i = dg b t (dg b u i)
  | 0, i, hi => absurd hi (by omega)
  | n + 1, i, hi => by
    simp only [compAux]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [dg_add_mul hb (compAux_lt hb t u n) (dg_lt hb t _) h]
      exact dg_compAux hb t u n i h
    · rw [h]
      exact dg_add_mul_self hb (compAux_lt hb t u n) (dg_lt hb t _)

theorem oneAux_lt {b : ℕ} (hb : 0 < b) : ∀ n, n ≤ b → oneAux b n < b ^ n
  | 0, _ => by simp [oneAux]
  | n + 1, h => by
    have h1 := oneAux_lt hb n (by omega)
    have h3 : n * b ^ n ≤ (b - 1) * b ^ n := Nat.mul_le_mul_right _ (by omega)
    have h4 : (b - 1) * b ^ n + b ^ n = b ^ (n + 1) := by
      rw [pow_succ]
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    simp only [oneAux]
    omega

theorem dg_oneAux {b : ℕ} (hb : 0 < b) : ∀ n i, n ≤ b → i < n → dg b (oneAux b n) i = i
  | 0, i, _, hi => absurd hi (by omega)
  | n + 1, i, hn, hi => by
    simp only [oneAux]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [dg_add_mul hb (oneAux_lt hb n (by omega)) (by omega) h]
      exact dg_oneAux hb n i (by omega) h
    · rw [h]
      exact dg_add_mul_self hb (oneAux_lt hb n (by omega)) (by omega)

@[expose] def Rep (b n p : ℕ) (g : Equiv.Perm (Fin n)) : Prop :=
  p < b ^ n ∧ ∀ i : Fin n, dg b p i = (g i : ℕ)

theorem pack_inj {b : ℕ} (hb : 0 < b) {n : ℕ} :
    ∀ {x y : ℕ}, x < b ^ n → y < b ^ n → (∀ i < n, dg b x i = dg b y i) → x = y := by
  induction n with
  | zero => intro x y hx hy _; simp at hx hy; omega
  | succ n ih =>
    intro x y hx hy h
    have hx' : x / b < b ^ n := by
      rw [pow_succ] at hx
      exact Nat.div_lt_of_lt_mul (by linarith)
    have hy' : y / b < b ^ n := by
      rw [pow_succ] at hy
      exact Nat.div_lt_of_lt_mul (by linarith)
    have h0 : x % b = y % b := by simpa [dg] using h 0 (by omega)
    have h1 : x / b = y / b := by
      apply ih hx' hy'
      intro i hi
      have := h (i + 1) (by omega)
      simpa [dg, pow_succ, Nat.div_div_eq_div_mul, mul_comm] using this
    have e1 := Nat.mod_add_div x b
    have e2 := Nat.mod_add_div y b
    rw [h0, h1] at e1
    omega

variable {b n : ℕ}

theorem Rep.unique {p : ℕ} {g h : Equiv.Perm (Fin n)} (hg : Rep b n p g) (hh : Rep b n p h) :
    g = h :=
  Equiv.ext fun i => Fin.ext ((hg.2 i).symm.trans (hh.2 i))

theorem Rep.inj (hb : 0 < b) {p q : ℕ} {g : Equiv.Perm (Fin n)} (hp : Rep b n p g)
    (hq : Rep b n q g) : p = q :=
  pack_inj hb hp.1 hq.1 fun i hi => by
    rw [hp.2 ⟨i, hi⟩, hq.2 ⟨i, hi⟩]

theorem Rep.comp (hb : 0 < b) {t u : ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep b n t g)
    (hu : Rep b n u h) : Rep b n (comp b n t u) (g * h) := by
  refine ⟨compAux_lt hb t u n, fun i => ?_⟩
  rw [PkG.comp, dg_compAux hb t u n i i.2, hu.2 i]
  exact ht.2 (h i)

theorem Rep.one (hb : 0 < b) (hn : n ≤ b) : Rep b n (one b n) 1 := by
  refine ⟨oneAux_lt hb n hn, fun i => ?_⟩
  rw [PkG.one, dg_oneAux hb n i hn i.2]
  rfl

theorem Rep.inv_of_lit {p q : ℕ} {g : Equiv.Perm (Fin n)} (hq : q < b ^ n) (hp : Rep b n p g)
    (h1 : ∀ i < n, dg b q i < n) (h2 : ∀ i < n, dg b p (dg b q i) = i) : Rep b n q g⁻¹ := by
  refine ⟨hq, fun i => ?_⟩
  have hj : dg b q i < n := h1 i i.2
  have h3 : g ⟨dg b q i, hj⟩ = i := by
    apply Fin.ext
    rw [← hp.2 ⟨dg b q i, hj⟩]
    exact h2 i i.2
  have : g⁻¹ i = ⟨dg b q i, hj⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq, h3]
  rw [this]

@[expose] def evalW (b n : ℕ) (gl : List ℕ) : List ℕ → ℕ
  | [] => one b n
  | l :: w => comp b n (gl.getD l (one b n)) (evalW b n gl w)

theorem evalW_rep (hb : 0 < b) (hn : n ≤ b) (gl : List ℕ) (G : ℕ → Equiv.Perm (Fin n))
    (hG : ∀ l, Rep b n (gl.getD l (one b n)) (G l)) :
    ∀ w : List ℕ, Rep b n (evalW b n gl w) (w.map G).prod
  | [] => by simpa [evalW] using Rep.one hb hn
  | l :: w => by
    have := (hG l).comp hb (evalW_rep hb hn gl G hG w)
    simpa [evalW] using this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.PkG
