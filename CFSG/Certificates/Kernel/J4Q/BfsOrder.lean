module

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.J4Q.BfsOrder

variable {n s L : Nat} {PAR LAB : Nat → Nat} {TT : Nat → Nat → Nat}

@[expose] def StepOK {β : Type} (I Q : β → Prop) : ForInStep β → Prop
  | .yield b => I b
  | .done b => Q b

theorem forIn_range'_inv {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) : ∀ (m s : Nat) (b : β),
    (∀ q b, s ≤ q → q < s + m → I q b → StepOK (I (q + 1)) Q (f q b)) →
    (∀ b, I (s + m) b → Q b) → I s b → Q (forIn (List.range' s m) b f)
  | 0, s, b, _, hend, h0 => hend b (by simpa using h0)
  | m + 1, s, b, hstep, hend, h0 => by
    rw [List.range'_succ, List.forIn_cons]
    have hs := hstep s b (Nat.le_refl _) (by omega) h0
    cases hf : f s b with
    | done b' =>
      rw [hf] at hs
      exact hs
    | yield b' =>
      rw [hf] at hs
      exact forIn_range'_inv I Q f m (s + 1) b'
        (fun q b h1 h2 h3 => hstep q b (by omega) (by omega) h3)
        (fun b hb => hend b (by rwa [show s + (m + 1) = s + 1 + m by omega])) hs

theorem forIn_range_inv {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) (n : Nat) (b : β)
    (hstep : ∀ q b, q < n → I q b → StepOK (I (q + 1)) Q (f q b))
    (hend : ∀ b, I n b → Q b) (h0 : I 0 b) : Q (forIn [:n] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : Std.Legacy.Range.size [:n] = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  exact forIn_range'_inv I Q f n 0 b (fun q b _ h2 h3 => hstep q b (by omega) h3)
    (fun b hb => hend b (by simpa using hb)) h0

theorem forIn_range_bind {β γ : Type} (I : Nat → β → Prop) (P : γ → Prop)
    (f : Nat → β → Id (ForInStep β)) (n : Nat) (b : β) (g : β → Id γ)
    (hstep : ∀ q b, q < n → I q b → StepOK (I (q + 1)) (fun b => P (g b).run) (f q b))
    (hend : ∀ b, I n b → P (g b).run) (h0 : I 0 b) : P (forIn [:n] b f >>= g).run :=
  forIn_range_inv I (fun b => P (g b).run) f n b hstep hend h0

@[expose] def Inv (n s L : Nat) (PAR LAB : Nat → Nat) (i g m : Nat) : Prop :=
  m ≤ n ∧ ∀ k < n, (k < m ↔ (k < s ∨ PAR k * L + LAB k < i * L + g))

structure Tree (n s L : Nat) (PAR LAB : Nat → Nat) (TT : Nat → Nat → Nat) : Prop where
  sn : s ≤ n
  par : ∀ k, s ≤ k → k < n → PAR k < k ∧ LAB k < L
  same : ∀ k, s ≤ k → k < n → TT (PAR k) (LAB k) = k
  clos : ∀ k < n, ∀ g < L, TT k g < n
  ord : ∀ k, s ≤ k → k + 1 < n → PAR k * L + LAB k < PAR (k + 1) * L + LAB (k + 1)
  first : ∀ k < n, ∀ g < L, TT k g < s ∨ PAR (TT k g) * L + LAB (TT k g) ≤ k * L + g

theorem key_mono (T : Tree n s L PAR LAB TT) {a b : Nat} (ha : s ≤ a) (hab : a < b) (hb : b < n) :
    PAR a * L + LAB a < PAR b * L + LAB b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
    · exact Nat.lt_trans (ih h (by omega)) (T.ord b (by omega) hb)
    · exact T.ord a ha hb

theorem key_inj (T : Tree n s L PAR LAB TT) {a b : Nat} (ha : s ≤ a) (hb : s ≤ b) (han : a < n)
    (hbn : b < n) (h : PAR a * L + LAB a = PAR b * L + LAB b) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd h (Nat.ne_of_lt (key_mono T ha hab hbn))
  · exact hab
  · exact absurd h.symm (Nat.ne_of_lt (key_mono T hb hab han))

theorem key_div (T : Tree n s L PAR LAB TT) {k i g : Nat} (hs : s ≤ k) (hk : k < n) (hg : g < L)
    (h : PAR k * L + LAB k = i * L + g) : PAR k = i ∧ LAB k = g := by
  have hl := (T.par k hs hk).2
  have h1 : (PAR k * L + LAB k) / L = PAR k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl, Nat.zero_add]
  have h2 : (i * L + g) / L = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hg, Nat.zero_add]
  have hp : PAR k = i := by rw [← h1, h, h2]
  refine ⟨hp, ?_⟩
  rw [hp] at h
  omega

theorem inv_init (T : Tree n s L PAR LAB TT) : Inv n s L PAR LAB 0 0 s :=
  ⟨T.sn, fun k _ => by simp⟩

theorem inv_old (T : Tree n s L PAR LAB TT) {i g m : Nat} (hI : Inv n s L PAR LAB i g m)
    (hi : i < n) (hg : g < L) (ht : TT i g < m) : Inv n s L PAR LAB i (g + 1) m := by
  refine ⟨hI.1, fun k hk => ?_⟩
  rw [hI.2 k hk]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hs : k < s
      · exact Or.inl hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 (show PAR k * L + LAB k < (i * L + g) + 1 by omega)
        with h' | h'
      · exact Or.inr h'
      · obtain ⟨hp, hl⟩ := key_div T (by omega) hk hg h'
        have e := T.same k (by omega) hk
        rw [hp, hl] at e
        rw [← e]
        exact (hI.2 _ (T.clos i hi g hg)).1 ht

theorem inv_new (T : Tree n s L PAR LAB TT) {i g m : Nat} (hI : Inv n s L PAR LAB i g m)
    (hi : i < n) (hg : g < L) (ht : ¬ TT i g < m) :
    TT i g = m ∧ m < n ∧ s ≤ m ∧ PAR m = i ∧ LAB m = g ∧ Inv n s L PAR LAB i (g + 1) (m + 1) := by
  have htn : TT i g < n := T.clos i hi g hg
  have hfi := T.first i hi g hg
  generalize TT i g = t at ht htn hfi ⊢
  have hnot := (not_congr (hI.2 t htn)).1 ht
  have hts : s ≤ t := by omega
  have hkey : PAR t * L + LAB t = i * L + g := by
    rcases hfi with h | h
    · omega
    · omega
  have hsm : s ≤ m := by
    by_contra hc
    have := (hI.2 m (by omega)).2 (Or.inl (by omega))
    omega
  have htm : t = m := by
    by_contra hne
    have hlt : m < t := by omega
    have := key_mono T hsm hlt htn
    have hm := (hI.2 m (by omega)).2 (Or.inr (by omega))
    omega
  refine ⟨htm, htm ▸ htn, hsm, ?_⟩
  obtain ⟨hp, hl⟩ := key_div T hts htn hg hkey
  rw [htm] at hp hl
  refine ⟨hp, hl, by omega, fun k hk => ?_⟩
  by_cases hkm : k = m
  · subst hkm
    rw [htm] at hkey
    omega
  · rw [show k < m + 1 ↔ k < m by omega, hI.2 k hk]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by omega)
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hs : k < s
        · exact Or.inl hs
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show PAR k * L + LAB k < (i * L + g) + 1 by omega)
          with h' | h'
        · exact Or.inr h'
        · rw [← hkey, htm] at h'
          exact absurd (key_inj T (by omega) hsm hk (by omega) h') hkm

theorem inv_next {i m : Nat} (hI : Inv n s L PAR LAB i L m) : Inv n s L PAR LAB (i + 1) 0 m := by
  refine ⟨hI.1, fun k hk => ?_⟩
  rw [hI.2 k hk, Nat.add_zero, Nat.succ_mul]

theorem inv_le (T : Tree n s L PAR LAB TT) {i m k : Nat} (hI : Inv n s L PAR LAB i 0 m)
    (hk : k < n) (hki : k ≤ i) : k < m := by
  refine (hI.2 k hk).2 ?_
  by_cases hs : k < s
  · exact Or.inl hs
  · obtain ⟨hp, hl⟩ := T.par k (by omega) hk
    refine Or.inr ?_
    have h1 : PAR k * L + LAB k < (PAR k + 1) * L := by rw [Nat.succ_mul]; omega
    have h2 : (PAR k + 1) * L ≤ i * L := Nat.mul_le_mul_right _ (by omega)
    omega

theorem inv_lt (T : Tree n s L PAR LAB TT) {i m : Nat} (hI : Inv n s L PAR LAB i 0 m) (hi : i < n) :
    i < m :=
  inv_le T hI hi (Nat.le_refl i)

theorem inv_done (T : Tree n s L PAR LAB TT) {i m : Nat} (hI : Inv n s L PAR LAB i 0 m)
    (hle : m ≤ i) : m = n := by
  by_contra hne
  have hmn : m < n := by have := hI.1; omega
  have := inv_le T hI hmn hle
  omega

end CFSG.KC.J4Q.BfsOrder

end
