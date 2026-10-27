module

public import Certificates.Data.Kernel.S1277K7213
public import CFSG.Certificates.Kernel.S1277KGmSound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
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

public section

namespace CFSG.KS.C7213

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm CFSG.KC.C7213 CFSG.KS.S1277Gm

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Enum.strictN y k = k y := by cases y <;> rfl

theorem allL_iff (f : ℕ → Bool) (l : List ℕ) : allL f l = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allL]
  | cons x xs ih =>
    change andB (f x) (allL f xs) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    simp

theorem forceM_eq (X : Mc) (k : Mc → Bool) : forceM X k = k X := by
  simp only [forceM, strictB_eq]

theorem isOne_iff (B : Mc) : isOne B = true ↔ B = Mc.one := by
  rcases B with ⟨a, b, c⟩
  simp only [isOne, andB_eq, Bool.and_eq_true, Nat.beq_eq, Mc.one, Mc.mk.injEq]

theorem pw_eq (A : Mc) : ∀ (n : ℕ) (B : Mc), pw A n B = isOne ((A.mul)^[n] B)
  | 0, _ => rfl
  | n + 1, B => by
    change forceM (mulF A B) (pw A n) = _
    rw [forceM_eq, pw_eq A n, mulF_eq, Function.iterate_succ_apply]

theorem pow_iter (A : Mc) : ∀ n : ℕ, A.pow n = (A.mul)^[n] Mc.one
  | 0 => rfl
  | n + 1 => by rw [Mc.pow, Function.iterate_succ_apply', pow_iter A n]

theorem ndK_sound : ∀ (L : List ℕ) (s : ℕ), ndK L s = true →
    L.Nodup ∧ ∀ x ∈ L, x < 262144 ∧ memS s x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: xs, s, h => by
    change andB (andB (Nat.blt x (nat_lit 262144)) (notB (memS s x)))
      (strictB (insS s x) (ndK xs)) = true at h
    rw [andB_eq, andB_eq, notB_eq, strictB_eq, Bool.and_eq_true, Bool.and_eq_true,
      Nat.blt_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hx, hm⟩, hr⟩ := h
    obtain ⟨hn, hall⟩ := ndK_sound xs _ hr
    have hrest : ∀ y ∈ xs, y ≠ x ∧ y < 262144 ∧ memS s y = false := fun y hy => by
      obtain ⟨hy1, hy2⟩ := hall y hy
      rw [memS_insS, Bool.or_eq_false_iff] at hy2
      refine ⟨fun e => ?_, hy1, hy2.1⟩
      subst e
      simp [hx] at hy2
    refine ⟨List.nodup_cons.2 ⟨fun hmem => (hrest x hmem).1 rfl, hn⟩, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨hx, hm⟩
    · exact (hrest y hy).2

theorem setK_mem : ∀ (L : List ℕ) (s i : ℕ), memS (setK L s) i = true → memS s i = true ∨ i ∈ L
  | [], _, _, h => Or.inl h
  | x :: xs, s, i, h => by
    change memS (CFSG.KC.Enum.strictN (insS s x) (setK xs)) i = true at h
    rw [strictN_eq] at h
    rcases setK_mem xs _ i h with h1 | h1
    · rw [memS_insS, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
      rcases h1 with h1 | ⟨rfl, -⟩
      · exact Or.inl h1
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem x h1)

theorem memS_zero (i : ℕ) : memS 0 i = false := by simp [memS]

theorem app_one (A : Mc) : A.app 1 = A.c0 := by simp [Mc.app, sV]

theorem app_four (A : Mc) : A.app 4 = A.c1 := by simp [Mc.app, sV]

theorem app_sixteen (A : Mc) : A.app 16 = A.c2 := by simp [Mc.app, sV]

theorem mem_v18 : ∀ c, c < 64 → oPts.contains (pn c) = true → c ∈ v18 := by decide

theorem col_of_inGm {A : Mc} (h : inGm A = true) {p : ℕ} (hp : p ∈ oPts) :
    oPts.contains (pn (A.app p)) = true := by
  unfold inGm at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 p hp

theorem ofIdx_inj {x y : ℕ} (hx : x < 262144) (hy : y < 262144) (e : Mc.ofIdx x = Mc.ofIdx y) :
    x = y := by
  simp only [Mc.ofIdx, Mc.mk.injEq] at e
  omega

theorem ofIdx_mcIdx {a b c : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    Mc.ofIdx (mcIdx ⟨a, b, c⟩) = ⟨a, b, c⟩ := by
  simp only [Mc.ofIdx, mcIdx, Mc.mk.injEq]
  omega

theorem facts (L : List ℕ) (hL : gmList = L.map Mc.ofIdx) (hlen : L.length = 1080)
    (h : chk7213 L = true) :
    gmList.length = 1080 ∧ gmList.Nodup ∧
      (∀ A ∈ gmList, A.Valid ∧ inGm A = true ∧ A.pow 60 = Mc.one) ∧
      ∀ c0 ∈ List.range 64, ∀ c1 ∈ List.range 64, ∀ c2 ∈ List.range 64,
        inGm ⟨c0, c1, c2⟩ = true → (⟨c0, c1, c2⟩ : Mc) ∈ gmList := by
  unfold chk7213 at h
  rw [andB_eq, andB_eq, strictB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hnd, hel, hcol⟩ := h
  obtain ⟨hn, hlt⟩ := ndK_sound L 0 hnd
  rw [allL_iff] at hel
  rw [hL]
  refine ⟨by rw [List.length_map, hlen], ?_, ?_, ?_⟩
  · exact hn.map_on fun x hx y hy e => ofIdx_inj (hlt x hx).1 (hlt y hy).1 e
  · intro A hA
    obtain ⟨n, hnL, rfl⟩ := List.mem_map.1 hA
    have := hel n hnL
    unfold eltK at this
    rw [andB_eq, Bool.and_eq_true, pw_eq, isOne_iff] at this
    refine ⟨?_, this.1, by rw [pow_iter]; exact this.2⟩
    simp only [Mc.Valid, Mc.ofIdx]
    omega
  · intro c0 h0 c1 h1 c2 h2 hg
    rw [List.mem_range] at h0 h1 h2
    have m0 := mem_v18 c0 h0 (by have := col_of_inGm hg (p := 1) (by decide); rwa [app_one] at this)
    have m1 := mem_v18 c1 h1 (by have := col_of_inGm hg (p := 4) (by decide); rwa [app_four] at this)
    have m2 := mem_v18 c2 h2
      (by have := col_of_inGm hg (p := 16) (by decide); rwa [app_sixteen] at this)
    unfold colK at hcol
    have hc := (allL_iff _ _).1 ((allL_iff _ _).1 ((allL_iff _ _).1 hcol c0 m0) c1 m1) c2 m2
    rw [orB_eq, notB_eq, hg, Bool.not_true, Bool.false_or] at hc
    rcases setK_mem L 0 _ hc with h0' | hmem
    · rw [memS_zero] at h0'
      exact absurd h0' Bool.false_ne_true
    · rw [← ofIdx_mcIdx h0 h1 h2]
      exact List.mem_map_of_mem hmem

end CFSG.KS.C7213

end
