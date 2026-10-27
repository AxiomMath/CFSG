module

public import Certificates.Data.Kernel.PkTree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace CFSG.KC.PkTree

open CFSG.KC.Loop

theorem pkAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem pkIf_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem pkIf_false {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc
  exact h

theorem pkAllBelow_spec {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := pkAnd_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl hlm
      · exact pkIf_true h1 (Nat.blt_eq.mpr hlm)
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; omega
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := pkAnd_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhh with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by decide))
    (by rw [e]; exact him)
  rwa [e] at this

theorem pkSumBelow_eq {m hi : Nat} (f : Nat → Nat) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have inner : ∀ (hh n : Nat), Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft hh 6) l)) ih2) n =
      ∑ l ∈ Finset.range n, (if 64 * hh + l < m then f (64 * hh + l) else 0) := by
    intro hh n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      change Nat.add _ _ = _
      have e : Nat.add (Nat.shiftLeft hh 6) n = 64 * hh + n := by
        change hh <<< 6 + n = _
        rw [Nat.shiftLeft_eq]
        omega
      rw [e, Nat.add_eq, Nat.add_comm]
      congr 1
      by_cases hc : 64 * hh + n < m
      · simp [hc, Nat.blt_eq.mpr hc]
      · have : Nat.blt (64 * hh + n) m = false := by
          cases hb : Nat.blt (64 * hh + n) m
          · rfl
          · exact absurd (Nat.blt_eq.mp hb) hc
        simp [hc, this]
  have outer : ∀ n, Nat.rec (motive := fun _ => Nat) 0 (fun hh ih => Nat.add (
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft hh 6) l)) ih2) 64)
        ih) n = ∑ i ∈ Finset.range (64 * n), (if i < m then f i else 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.add _ _ = _
      rw [ih, inner, Nat.add_eq, Nat.mul_succ, Finset.sum_range_add, Nat.add_comm]
  change Nat.rec (motive := fun _ => Nat) 0 _ hi = _
  rw [outer, ← Nat.add_sub_cancel' hm, Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range (64 * hi - m), (if m + x < m then f (m + x) else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => by simp
  rw [h2, Nat.add_zero]
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.mem_range.mp hx]

theorem pkTree_sound {N hi w wg D G : Nat} {inSet isRoot gok : Nat → Bool}
    {step : Nat → Nat → Nat} (h : pkTreeOK N hi w wg D G inSet isRoot gok step = true)
    (hN : N ≤ 64 * hi) : ∀ x < N, inSet x = true → ∃ r, isRoot r = true ∧
      Relation.ReflTransGen
        (fun p y => ∃ g, gok g = true ∧ step g y = p ∧ y < N ∧ inSet y = true) r x := by
  have hall := pkAllBelow_spec h hN
  suffices H : ∀ n, ∀ x < N, inSet x = true → pkGet D w x ≤ n → ∃ r, isRoot r = true ∧
      Relation.ReflTransGen
        (fun p y => ∃ g, gok g = true ∧ step g y = p ∧ y < N ∧ inSet y = true) r x from
    fun x hx hs => H _ x hx hs le_rfl
  intro n
  induction n with
  | zero =>
    intro x hx hs hd
    have h1 := pkIf_true (hall x hx) hs
    have := (pkAnd_true h1).1
    simp [Nat.blt_eq] at this
    omega
  | succ n ih =>
    intro x hx hs hd
    have h1 := pkIf_true (hall x hx) hs
    unfold pkRecOK at h1
    obtain ⟨h0, h2⟩ := pkAnd_true h1
    cases hb : Nat.beq (pkGet D w x) 1
    · have h3 := pkIf_false h2 hb
      obtain ⟨hg, h4⟩ := pkAnd_true h3
      unfold pkParOK at h4
      obtain ⟨hp, h5⟩ := pkAnd_true h4
      obtain ⟨hps, h6⟩ := pkAnd_true h5
      obtain ⟨hp0, hpd⟩ := pkAnd_true h6
      have hpd' := Nat.blt_eq.mp hpd
      obtain ⟨r, hr, hrp⟩ := ih _ (Nat.blt_eq.mp hp) hps (by omega)
      exact ⟨r, hr, Relation.ReflTransGen.tail hrp ⟨_, hg, rfl, hx, hs⟩⟩
    · exact ⟨x, pkIf_true h2 hb, Relation.ReflTransGen.refl⟩

end CFSG.KC.PkTree

end
