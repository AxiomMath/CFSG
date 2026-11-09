module

public import Certificates.Data.Kernel.SporLatOrbN
public import Aesop.BuiltinRules
public import Batteries.Data.List.Lemmas
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
import Mathlib.Data.List.Nodup

public section

namespace CFSG.KC.SLOrb

variable (actF : Nat → Nat → Nat) (m : Nat) (Δ : Nat)

inductive ReachN : Nat → Prop
  | base : ReachN Δ
  | step {x l : Nat} : ReachN x → l < m → ReachN (actF l x)

theorem allNR_iff (f : Nat → Bool) : ∀ n, allNR n f = true ↔ ∀ i < n, f i = true
  | 0 => ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | n + 1 => by
    have ih := allNR_iff f n
    change (f n && allNR n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

theorem strictMono_of_succ {c : Nat → Nat} {n : Nat}
    (h : ∀ i, i + 1 < n → c i < c (i + 1)) : ∀ i j, i < j → j < n → c i < c j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · exact Nat.lt_trans (ih h' (by omega)) (h j hj)
    · exact h i hj

theorem orbRec_sound {R : Nat → Nat} {n iz : Nat} (h : orbRec actF R n Δ iz = true) :
    ∃ O : List Nat, O.Nodup ∧ O.length = n ∧ Δ ∈ O ∧
      (∀ x ∈ O, ∀ l < 2, actF l x ∈ O) ∧ ∀ x ∈ O, ReachN actF 2 Δ x := by
  unfold orbRec at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨hiz, hz⟩, hall⟩ := h
  have hR := (allNR_iff _ n).1 hall
  let c : Nat → Nat := fun i => rCode (R i)
  have hrec : ∀ i < n, (i + 1 < n → c i < c (i + 1)) ∧
      (∀ l < 2, rRow l (R i) < n ∧ c (rRow l (R i)) = actF l (c i)) ∧
      (rDep (R i) = 0 → c i = Δ) ∧
      (rDep (R i) ≠ 0 → rPar (R i) < n ∧ rVia (R i) < 2 ∧
        rDep (R (rPar (R i))) + 1 = rDep (R i) ∧ rRow (rVia (R i)) (R (rPar (R i))) = i) := by
    intro i hi
    have e := hR i hi
    unfold recOK at e
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at e
    obtain ⟨⟨⟨⟨⟨hs, h0⟩, e0⟩, h1⟩, e1⟩, hd⟩ := e
    refine ⟨fun hn => ?_, fun l hl => ?_, fun hd0 => ?_, fun hd0 => ?_⟩
    · rcases hs with hs | hs
      · omega
      · exact hs
    · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact ⟨h0, e0⟩
      · exact ⟨h1, e1⟩
    · have : Nat.beq (rDep (R i)) 0 = true := by rw [hd0]; rfl
      rw [this, Bool.cond_true] at hd
      exact Nat.eq_of_beq_eq_true hd
    · have : Nat.beq (rDep (R i)) 0 = false := by
        cases e : Nat.beq (rDep (R i)) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hd0
      rw [this, Bool.cond_false] at hd
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hd
      obtain ⟨⟨⟨hp, hv⟩, hdp⟩, hrw⟩ := hd
      exact ⟨hp, hv, hdp, hrw⟩
  have hmono := strictMono_of_succ (c := c) (n := n) fun i hi => (hrec i (by omega)).1 hi
  have hinj : ∀ i < n, ∀ j < n, c i = c j → i = j := by
    intro i hi j hj e
    rcases Nat.lt_trichotomy i j with h' | h' | h'
    · exact absurd e (Nat.ne_of_lt (hmono i j h' hj))
    · exact h'
    · exact absurd e.symm (Nat.ne_of_lt (hmono j i h' hi))
  have hreach : ∀ d, ∀ i < n, rDep (R i) = d → ReachN actF 2 Δ (c i) := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      rw [(hrec i hi).2.2.1 hd]
      exact ReachN.base
    | succ d ih =>
      intro i hi hd
      obtain ⟨hp, hv, hdp, hrw⟩ := (hrec i hi).2.2.2 (by omega)
      have hpr := ih _ hp (by omega)
      have e := ((hrec _ hp).2.1 _ hv).2
      rw [hrw] at e
      rw [e]
      exact ReachN.step hpr hv
  refine ⟨(List.range n).map c, ?_, by simp, ?_, ?_, ?_⟩
  · exact List.Nodup.map_on (fun a ha b hb e => hinj a (List.mem_range.1 ha) b
      (List.mem_range.1 hb) e) List.nodup_range
  · exact List.mem_map.2 ⟨iz, List.mem_range.2 hiz, hz⟩
  · intro x hx l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2⟩ := (hrec i (List.mem_range.1 hi)).2.1 l hl
    exact List.mem_map.2 ⟨_, List.mem_range.2 h1, h2⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hreach _ i (List.mem_range.1 hi) rfl

end CFSG.KC.SLOrb

end
