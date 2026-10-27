module

public import Certificates.Data.Kernel.G23F48.Pts
public import CFSG.Certificates.Kernel.TreeKSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.G23F48

open CFSG.KC.Enum CFSG.KS

private theorem nIf_ite (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem bIf_ite (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem beq_t {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem scan_succ (p r : Nat) : normScan p (r + 1) =
    if pg 2 (mask 2) p r < 3 then
      (if normScan p r = 0 then
        (if pg 2 (mask 2) p r = 0 then 0 else if pg 2 (mask 2) p r = 1 then 1 else 2)
      else normScan p r)
    else 2 := by
  have e : normScan p (r + 1) = normStep (pg 2 (mask 2) p r) (normScan p r) :=
    strictN_app (pg 2 (mask 2) p r) (fun v => normStep v (normScan p r))
  rw [e]
  unfold normStep
  simp only [nIf_ite, Nat.blt_eq, beq_t]

private theorem scan_spec (p : Nat) : ∀ r,
    (normScan p r = 0 → ∀ s < r, pg 2 (mask 2) p s = 0) ∧
    (normScan p r = 1 → (∀ s < r, pg 2 (mask 2) p s < 3) ∧
      ∃ t < r, (∀ s < t, pg 2 (mask 2) p s = 0) ∧ pg 2 (mask 2) p t = 1) := by
  intro r
  induction r with
  | zero => exact ⟨fun _ s hs => absurd hs (Nat.not_lt_zero s), fun h => absurd h Nat.zero_ne_one⟩
  | succ r ih =>
    obtain ⟨ih0, ih1⟩ := ih
    rw [scan_succ]
    by_cases h3 : pg 2 (mask 2) p r < 3
    · rw [if_pos h3]
      by_cases h0 : normScan p r = 0
      · rw [if_pos h0]
        have hz := ih0 h0
        by_cases hv0 : pg 2 (mask 2) p r = 0
        · rw [if_pos hv0]
          refine ⟨fun _ s hs => ?_, fun h => absurd h (by decide)⟩
          rcases Nat.lt_or_ge s r with h1 | h1
          · exact hz s h1
          · have e : s = r := by omega
            rw [e]
            exact hv0
        · rw [if_neg hv0]
          by_cases hv1 : pg 2 (mask 2) p r = 1
          · rw [if_pos hv1]
            refine ⟨fun h => absurd h (by decide), fun _ => ⟨fun s hs => ?_, r, by omega, hz, hv1⟩⟩
            rcases Nat.lt_or_ge s r with h1 | h1
            · rw [hz s h1]
              decide
            · have e : s = r := by omega
              rw [e]
              exact h3
          · rw [if_neg hv1]
            exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      · rw [if_neg h0]
        refine ⟨fun h => absurd h h0, fun h => ?_⟩
        obtain ⟨ha, t, ht, hb⟩ := ih1 h
        refine ⟨fun s hs => ?_, t, by omega, hb⟩
        rcases Nat.lt_or_ge s r with h1 | h1
        · exact ha s h1
        · have e : s = r := by omega
          rw [e]
          exact h3
    · rw [if_neg h3]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem ptNormK_spec {p : Nat} (h : ptNormK p = true) :
    p >>> 28 = 0 ∧ (∀ c < 14, pg 2 (mask 2) p c < 3) ∧
      ∃ r < 14, (∀ s < r, pg 2 (mask 2) p s = 0) ∧ pg 2 (mask 2) p r = 1 := by
  unfold ptNormK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ha, hb⟩ := (scan_spec p 14).2 (beq_t.1 h2)
  exact ⟨beq_t.1 h1, ha, hb⟩

private theorem dotN_eq (MA p r : Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c acc => Nat.add acc (Nat.mul (pg (nat_lit 2) (mask (nat_lit 2)) MA
        (Nat.add (Nat.mul (nat_lit 14) r) c)) (pg (nat_lit 2) (mask (nat_lit 2)) p c))) n =
    ((List.range n).map fun c => pg 2 (mask 2) MA (14 * r + c) * pg 2 (mask 2) p c).sum := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ← ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rfl

theorem dotK_eq (MA p r : Nat) :
    dotK MA p r = ((List.range 14).map fun c =>
      pg 2 (mask 2) MA (14 * r + c) * pg 2 (mask 2) p c).sum :=
  dotN_eq MA p r 14

theorem ptsK_spec {F : Nat → Nat} (h : ptsK F = true) :
    (∀ i < 728, ptNormK (F i) = true) ∧ ∀ i < 728, ∀ l < 728, F i = F l → i = l := by
  unfold ptsK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨allN_spec h1, fun i hi l hl e => ?_⟩
  have hd := CFSG.KC.TreeK.distinctK_sound h2
  refine hd.eq_of_getElem_eq (i := i) (j := l) (by simpa using hi) (by simpa using hl) ?_
  simpa using e

theorem genK_spec {G MA : Nat} {F : Nat → Nat} {i : Nat} (h : genK G MA F i = true) :
    pg 10 (mask 10) G i < 728 ∧ ∃ s, (s = 1 ∨ s = 2) ∧ ∀ r < 14,
      pg 2 (mask 2) (F (pg 10 (mask 10) G i)) r = s * dotK MA (F i) r % 3 := by
  unfold genK at h
  rw [strictB_app, bAnd_iff, bIf_ite] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [← Nat.blt_eq]; exact h1, ?_⟩
  have rows : ∀ {q s : Nat}, rowsK MA (F i) q s = true → ∀ r < 14,
      pg 2 (mask 2) q r = s * dotK MA (F i) r % 3 := fun {q s} hq r hr =>
    beq_t.1 (allN_spec hq r hr)
  by_cases hs : rowsK MA (F i) (F (pg 10 (mask 10) G i)) 1 = true
  · exact ⟨1, Or.inl rfl, rows hs⟩
  · rw [if_neg hs] at h2
    exact ⟨2, Or.inr rfl, rows h2⟩

theorem gensK_spec {G MA F : Nat → Nat} (h : gensK G MA F = true) {k i : Nat} (hk : k < 4)
    (hi : i < 728) : genK (G k) (MA k) F i = true :=
  allN_spec (allN_spec h k hk) i hi

end CFSG.KC.G23F48

end
