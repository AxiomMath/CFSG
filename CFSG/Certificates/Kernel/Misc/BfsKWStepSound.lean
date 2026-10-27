module

public import Certificates.Data.Kernel.Misc.BfsKWStep
public import CFSG.Certificates.Kernel.G2Three.Tables

public section

namespace CFSG.KC.BfsKW

open CFSG.KD.BfsK CFSG.KD.BfsKW CFSG.KC.Loop

theorem recAnd_ofW (f : ℕ → Bool) : ∀ n, (∀ i < n, f i = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n) (f n) = true
    rw [h n (by omega)]
    exact recAnd_ofW f n fun i hi => h i (by omega)

theorem allBelow_ofW {m hi : ℕ} {f : ℕ → Bool} (h : ∀ i < m, f i = true) :
    allBelow m hi f = true := by
  unfold allBelow
  refine recAnd_ofW _ hi fun h' _ => recAnd_ofW (fun l => (fun i =>
    bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h' 6) l)) 64 fun l _ => ?_
  dsimp only
  by_cases hb : Nat.blt (Nat.add (Nat.shiftLeft h' 6) l) m = true
  · rw [hb]
    exact h _ (Nat.blt_eq.mp hb)
  · rw [Bool.eq_false_iff.2 hb]

theorem stepRecW_at {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {o n k h : ℕ}
    (hr : stepRecW R st o n k h = true) : ∀ s < k, stepHW R st o n k h s = true :=
  CFSG.KC.G2Three.recAnd_g2 (fun s => stepHW R st o n k h s) k hr

theorem stepSlW_at {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {o n k S : ℕ} (hS : n ≤ 1024 * S)
    (h : ∀ j < S, stepSlW R st o n k j = true) : ∀ t < n, stepRecW R st o n k t = true := by
  intro t ht
  have h1 := CFSG.KC.G2Three.allBelow_g2 (h (t / 1024) (by omega)) (by norm_num) (t % 1024)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (t / 1024) 1024) (t % 1024) = t := by
    change t / 1024 * 1024 + t % 1024 = t
    omega
  rw [e, Nat.blt_eq.mpr ht] at h1
  simpa using h1

theorem succ_divmodW {i k : ℕ} (hk : 0 < k) :
    (i % k + 1 < k → (i + 1) % k = i % k + 1 ∧ (i + 1) / k = i / k) ∧
      (¬ i % k + 1 < k → (i + 1) % k = 0 ∧ (i + 1) / k = i / k + 1) := by
  have e : i + 1 = (i % k + 1) + k * (i / k) := by
    have := Nat.mod_add_div i k
    omega
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ hk,
      Nat.div_eq_of_lt hlt, Nat.zero_add]
    exact ⟨rfl, rfl⟩
  · have hk' : i % k + 1 = k := by
      have := Nat.mod_lt i hk
      omega
    rw [e, hk', Nat.add_mul_mod_self_left, Nat.mod_self, Nat.add_mul_div_left _ _ hk,
      Nat.div_self hk, Nat.add_comm 1]
    exact ⟨rfl, rfl⟩

theorem next_countW (R : ℕ → ℕ) {o k i : ℕ} (hk : 0 < k) :
    cond (Nat.blt (Nat.succ (i % k)) k) (recFW R o (Nat.add 4 (Nat.succ (i % k))) (i / k))
      (recFW R o 4 (Nat.succ (i / k))) = recCW R o k (Nat.succ i) := by
  unfold recCW
  by_cases hlt : i % k + 1 < k
  · obtain ⟨h1, h2⟩ := (succ_divmodW hk).1 hlt
    rw [Nat.blt_eq.mpr hlt, cond_true]
    change _ = recFW R o (4 + (i + 1) % k) ((i + 1) / k)
    rw [h1, h2]
    rfl
  · obtain ⟨h1, h2⟩ := (succ_divmodW hk).2 hlt
    rw [Bool.eq_false_iff.2 fun hb => hlt (Nat.blt_eq.mp hb), cond_false]
    change _ = recFW R o (4 + (i + 1) % k) ((i + 1) / k)
    rw [h1, h2]

theorem stepG_of_slW {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {o n k hi S : ℕ} (hk : 0 < k)
    (h0 : recCW R o k 0 = 1) (hn : recCW R o k (n * k) = n) (hS : n ≤ 1024 * S)
    (h : ∀ j < S, stepSlW R st o n k j = true) :
    CFSG.KD.Sp62.stepG st (recX R o) (recFW R o 0) (recFW R o 1) (recCW R o k) (recPOSW R o k)
      n k hi = true := by
  have hr := stepSlW_at hS h
  unfold CFSG.KD.Sp62.stepG
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  refine ⟨⟨h0, hn⟩, allBelow_ofW fun i hi' => ?_⟩
  have hi : i < n * k := hi'
  have hh : i / k < n := (Nat.div_lt_iff_lt_mul hk).2 hi
  have e := stepRecW_at (hr (i / k) hh) (i % k) (Nat.mod_lt _ hk)
  unfold stepHW at e
  rw [next_countW R hk] at e
  exact e

end CFSG.KC.BfsKW

end
