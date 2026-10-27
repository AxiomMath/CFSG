module

public import Certificates.Data.Kernel.Misc.BfsKWWalk
public import CFSG.Certificates.Kernel.Misc.BfsKWStepSound

public section

namespace CFSG.KC.BfsKW

open CFSG.KD.BfsK CFSG.KD.BfsKW CFSG.KC.Loop

theorem strictW_eq (y : ℕ) (k : ℕ → Bool) : strictW y k = k y := by
  cases y <;> rfl

theorem bAnd_ttW {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem bIf_ttW {c : Bool} {a : Bool} (h : Bool.rec (motive := fun _ => Bool) true a c = true)
    (hc : c = true) : a = true := by
  rw [hc] at h
  exact h

theorem walkLW_succ (R : ℕ → ℕ) (o : ℕ) (P : ℕ → ℕ) (B : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (b m rn qn : ℕ) :
    walkLW R o P B b (m + 1) rn qn = strictW (R (o + (b + m))) fun r =>
      strictW (R (o + P r)) fun q => bAnd(B (b + m) r rn q qn, walkLW R o P B b m r q) :=
  rfl

theorem walkLW_at {R : ℕ → ℕ} {o : ℕ} {P : ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {b : ℕ} :
    ∀ m, walkLW R o P B b m (R (o + (b + m))) (R (o + P (R (o + (b + m))))) = true →
    ∀ l < m, B (b + l) (R (o + (b + l))) (R (o + (b + (l + 1)))) (R (o + P (R (o + (b + l)))))
      (R (o + P (R (o + (b + (l + 1)))))) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | m + 1, h, l, hl => by
    rw [walkLW_succ, strictW_eq, strictW_eq] at h
    obtain ⟨h1, h2⟩ := bAnd_ttW h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · exact walkLW_at m h2 l hl
    · exact h1

theorem walkW_at {R : ℕ → ℕ} {o : ℕ} {P : ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {b m : ℕ}
    (h : walkW R o P B b m = true) :
    ∀ l < m, B (b + l) (R (o + (b + l))) (R (o + (b + (l + 1)))) (R (o + P (R (o + (b + l)))))
      (R (o + P (R (o + (b + (l + 1)))))) = true := by
  unfold walkW at h
  rw [strictW_eq, strictW_eq] at h
  exact walkLW_at m h

theorem slW_at {R : ℕ → ℕ} {o : ℕ} {P : ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {j : ℕ}
    (h : Nat.rec (motive := fun _ => Bool) true (fun c ih => bAnd(walkW R o P B
      (Nat.add (Nat.mul j 1024) (Nat.mul c 64)) 64, ih)) 16 = true) (l : ℕ) (hl : l < 1024) :
    B (1024 * j + l) (R (o + (1024 * j + l))) (R (o + (1024 * j + l + 1)))
      (R (o + P (R (o + (1024 * j + l))))) (R (o + P (R (o + (1024 * j + l + 1))))) = true := by
  have h1 := walkW_at (CFSG.KC.G2Three.recAnd_g2 (fun c => walkW R o P B
    (Nat.add (Nat.mul j 1024) (Nat.mul c 64)) 64) 16 h (l / 64) (by omega)) (l % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul j 1024) (Nat.mul (l / 64) 64) + l % 64 = 1024 * j + l := by
    change j * 1024 + l / 64 * 64 + l % 64 = 1024 * j + l
    omega
  have e1 : Nat.add (Nat.mul j 1024) (Nat.mul (l / 64) 64) + (l % 64 + 1) = 1024 * j + l + 1 := by
    change j * 1024 + l / 64 * 64 + (l % 64 + 1) = 1024 * j + l + 1
    omega
  rw [e, e1] at h1
  exact h1

theorem split_ltW {n S i : ℕ} (hS : n ≤ 1024 * S) (hi : i < n) :
    i / 1024 < S ∧ i % 1024 < 1024 ∧ 1024 * (i / 1024) + i % 1024 = i :=
  ⟨by omega, Nat.mod_lt _ (by norm_num), Nat.div_add_mod i 1024⟩

theorem buildG_of_slW {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {o n k hi S : ℕ} (hS : n ≤ 1024 * S)
    (h : ∀ j < S, buildSlW R st o n k j = true) :
    CFSG.KD.Sp62.buildG st (recX R o) (recFW R o 0) (recFW R o 1) n k hi = true := by
  unfold CFSG.KD.Sp62.buildG
  refine allBelow_ofW fun i hi' => ?_
  have hi : i + 1 < n := by
    change i < n - 1 at hi'
    omega
  obtain ⟨hj, hl, e⟩ := split_ltW hS (show i < n by omega)
  have h1 := slW_at (P := fun r => fldW r 0) (B := buildAtW st n k) (h _ hj) _ hl
  rw [e] at h1
  unfold buildAtW at h1
  have h2 := bIf_ttW h1 (Nat.blt_eq.mpr hi)
  rw [strictW_eq] at h2
  exact h2

theorem sortK_of_slW {R : ℕ → ℕ} {o n hi S : ℕ} (hS : n ≤ 1024 * S)
    (h : ∀ j < S, sortSlW R o n j = true) :
    CFSG.KD.G2Three.sortK (recX R o) (recFW R o 2) (recFW R o 3) n hi = true := by
  unfold CFSG.KD.G2Three.sortK
  refine allBelow_ofW fun i hi => ?_
  obtain ⟨hj, hl, e⟩ := split_ltW hS hi
  have h1 := slW_at (P := fun r => fldW r 2) (B := sortAtW R o n) (h _ hj) _ hl
  rw [e] at h1
  unfold sortAtW at h1
  have h2 := bIf_ttW h1 (Nat.blt_eq.mpr hi)
  rw [strictW_eq] at h2
  exact h2

end CFSG.KC.BfsKW

end
