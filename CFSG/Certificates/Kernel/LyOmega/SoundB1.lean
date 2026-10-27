module

public import CFSG.Certificates.Kernel.LyOmega.Defs
public import Certificates.Data.Kernel.LyOmega.Base
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section
namespace CFSG.KS.LyOm.SB1
open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KS.LyOm CFSG.KC.Loop

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem nIf_eq (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem fldW_eq (r o w : ℕ) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by cases v <;> rfl

private theorem shr6 (i : ℕ) : Nat.shiftRight i 6 = i / 64 := by
  change i >>> 6 = _
  rw [Nat.shiftRight_eq_div_pow]

private theorem land63 (i : ℕ) : Nat.land i 63 = i % 64 := by
  change i &&& 63 = _
  have : (63 : ℕ) = 2 ^ 6 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

private theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

private theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

private theorem getRec_eq (blk : ℕ → ℕ) (RB i : ℕ) :
    getRec blk RB i = blk (i / 64) / 2 ^ ((i % 64) * RB) % 2 ^ RB := by
  unfold getRec
  rw [strictN_eq', fldW_eq, shr6, land63]
  rfl

private theorem recAnd_iff (g : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (g l)) n = true ↔
      ∀ l < n, g l = true
  | 0 => ⟨fun _ l hl => absurd hl (Nat.not_lt_zero l), fun _ => rfl⟩
  | n + 1 => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (g l)) n) (g n) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, recAnd_iff g n]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact h2 l h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun l hl => h l (Nat.lt_succ_of_lt hl)⟩

private theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := (recAnd_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2 ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l))) 64) hi).1 h (i / 64) (by omega)
  have h2 := (recAnd_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
    omega
  dsimp only at h2
  rw [e, blt_iff.2 him] at h2
  exact h2

private theorem shr6' (x : ℕ) : Nat.shiftRight x 6 = x / 64 := shr6 x

private theorem bEnt_eq (X i j : ℕ) : bEnt X i j = X / 2 ^ (1332 * i + 12 * j) % 2 ^ 12 :=
  fldW_eq _ _ _

private theorem sEnt_eq (X i j : ℕ) : sEnt X i j = X / 2 ^ (77 * i + 11 * j) % 2 ^ 11 :=
  fldW_eq _ _ _

theorem trOK_sound {r c X Y : ℕ} (h : trOK r c X Y = true) :
    ∀ i < r, ∀ j < c, ent 12 1332 Y j i = ent 12 1332 X i j := by
  intro i hi j hj
  have hm : r * c ≤ 64 * (Nat.shiftRight (Nat.mul r c) (nat_lit 6) + 1) := by
    rw [shr6]; change r * c ≤ 64 * (r * c / 64 + 1); omega
  have key := allBelow_spec h hm (i * c + j) (by
    calc i * c + j < i * c + c := by omega
      _ = (i + 1) * c := by ring
      _ ≤ r * c := Nat.mul_le_mul_right c hi)
  have hc : 0 < c := by omega
  have e1 : (i * c + j) / c = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hj]; simp
  have e2 : (i * c + j) % c = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have key' : Nat.beq (bEnt X i j) (bEnt Y j i) = true := by
    have : (fun t => (fun i j => Nat.beq (bEnt X i j) (bEnt Y j i)) (Nat.div t c) (Nat.mod t c))
        (i * c + j) = Nat.beq (bEnt X i j) (bEnt Y j i) := by
      change Nat.beq (bEnt X ((i * c + j) / c) ((i * c + j) % c))
        (bEnt Y ((i * c + j) % c) ((i * c + j) / c)) = _
      rw [e1, e2]
    rw [← this]; exact key
  have := beq_iff.1 key'
  rw [bEnt_eq, bEnt_eq] at this
  simp only [ent]
  rw [← this]

theorem relayOK_sound {X Y : ℕ} (h : relayOK X Y = true) :
    Y < 2 ^ 539 ∧ ∀ i j : Fin 7, smM Y i j = ent 12 1332 X i j := by
  unfold relayOK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have := beq_iff.1 h1
    change Y >>> 539 = 0 at this
    rw [Nat.shiftRight_eq_div_pow] at this
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 this
  · intro i j
    have := (recAnd_iff (fun t => (fun i j => Nat.beq (bEnt X i j) (sEnt Y i j))
      (Nat.div t 7) (Nat.mod t 7)) 49).1 h2 (7 * i.val + j.val) (by omega)
    have e1 : (7 * i.val + j.val) / 7 = i.val := by omega
    have e2 : (7 * i.val + j.val) % 7 = j.val := by omega
    have key : Nat.beq (bEnt X i.val j.val) (sEnt Y i.val j.val) = true := by
      change Nat.beq (bEnt X ((7 * i.val + j.val) / 7) ((7 * i.val + j.val) % 7))
        (sEnt Y ((7 * i.val + j.val) / 7) ((7 * i.val + j.val) % 7)) = true at this
      rw [e1, e2] at this
      exact this
    have := beq_iff.1 key
    rw [bEnt_eq, sEnt_eq] at this
    simp only [smM, ent]
    rw [← this]

theorem sSort_sound {KX SG : ℕ → ℕ} {n k₀ c : ℕ} (h : sSort KX SG n k₀ c = true) :
    ∀ k, k₀ ≤ k → k < k₀ + c → getRec SG 20 k < n ∧ getRec SG 20 (k + 1) < n ∧
      getRec KX 539 (getRec SG 20 k) < getRec KX 539 (getRec SG 20 (k + 1)) := by
  intro k hk1 hk2
  have hm : c ≤ 64 * (Nat.shiftRight c (nat_lit 6) + 1) := by
    rw [shr6]; omega
  have key := allBelow_spec h hm (k - k₀) (by omega)
  have e : Nat.add k₀ (k - k₀) = k := by change k₀ + (k - k₀) = k; omega
  dsimp only at key
  rw [e] at key
  simp only [letB_eq, bAnd_eq, Bool.and_eq_true, blt_iff, Nat.succ_eq_add_one] at key
  exact ⟨key.1, key.2.1, key.2.2⟩

private theorem fldW_leaf (KX : ℕ → ℕ) (b r : ℕ) (hr : r < 64) :
    fldW (KX b) (Nat.mul 539 r) 539 = getRec KX 539 (64 * b + r) := by
  rw [getRec_eq, fldW_eq]
  have e1 : (64 * b + r) / 64 = b := by omega
  have e2 : (64 * b + r) % 64 = r := by omega
  rw [e1, e2, Nat.mul_comm r]
  rfl

private theorem sCount_rec (C : SConsts) (KX : ℕ → ℕ) (n b : ℕ) : ∀ t, t ≤ 64 →
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => strictN acc (fun a =>
        nIf(Nat.blt (Nat.add (Nat.shiftLeft b (nat_lit 6)) r) n,
          Nat.add a (sClass C (fldW (KX b) (Nat.mul (nat_lit 539) r) (nat_lit 539))), a))) t =
      ∑ r ∈ (Finset.range t).filter (fun r => 64 * b + r < n),
        sClass C (getRec KX 539 (64 * b + r))
  | 0, _ => by simp
  | t + 1, ht => by
    have ih := sCount_rec C KX n b t (by omega)
    change strictN (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => strictN acc (fun a =>
        nIf(Nat.blt (Nat.add (Nat.shiftLeft b (nat_lit 6)) r) n,
          Nat.add a (sClass C (fldW (KX b) (Nat.mul (nat_lit 539) r) (nat_lit 539))), a))) t) _ = _
    rw [strictN_eq', ih]
    have hsh : Nat.shiftLeft b 6 = 64 * b := by
      change b <<< 6 = _
      rw [Nat.shiftLeft_eq]; omega
    show (Bool.rec (motive := fun _ => ℕ) _ _ (Nat.blt (Nat.shiftLeft b 6 + t) n)) = _
    rw [nIf_eq, hsh, Finset.range_add_one, Finset.filter_insert, fldW_leaf KX b t (by omega)]
    by_cases hlt : 64 * b + t < n
    · rw [if_pos (blt_iff.2 hlt), if_pos hlt, Finset.sum_insert (by simp)]
      exact Nat.add_comm _ _
    · rw [if_neg (by rw [blt_iff]; exact hlt), if_neg hlt]

theorem sCountLeaf_eq {C : SConsts} {KX : ℕ → ℕ} {n b : ℕ} :
    sCountLeaf C KX n b = ∑ r ∈ (Finset.range 64).filter (fun r => 64 * b + r < n),
      sClass C (getRec KX 539 (64 * b + r)) :=
  sCount_rec C KX n b 64 le_rfl

end CFSG.KS.LyOm.SB1
end
