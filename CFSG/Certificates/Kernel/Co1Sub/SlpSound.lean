module

public import Certificates.Data.Kernel.Co1Sub.Defs
public import CFSG.Certificates.Kernel.TabMatGrpSound

public section

namespace CFSG.KC.Co1Sub

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.TabMatGrp

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem nrec_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem getL_zero_eq (L : List Nat) (i : Nat) : getL 0 L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem lenL_eq_length (L : List Nat) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg Nat.succ ih

theorem mulS_eq (A B : Nat) : mulS A B = mulF 24 A B := mulW_eq 24 A B

theorem MatP_oneS : MatP 24 oneS = 1 := MatP_id 24

theorem bit_zero_eq (c : Nat) : bit c 0 = decide (c % 2 = 1) := by
  change Nat.beq (c &&& 1) 1 = decide (c % 2 = 1)
  rw [Nat.and_one_is_mod]
  by_cases h : c % 2 = 1
  · rw [h]
    rfl
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.2 fun hb => h (Nat.eq_of_beq_eq_true hb)

theorem shiftRight_one_eq (c : Nat) : c.shiftRight 1 = c / 2 := by
  change c >>> 1 = c / 2
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem refsK_iff (lim : Nat) : ∀ w : List Nat, refsK lim w = true ↔ ∀ c ∈ w, c / 2 < lim
  | [] => by simp [refsK]
  | c :: w => by
    change andB (Nat.blt (c >>> 1) lim) (refsK lim w) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, refsK_iff lim w, Nat.blt_eq, Nat.shiftRight_eq_div_pow,
      pow_one, List.forall_mem_cons]

theorem slpAt_spec {nB : Nat} {B Bi M Mi : List Nat} : ∀ (W : List (List Nat)) (j : Nat),
    slpAt nB B Bi M Mi W j = true → M.length = j + W.length ∧ Mi.length = j + W.length ∧
      ∀ t < W.length, (∀ c ∈ W.getD t [], c / 2 < nB + (j + t)) ∧
        M.getD (j + t) 0 = wordS nB B Bi M Mi (W.getD t []) ∧
        mulS (M.getD (j + t) 0) (Mi.getD (j + t) 0) = oneS
  | [], j, h => by
    change andB (Nat.beq (lenL M) j) (Nat.beq (lenL Mi) j) = true at h
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, lenL_eq_length, lenL_eq_length] at h
    exact ⟨h.1, h.2, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | w :: W, j, h => by
    change strictB j (fun j => andB (refsK (Nat.add nB j) w) (andB
      (Nat.beq (getL (nat_lit 0) M j) (wordS nB B Bi M Mi w))
      (andB (Nat.beq (mulS (getL (nat_lit 0) M j) (getL (nat_lit 0) Mi j)) oneS)
        (slpAt nB B Bi M Mi W (Nat.succ j))))) = true at h
    rw [strictB_eq, andB_eq, andB_eq, andB_eq] at h
    simp only [Bool.and_eq_true, Nat.beq_eq, getL_zero_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨l1, l2, ih⟩ := slpAt_spec W (Nat.succ j) h4
    refine ⟨by simp only [l1, List.length_cons]; omega, by simp only [l2, List.length_cons]; omega,
      fun t ht => ?_⟩
    rcases t with _ | s
    · simpa only [Nat.add_zero, List.getD_cons_zero, (refsK_iff _ w).1 h1] using
        ⟨(refsK_iff _ w).1 h1, h2, h3⟩
    · obtain ⟨r1, r2, r3⟩ := ih s (by simpa using ht)
      have e : Nat.succ j + s = j + (s + 1) := by omega
      rw [e] at r1 r2 r3
      exact ⟨by simpa only [List.getD_cons_succ] using r1, by simpa only [List.getD_cons_succ] using r2,
        r3⟩

variable {G : Type*} [Group G] {φ : G →* GL (Fin 24) (ZMod 2)}

@[expose] def letG (e : ℕ → G) (c : ℕ) : G := if c % 2 = 1 then (e (c / 2))⁻¹ else e (c / 2)

section Word

variable {e : ℕ → G} {nB lim : Nat} {B Bi M Mi : List Nat}
  (hE : ∀ k < lim, MatP 24 (entS nB B M k) = matOf φ (e k) ∧
    MatP 24 (entS nB Bi Mi k) = matOf φ (e k)⁻¹)
include hE

theorem MatP_letS {c : Nat} (hc : c / 2 < lim) :
    MatP 24 (letS nB B Bi M Mi c) = matOf φ (letG e c) := by
  unfold letS letG
  rw [nrec_eq, bit_zero_eq, shiftRight_one_eq]
  by_cases h : c % 2 = 1
  · simp only [h, decide_true, if_true]
    exact (hE _ hc).2
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    exact (hE _ hc).1

theorem MatP_wordFromS : ∀ (w : List Nat) (acc : Nat), (∀ c ∈ w, c / 2 < lim) →
    MatP 24 (wordFromS nB B Bi M Mi w acc) = MatP 24 acc * matOf φ ((w.map (letG e)).prod)
  | [], acc, _ => by
    change MatP 24 acc = _
    rw [List.map_nil, List.prod_nil, matOf_one, mul_one]
  | c :: w, acc, hw => by
    change MatP 24 (strictN (mulS acc (letS nB B Bi M Mi c)) (wordFromS nB B Bi M Mi w)) = _
    rw [strictN_eq, MatP_wordFromS w _ fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'), mulS_eq,
      MatP_mul, MatP_letS hE (hw c List.mem_cons_self), List.map_cons, List.prod_cons, matOf_mul,
      mul_assoc]

end Word

theorem slpK_sound {e : ℕ → G} {B Bi M Mi : List Nat} {W : List (List Nat)}
    (h : slpK B Bi W M Mi = true)
    (hB : ∀ i < B.length, MatP 24 (B.getD i 0) = matOf φ (e i) ∧
      MatP 24 (Bi.getD i 0) = matOf φ (e i)⁻¹)
    (he : ∀ t < W.length, e (B.length + t) = ((W.getD t []).map (letG e)).prod) :
    ∀ t < W.length, (∀ c ∈ W.getD t [], c / 2 < B.length + t) ∧
      MatP 24 (M.getD t 0) = matOf φ (e (B.length + t)) ∧
      MatP 24 (Mi.getD t 0) = matOf φ (e (B.length + t))⁻¹ := by
  unfold slpK at h
  rw [strictB_eq, lenL_eq_length] at h
  obtain ⟨-, -, hs⟩ := slpAt_spec W 0 h
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    obtain ⟨hr, hm, hi⟩ := hs t ht
    rw [Nat.zero_add] at hr hm hi
    have hE : ∀ k < B.length + t, MatP 24 (entS B.length B M k) = matOf φ (e k) ∧
        MatP 24 (entS B.length Bi Mi k) = matOf φ (e k)⁻¹ := by
      intro k hk
      unfold entS
      rw [nrec_eq, nrec_eq, getL_zero_eq, getL_zero_eq, getL_zero_eq, getL_zero_eq]
      by_cases hkB : k < B.length
      · simp only [Nat.blt_eq.mpr hkB, if_true]
        exact hB k hkB
      · have hlt : k - B.length < t := by omega
        obtain ⟨-, h2, h3⟩ := ih (k - B.length) hlt (by omega)
        have ek : B.length + (k - B.length) = k := by omega
        rw [ek] at h2 h3
        have hf : Nat.blt k B.length = false := Bool.eq_false_iff.2 fun h => hkB (Nat.blt_eq.mp h)
        simp only [hf, Bool.false_eq_true, if_false]
        exact ⟨h2, h3⟩
    have hw := MatP_wordFromS (φ := φ) (e := e) hE (W.getD t []) oneS hr
    rw [MatP_oneS, one_mul, ← he t ht] at hw
    have hM : MatP 24 (M.getD t 0) = matOf φ (e (B.length + t)) := by
      rw [hm]
      exact hw
    refine ⟨hr, hM, MatP_inv_of hM ?_⟩
    rw [← MatP_mul, ← mulS_eq, hi, MatP_oneS]

end CFSG.KC.Co1Sub

end
