module

public import Certificates.Data.Kernel.Misc.MergeTP
public import CFSG.Certificates.Kernel.Misc.MergeTSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace CFSG.KC.MergeT

open CFSG.KC.Enum
open CFSG.KS (mask)
open CFSG.KC.YModel (lget)

def packLab (W : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => a + 2 ^ W * packLab W l

theorem packLab_add (W : Nat) (f g : Nat → Nat) : ∀ l : List Nat,
    packLab W (l.map f) + packLab W (l.map g) = packLab W (l.map fun a => f a + g a)
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, packLab]
    rw [← packLab_add W f g l]
    ring

theorem packLab_mul (W c : Nat) (f : Nat → Nat) : ∀ l : List Nat,
    packLab W (l.map f) * c = packLab W (l.map fun a => f a * c)
  | [] => by simp [packLab]
  | a :: l => by
    simp only [List.map_cons, packLab]
    rw [← packLab_mul W c f l]
    ring

theorem packLab_sub (W : Nat) (f g : Nat → Nat) (l : List Nat) (h : ∀ a ∈ l, g a ≤ f a) :
    packLab W (l.map f) - packLab W (l.map g) = packLab W (l.map fun a => f a - g a) := by
  have := packLab_add W (fun a => f a - g a) g l
  have e : (l.map fun a => f a - g a + g a) = l.map f :=
    List.map_congr_left (fun a ha => Nat.sub_add_cancel (h a ha))
  rw [e] at this
  omega

theorem packLab_div (W c : Nat) (hc : 0 < c) (f g : Nat → Nat) (l : List Nat)
    (h : ∀ a ∈ l, f a = g a * c) : packLab W (l.map f) / c = packLab W (l.map g) := by
  rw [List.map_congr_left h, ← packLab_mul, Nat.mul_div_cancel _ hc]

theorem testBit_split (W a x i : Nat) (ha : a < 2 ^ W) :
    (a + 2 ^ W * x).testBit i = if i < W then a.testBit i else x.testBit (i - W) := by
  rw [mul_comm, ← Nat.shiftLeft_eq, add_comm, Nat.shiftLeft_add_eq_or_of_lt ha, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hi : i < W
  · simp [hi]
  · have : a.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right two_pos (not_lt.1 hi)))
    simp [hi, this, not_lt.1 hi]

theorem land_split (W a b x y : Nat) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    (a + 2 ^ W * x) &&& (b + 2 ^ W * y) = (a &&& b) + 2 ^ W * (x &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_split W _ _ i (Nat.and_lt_two_pow _ hb), Nat.testBit_and, testBit_split W _ _ i ha,
    testBit_split W _ _ i hb, Nat.testBit_and, Nat.testBit_and]
  split_ifs <;> rfl

theorem xor_split (W a b x y : Nat) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    (a + 2 ^ W * x) ^^^ (b + 2 ^ W * y) = (a ^^^ b) + 2 ^ W * (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_split W _ _ i (Nat.xor_lt_two_pow ha hb), Nat.testBit_xor, testBit_split W _ _ i ha,
    testBit_split W _ _ i hb, Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

theorem packLab_land (W : Nat) (f g : Nat → Nat) : ∀ l : List Nat, (∀ a ∈ l, f a < 2 ^ W) →
    (∀ a ∈ l, g a < 2 ^ W) →
    packLab W (l.map f) &&& packLab W (l.map g) = packLab W (l.map fun a => f a &&& g a)
  | [], _, _ => by simp [packLab]
  | a :: l, hf, hg => by
    simp only [List.map_cons, packLab]
    rw [land_split W _ _ _ _ (hf a (by simp)) (hg a (by simp)),
      packLab_land W f g l (fun b hb => hf b (by simp [hb])) (fun b hb => hg b (by simp [hb]))]

theorem packLab_xor (W : Nat) (f g : Nat → Nat) : ∀ l : List Nat, (∀ a ∈ l, f a < 2 ^ W) →
    (∀ a ∈ l, g a < 2 ^ W) →
    packLab W (l.map f) ^^^ packLab W (l.map g) = packLab W (l.map fun a => f a ^^^ g a)
  | [], _, _ => by simp [packLab]
  | a :: l, hf, hg => by
    simp only [List.map_cons, packLab]
    rw [xor_split W _ _ _ _ (hf a (by simp)) (hg a (by simp)),
      packLab_xor W f g l (fun b hb => hf b (by simp [hb])) (fun b hb => hg b (by simp [hb]))]

theorem packLab_get (W : Nat) : ∀ (l : List Nat) (i : Nat), (∀ a ∈ l, a < 2 ^ W) →
    packLab W l / 2 ^ (W * i) % 2 ^ W = l.getD i 0
  | [], i, _ => by simp [packLab]
  | a :: l, 0, h => by
    simp only [packLab, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h a (by simp))]
  | a :: l, i + 1, h => by
    simp only [packLab, List.getD_cons_succ]
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (W * i)), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt (h a (by simp)), Nat.zero_add]
    exact packLab_get W l i (fun b hb => h b (by simp [hb]))

theorem packLab_append (W a : Nat) : ∀ l : List Nat,
    packLab W (l ++ [a]) = packLab W l + 2 ^ (W * l.length) * a
  | [] => by simp [packLab]
  | b :: l => by
    simp only [List.cons_append, packLab, packLab_append W a l, List.length_cons, Nat.mul_succ,
      Nat.pow_add]
    ring

theorem field_relabel {l lp lq : Nat} (hl : l < 2 ^ 14) (hp : lp < 2 ^ 14) (hq : lq < 2 ^ 14) :
    ((16384 - (((l ^^^ lq) + 16383) &&& 16384)) = (if l = lq then 1 else 0) * 16384) ∧
    l ^^^ ((l ^^^ lp) &&& ((if l = lq then 1 else 0) * 16383)) = (if l = lq then lp else l) := by
  by_cases h : l = lq
  · subst h
    simp only [Nat.xor_self, Nat.zero_add, ite_true, Nat.one_mul]
    refine ⟨by decide, ?_⟩
    have e : (16383 : Nat) = 2 ^ 14 - 1 := rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hl hp),
      ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · have hz : l ^^^ lq ≠ 0 := fun e => by
      apply h
      have h2 : l ^^^ (l ^^^ lq) = lq := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [e, Nat.xor_zero] at h2
      exact h2
    have hz2 : l ^^^ lq < 2 ^ 14 := Nat.xor_lt_two_pow hl hq
    have ht : ((l ^^^ lq) + 16383) &&& 16384 = 16384 := by
      have p14 : (2 : Nat) ^ 14 = 16384 := rfl
      generalize l ^^^ lq = z at hz hz2 ⊢
      have e1 : z + 16383 = (z - 1) + 2 ^ 14 * 1 := by omega
      have e2 : (16384 : Nat) = 0 + 2 ^ 14 * 1 := rfl
      rw [e1, e2, land_split 14 _ _ _ _ (by omega) (by omega), Nat.and_zero]
      rfl
    simp only [ht, h, ite_false, Nat.zero_mul, Nat.sub_self, Nat.and_zero, Nat.xor_zero, and_self]

theorem relabel_pack (l : List Nat) (hl : ∀ a ∈ l, a < 2 ^ 14) {lp lq : Nat} (hp : lp < 2 ^ 14)
    (hq : lq < 2 ^ 14) :
    packLab 15 l ^^^ ((packLab 15 l ^^^ packLab 15 (l.map fun _ => lp)) &&&
      (((packLab 15 (l.map fun _ => 16384) - (((packLab 15 l ^^^ packLab 15 (l.map fun _ => lq)) +
        packLab 15 (l.map fun _ => 16383)) &&& packLab 15 (l.map fun _ => 16384))) / 16384) * 16383)) =
    packLab 15 (l.map fun a => if a = lq then lp else a) := by
  have h15 : ∀ a ∈ l, a < 2 ^ 15 := fun a ha => by have := hl a ha; omega
  have hP : packLab 15 l = packLab 15 (l.map fun a => a) := by rw [List.map_id']
  have c15 : ∀ c, c < 2 ^ 15 → ∀ a ∈ l, (fun _ => c) a < 2 ^ 15 := fun c hc _ _ => hc
  rw [hP, packLab_xor 15 _ _ l h15 (c15 lq (by omega)), packLab_add,
    packLab_land 15 _ _ l (fun a ha => by have := hl a ha; have := Nat.xor_lt_two_pow this hq; simp; omega)
      (c15 16384 (by norm_num)),
    packLab_sub 15 _ _ l (fun a _ => Nat.and_le_right),
    packLab_div 15 16384 (by norm_num) _ (fun a => if a = lq then 1 else 0) l
      (fun a ha => (field_relabel (hl a ha) hp hq).1),
    packLab_mul, packLab_xor 15 _ _ l h15 (c15 lp (by omega)),
    packLab_land 15 _ _ l (fun a ha => by have := Nat.xor_lt_two_pow (hl a ha) hp; simp; omega)
      (fun a _ => by split_ifs <;> simp),
    packLab_xor 15 _ _ l h15 (fun a _ => Nat.and_lt_two_pow _ (by split_ifs <;> simp))]
  exact congrArg (packLab 15) (List.map_congr_left fun a ha => (field_relabel (hl a ha) hp hq).2)

theorem onesP_eq : ∀ n : Nat, onesP n = packLab 15 (List.replicate n 1)
  | 0 => rfl
  | n + 1 => by
    change Nat.add 1 (Nat.shiftLeft (onesP n) 15) = _
    rw [onesP_eq n, List.replicate_succ, packLab]
    change 1 + packLab 15 (List.replicate n 1) <<< 15 = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem const_eq {l : List Nat} {n : Nat} (hl : l.length = n) (c : Nat) :
    Nat.mul c (onesP n) = packLab 15 (l.map fun _ => c) := by
  change c * onesP n = _
  rw [Nat.mul_comm, onesP_eq, ← hl, ← List.map_const', packLab_mul]
  simp

theorem pg15_eq (l : List Nat) (hl : ∀ a ∈ l, a < 2 ^ 15) (i : Nat) :
    pg 15 (mask 15) (packLab 15 l) i = lget l i := by
  change Nat.land (Nat.shiftRight (packLab 15 l) (15 * i)) (Nat.sub (1 <<< 15) 1) = _
  rw [Nat.shiftLeft_eq, one_mul]
  change (packLab 15 l >>> (15 * i)) &&& (2 ^ 15 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, packLab_get 15 l i hl, lget_eq]

theorem lget_lt {l : List Nat} {B : Nat} (hl : ∀ a ∈ l, a < B) (hB : 0 < B) (i : Nat) :
    lget l i < B := by
  rw [lget_eq, List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simpa using hB
  | some a => simpa using hl a (List.mem_of_getElem? h)

theorem relabelP_eq {l : List Nat} {n : Nat} (hlen : l.length = n) (hl : ∀ a ∈ l, a < 2 ^ 14)
    {lp lq : Nat} (hp : lp < 2 ^ 14) (hq : lq < 2 ^ 14) :
    relabelP (onesP n) (packLab 15 l) lp lq = packLab 15 (l.map fun a => if a = lq then lp else a) := by
  unfold relabelP
  rw [const_eq hlen, const_eq hlen, const_eq hlen, const_eq hlen]
  exact relabel_pack l hl hp hq

theorem initP_eq (b x : Nat) : ∀ n : Nat, initP n b x = packLab 15 (initL n b x)
  | 0 => rfl
  | n + 1 => by
    change Nat.add (initP n b x) (Nat.shiftLeft (nIf(Nat.beq n x, b, n)) (Nat.mul 15 n)) = _
    rw [initP_eq b x n]
    unfold initL
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, packLab_append,
      List.length_map, List.length_range]
    change _ + _ <<< (15 * n) = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm (2 ^ (15 * n))]

def RelP (n : Nat) (s : Bool × List Nat) (p : Bool × Nat) : Prop :=
  s.1 = p.1 ∧ (s.1 = true → p.2 = packLab 15 s.2 ∧ s.2.length = n ∧ ∀ a ∈ s.2, a < 2 ^ 14)

theorem relP_step {n w kG : Nat} {GP : Nat → Nat} {s : Bool × List Nat} {p : Bool × Nat}
    (hr : RelP n s p) (t : Nat × Nat × Nat) :
    RelP n (mergeStepK n w GP kG s t) (mergeStepP n w GP kG (onesP n) p t) := by
  obtain ⟨h1, h2⟩ := hr
  obtain ⟨i, u, v⟩ := t
  cases hs : s.1
  · rw [hs] at h1
    refine ⟨?_, fun h => ?_⟩
    · unfold mergeStepK mergeStepP
      dsimp only
      rw [hs, ← h1]
    · unfold mergeStepK at h
      dsimp only at h
      rw [hs] at h
      exact absurd h Bool.false_ne_true
  · obtain ⟨hP, hlen, hb⟩ := h2 hs
    rw [hs] at h1
    have h15 : ∀ a ∈ s.2, a < 2 ^ 15 := fun a ha => by have := hb a ha; omega
    have hg : ∀ k, pg 15 (mask 15) p.2 k = lget s.2 k := fun k => by rw [hP, pg15_eq _ h15]
    have hlt : ∀ k, lget s.2 k < 2 ^ 14 := lget_lt hb (by norm_num)
    unfold mergeStepK mergeStepP relabelL
    dsimp only
    simp only [hg, ← h1, hs, strictL_eq, mapE_eq]
    refine ⟨rfl, fun _ => ⟨?_, by simp [hlen], ?_⟩⟩
    · rw [hP, relabelP_eq hlen hb (hlt _) (hlt _)]
      dsimp only
      congr 1
      apply List.map_congr_left
      intro a _
      rw [CFSG.KS.Raw.Orb.nIf_eq]
      simp
    · intro a ha
      rw [List.mem_map] at ha
      obtain ⟨c, hc, rfl⟩ := ha
      rw [CFSG.KS.Raw.Orb.nIf_eq]
      split
      · exact hlt _
      · exact hb c hc

theorem relP_fold {n w kG : Nat} {GP : Nat → Nat} : ∀ (L : List (Nat × Nat × Nat))
    {s : Bool × List Nat} {p : Bool × Nat}, RelP n s p →
    RelP n (L.foldl (mergeStepK n w GP kG) s) (L.foldl (mergeStepP n w GP kG (onesP n)) p)
  | [], _, _, hr => hr
  | t :: L, _, _, hr => relP_fold L (relP_step hr t)

theorem relP_init {n b x : Nat} (hn : n ≤ 2 ^ 14) (hb : b < n) :
    RelP n (true, initL n b x) (true, initP n b x) := by
  refine ⟨rfl, fun _ => ⟨initP_eq b x n, by simp [initL], fun a ha => ?_⟩⟩
  simp only [initL, List.mem_map, List.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [CFSG.KS.Raw.Orb.nIf_eq]
  split <;> omega

theorem mergeTK_of_mergeTP {n w kG b x : Nat} {GP : Nat → Nat} {L : List (Nat × Nat × Nat)}
    {ts : List Nat} (hn : n ≤ 2 ^ 14) (h : mergeTP n w GP kG b x L ts = true) :
    mergeTK n w GP kG b x L ts = true := by
  unfold mergeTP at h
  unfold mergeTK
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h ⊢
  obtain ⟨hb, hx, hf, ht⟩ := h
  obtain ⟨r1, r2⟩ := relP_fold (w := w) (GP := GP) (kG := kG) L (relP_init (x := x) hn hb)
  have hf' : (L.foldl (mergeStepK n w GP kG) (true, initL n b x)).1 = true := r1.trans hf
  obtain ⟨hP, -, hB⟩ := r2 hf'
  have h15 : ∀ a ∈ (L.foldl (mergeStepK n w GP kG) (true, initL n b x)).2, a < 2 ^ 15 :=
    fun a ha => by have := hB a ha; omega
  refine ⟨hb, hx, hf', ?_⟩
  rw [List.all_eq_true] at ht ⊢
  intro t htm
  have e := ht t htm
  simp only [Bool.and_eq_true, Nat.blt_eq] at e ⊢
  rw [hP, pg15_eq _ h15, pg15_eq _ h15] at e
  exact e

end CFSG.KC.MergeT

end
