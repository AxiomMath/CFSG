module

public import Certificates.Data.Antiflag
public import Certificates.Data.Kernel.Antiflag.Kit
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KC.Antiflag

open Certificates.Antiflag CFSG.KD.Antiflag

@[expose] def bz (b : Bool) : ZMod 2 := if b then 1 else 0

@[expose] def decV (n c : ℕ) : Fin n → ZMod 2 := fun k => bz (c.testBit k)

@[expose] def dec (n c : ℕ) : Pt n := (decV n c, decV n (c >>> n))

theorem bz_xor (a b : Bool) : bz (xor a b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_and (a b : Bool) : bz (a && b) = bz a * bz b := by
  cases a <;> cases b <;> decide

theorem bz_eq_one {b : Bool} (h : bz b = 1) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

theorem testBit_cond (b : Bool) (i k : ℕ) :
    (bif b then 2 ^ i else 0).testBit k = (b && decide (i = k)) := by
  cases b <;> simp [Nat.testBit_two_pow]

theorem dec_swN (n c : ℕ) : dec n (swN n c) = sw (dec n c) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · have hk : ¬ n ≤ (k : ℕ) := by omega
    simp [dec, decV, swN, sw, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, k.isLt, hk]
  · have hk := k.isLt
    simp [dec, decV, swN, sw, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, hk]

theorem dec_tvN (n : ℕ) (i j : Fin n) (c : ℕ) : dec n (tvN n i j c) = tv i j (dec n c) := by
  have hi := i.isLt
  have hj := j.isLt
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · have hk := k.isLt
    have h1 : ¬ n + (j : ℕ) = k := by omega
    simp only [dec, decV, tvN, tv, Pi.add_apply, Pi.single_apply, Nat.testBit_xor, testBit_cond,
      decide_eq_false h1, Bool.and_false, Bool.xor_false, bz_xor, bz_and]
    by_cases h : k = i
    · subst h
      simp [bz]
    · have h' : ¬ (i : ℕ) = k := fun e => h (Fin.ext e.symm)
      simp [h, h', bz]
  · have hk := k.isLt
    have h1 : ¬ (i : ℕ) = n + k := by omega
    simp only [dec, decV, tvN, tv, Pi.add_apply, Pi.single_apply, Nat.testBit_shiftRight,
      Nat.testBit_xor, testBit_cond, decide_eq_false h1, Bool.and_false, Bool.xor_false, bz_xor,
      bz_and]
    by_cases h : k = j
    · subst h
      simp [bz]
    · have h' : ¬ n + (j : ℕ) = n + k := fun e => h (Fin.ext (by omega))
      have h'' : ¬ (j : ℕ) = k := fun e => h (Fin.ext e.symm)
      simp [h, h', h'', bz]

@[expose] def Rel (n : ℕ) (f : Pt n → Pt n) (g : ℕ → ℕ) : Prop := ∀ c, dec n (g c) = f (dec n c)

theorem f2_map {α : Type} {n : ℕ} (L : List α) (f : α → Pt n → Pt n) (g : α → ℕ → ℕ)
    (h : ∀ x ∈ L, Rel n (f x) (g x)) : List.Forall₂ (Rel n) (L.map f) (L.map g) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons a L ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem f2_append {n : ℕ} {A C : List (Pt n → Pt n)} {B D : List (ℕ → ℕ)}
    (h1 : List.Forall₂ (Rel n) A B) (h2 : List.Forall₂ (Rel n) C D) :
    List.Forall₂ (Rel n) (A ++ C) (B ++ D) := by
  induction h1 with
  | nil => simpa using h2
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem f2_flatMap {α : Type} {n : ℕ} (L : List α) (F : α → List (Pt n → Pt n))
    (G : α → List (ℕ → ℕ)) (h : ∀ x ∈ L, List.Forall₂ (Rel n) (F x) (G x)) :
    List.Forall₂ (Rel n) (L.flatMap F) (L.flatMap G) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons a L ih =>
    simp only [List.flatMap_cons]
    exact f2_append (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem f2_getD {n : ℕ} {A : List (Pt n → Pt n)} {B : List (ℕ → ℕ)}
    (h : List.Forall₂ (Rel n) A B) (i : ℕ) : Rel n (A.getD i id) (B.getD i id) := by
  induction h generalizing i with
  | nil => exact fun c => rfl
  | cons hab _ ih =>
    cases i with
    | zero => exact hab
    | succ i => exact ih i

theorem rel_gGN (n : ℕ) : List.Forall₂ (Rel n) (globalGens n) (gGN n) := by
  simp only [globalGens, gGN, gDN, List.map_cons, List.map_flatMap, List.map_map]
  refine List.Forall₂.cons (dec_swN n) ?_
  exact f2_flatMap _ _ _ fun i _ => f2_map _ _ _ fun j _ => dec_tvN n i j

theorem rel_gSN (n : ℕ) : List.Forall₂ (Rel n) (stabGens n) (gSN n) := by
  simp only [stabGens, gSN, sDN, List.map_cons, List.map_flatMap, List.map_map]
  refine List.Forall₂.cons (dec_swN n) ?_
  exact f2_flatMap _ _ _ fun i _ => f2_map _ _ _ fun j _ => dec_tvN n i j

theorem runCode_succ (gs : List (ℕ → ℕ)) (f w c : ℕ) :
    runCode gs (f + 1) w c =
      bif w == 0 then c else gs.getD ((w &&& 31) - 1) id (runCode gs f (w >>> 5) c) := rfl

theorem decodeW_succ (f w : ℕ) :
    decodeW (f + 1) w = bif w == 0 then [] else ((w &&& 31) - 1) :: decodeW f (w >>> 5) := rfl

theorem dec_runCode {n : ℕ} {A : List (Pt n → Pt n)} {B : List (ℕ → ℕ)}
    (h : List.Forall₂ (Rel n) A B) (fuel w c : ℕ) :
    dec n (runCode B fuel w c) = applyWord A (decodeW fuel w) (dec n c) := by
  induction fuel generalizing w with
  | zero => rfl
  | succ f ih =>
    rw [runCode_succ, decodeW_succ]
    cases hw : (w == 0)
    · simp only [cond_false]
      rw [f2_getD h, ih]
      rfl
    · rfl

theorem allLt_spec {m : ℕ} {f : ℕ → Bool} (h : allLt m f = true) : ∀ k < m, f k = true := by
  induction m with
  | zero => intro k hk; omega
  | succ m ih =>
    have h' : (allLt m f && f m) = true := h
    rw [Bool.and_eq_true] at h'
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h'.1 k hk
    · exact h'.2

theorem sum_dotAux (n c m : ℕ) :
    (∑ k : Fin m, bz (c.testBit k) * bz (c.testBit (n + k))) = bz (dotAux n c m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, ih]
    change _ = bz (xor (dotAux n c m) (c.testBit m && c.testBit (n + m)))
    rw [bz_xor, bz_and]

theorem dot_dec (n c : ℕ) : (dec n c).1 ⬝ᵥ (dec n c).2 = bz (dotB n c) := by
  simp only [dec, decV, dotProduct, Nat.testBit_shiftRight]
  exact sum_dotAux n c n

theorem exists_bits (v : ℕ → ZMod 2) :
    ∀ m, ∃ a < 2 ^ m, ∀ k < m, bz (a.testBit k) = v k := by
  intro m
  induction m with
  | zero => exact ⟨0, by norm_num, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ m ih =>
    obtain ⟨a, ha, hv⟩ := ih
    refine ⟨a ||| (bif decide (v m = 1) then 2 ^ m else 0), ?_, fun k hk => ?_⟩
    · refine Nat.or_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
        ?_
      cases decide (v m = 1)
      · exact Nat.two_pow_pos _
      · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · rw [Nat.testBit_or, testBit_cond]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · have : ¬ m = k := by omega
        simp [this, hv k hk]
      · rw [hk, Nat.testBit_lt_two_pow ha]
        have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        rcases h2 (v m) with h | h <;> simp [h, bz] <;> decide

theorem exists_vec (n : ℕ) (v : Fin n → ZMod 2) : ∃ a < 2 ^ n, decV n a = v := by
  obtain ⟨a, ha, hv⟩ := exists_bits (fun k => if h : k < n then v ⟨k, h⟩ else 0) n
  refine ⟨a, ha, funext fun k => ?_⟩
  simpa [decV, k.isLt] using hv k k.isLt

theorem exists_code (n : ℕ) (ω : Pt n) : ∃ c < 4 ^ n, dec n c = ω := by
  obtain ⟨a, ha, hx⟩ := exists_vec n ω.1
  obtain ⟨b, hb, hy⟩ := exists_vec n ω.2
  refine ⟨a ||| (b <<< n), ?_, Prod.ext ?_ ?_⟩
  · have h4 : (4 : ℕ) ^ n = 2 ^ (n + n) := by rw [← two_mul, pow_mul]; norm_num
    rw [h4]
    refine Nat.or_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))) ?_
    rw [Nat.shiftLeft_eq, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hb (by positivity)
  · rw [← hx]
    funext k
    have hk : ¬ n ≤ (k : ℕ) := by omega
    simp [dec, decV, Nat.testBit_or, Nat.testBit_shiftLeft, hk]
  · rw [← hy]
    funext k
    have hz : a.testBit (n + k) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [dec, decV, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hz]

theorem dotB_of_mem {n c : ℕ} (h : dec n c ∈ antiflags n) : dotB n c = true := by
  simp only [antiflags, Finset.mem_filter, Finset.mem_univ, true_and, dot_dec] at h
  exact bz_eq_one h

theorem mem_of_dotB {n c : ℕ} (h : dotB n c = true) : dec n c ∈ antiflags n := by
  simp only [antiflags, Finset.mem_filter, Finset.mem_univ, true_and, dot_dec, h]
  rfl

theorem run_of_chk {n : ℕ} {f : ℕ → Bool} (h : allLt (4 ^ n) f = true) {c : ℕ} (hc : c < 4 ^ n) :
    f c = true := allLt_spec h c hc

theorem facts_of_check (n tG tS : ℕ) (tT : ℕ → ℕ)
    (hreps : (List.range 4).map (fun s => dec n (repN n s)) = reps n)
    (hrepLt : ∀ s < 4, repN n s < 4 ^ n) (hbase : dec n (baseN n) = base n)
    (hdot : ∀ s < 4, dotB n (repN n s) = true) (hG : chkG n tG = true) (hS : chkS n tS = true)
    (hT : ∀ s < 4, chkT n tG s (tT s) = true) : Facts n := by
  have h1 : ∀ r ∈ reps n, r ∈ antiflags n := by
    intro r hr
    rw [← hreps] at hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact mem_of_dotB (hdot s (List.mem_range.1 hs))
  have gG : ∀ c < 4 ^ n, dec n c ∈ antiflags n →
      applyWord (globalGens n) (decodeW fuelW (lane tG c)) (base n) = dec n c := by
    intro c hc hm
    have := run_of_chk hG hc
    simp only [dotB_of_mem hm, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    rw [← hbase, ← dec_runCode (rel_gGN n), this]
  refine ⟨h1, fun ω hω => ?_, fun ω hω hne => ?_, fun r hr => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := exists_code n ω
    exact ⟨_, gG c hc hω⟩
  · obtain ⟨c, hc, rfl⟩ := exists_code n ω
    have := run_of_chk hS hc
    have hcb : (c == baseN n) = false := by
      rw [beq_eq_false_iff_ne]
      rintro rfl
      exact hne hbase
    simp only [dotB_of_mem hω, Bool.not_true, Bool.false_or, hcb, beq_iff_eq] at this
    have hs : (lane tS c &&& 3) < 4 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
    refine ⟨dec n (repN n (lane tS c &&& 3)), ?_, decodeW fuelW (lane tS c >>> 2), ?_⟩
    · rw [← hreps]
      exact List.mem_map.2 ⟨_, List.mem_range.2 hs, rfl⟩
    · rw [← dec_runCode (rel_gSN n), this]
  · rw [← hreps] at hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs := List.mem_range.1 hs
    have hrA : dec n (repN n s) ∈ antiflags n :=
      h1 _ (by rw [← hreps]; exact List.mem_map.2 ⟨s, List.mem_range.2 hs, rfl⟩)
    refine ⟨decodeW fuelW (lane tG (repN n s)), gG _ (hrepLt s hs) hrA, fun ω hω => ?_⟩
    obtain ⟨c, hc, rfl⟩ := exists_code n ω
    have := run_of_chk (hT s hs) hc
    simp only [dotB_of_mem hω, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    have hrel : List.Forall₂ (Rel n) (stabGens n ++ [applyWord (globalGens n)
        (decodeW fuelW (lane tG (repN n s)))]) (gTN n tG s) :=
      f2_append (rel_gSN n) (List.Forall₂.cons (fun c => dec_runCode (rel_gGN n) _ _ c)
        List.Forall₂.nil)
    exact ⟨decodeW fuelW (lane (tT s) c), by rw [← hbase, ← dec_runCode hrel, this]⟩

end CFSG.KC.Antiflag
