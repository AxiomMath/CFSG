module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverForms
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Data.LawfulXor.Basic

public section

namespace CFSG.KC.LQT.Cov.Ge

open CFSG.QuasithinUnique.Ch1.TitsCover (reduceF insertF gePivots)

private def comb (piv : Array ℕ) (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if b n then piv[n]! else 0) ^^^ comb piv b n

private def Lead (piv : Array ℕ) : Prop :=
  ∀ k, piv[k]! ≠ 0 → Nat.log2 piv[k]! = k

private def InSpan (M : ℕ) (piv : Array ℕ) (x : ℕ) : Prop :=
  ∃ b : ℕ → Bool, comb piv b M = x

private theorem xor_xor_xor_comm (a b c d : ℕ) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

private theorem getElem!_eq_zero {piv : Array ℕ} {k : ℕ} (hk : piv.size ≤ k) : piv[k]! = 0 :=
  getElem!_neg piv k (Nat.not_lt.2 hk)

private theorem entry_lt {piv : Array ℕ} (h : Lead piv) (k : ℕ) : piv[k]! < 2 ^ (k + 1) := by
  by_cases h0 : piv[k]! = 0
  · rw [h0]
    exact Nat.two_pow_pos _
  · have := Nat.lt_log2_self (n := piv[k]!)
    rwa [h k h0] at this

private theorem sel_lt {piv : Array ℕ} (h : Lead piv) (b : Bool) (n : ℕ) :
    (if b then piv[n]! else 0) < 2 ^ (n + 1) := by
  split
  · exact entry_lt h n
  · exact Nat.two_pow_pos _

private theorem sel_xor (p : ℕ) (b c : Bool) :
    ((if b then p else 0) ^^^ (if c then p else 0)) = (if (b ^^ c) then p else 0) := by
  cases b <;> cases c <;> simp

private theorem comb_lt {piv : Array ℕ} (h : Lead piv) (b : ℕ → Bool) :
    ∀ n, comb piv b n < 2 ^ n
  | 0 => by simp [comb]
  | n + 1 => by
    simp only [comb]
    exact Nat.xor_lt_two_pow (sel_lt h _ n)
      ((comb_lt h b n).trans (Nat.pow_lt_pow_succ (by omega)))

private theorem comb_lead {piv : Array ℕ} (h : Lead piv) (b : ℕ → Bool) :
    ∀ n, comb piv b n ≠ 0 → piv[Nat.log2 (comb piv b n)]! ≠ 0
  | 0 => by simp [comb]
  | n + 1 => by
    simp only [comb]
    intro hne
    by_cases hb : b n = true
    · rw [if_pos hb] at hne ⊢
      by_cases hp : piv[n]! = 0
      · rw [hp, Nat.zero_xor] at hne ⊢
        exact comb_lead h b n hne
      · have hy := comb_lt h b n
        have ht := Nat.testBit_log2 hp
        rw [h n hp] at ht
        have hbit : (piv[n]! ^^^ comb piv b n).testBit n = true := by
          simp [Nat.testBit_xor, ht, Nat.testBit_lt_two_pow hy]
        have hge := Nat.ge_two_pow_of_testBit hbit
        have hx0 : piv[n]! ^^^ comb piv b n ≠ 0 := by
          have := Nat.two_pow_pos n
          omega
        have hlog : Nat.log2 (piv[n]! ^^^ comb piv b n) = n := by
          rw [Nat.log2_eq_iff hx0]
          exact ⟨hge, Nat.xor_lt_two_pow (entry_lt h n)
            (hy.trans (Nat.pow_lt_pow_succ (by omega)))⟩
        rw [hlog]
        exact hp
    · rw [if_neg hb, Nat.zero_xor] at hne ⊢
      exact comb_lead h b n hne

private theorem comb_xor (piv : Array ℕ) (b c : ℕ → Bool) :
    ∀ n, comb piv b n ^^^ comb piv c n = comb piv (fun k => b k ^^ c k) n
  | 0 => by simp [comb]
  | n + 1 => by
    simp only [comb]
    rw [xor_xor_xor_comm, sel_xor, comb_xor piv b c n]

private theorem comb_false (piv : Array ℕ) : ∀ n, comb piv (fun _ => false) n = 0
  | 0 => by simp only [comb]
  | n + 1 => by simp [comb, comb_false piv n]

private theorem comb_single (piv : Array ℕ) {k : ℕ} {b : ℕ → Bool}
    (hb : ∀ j, b j = true ↔ j = k) : ∀ n, comb piv b n = if k < n then piv[k]! else 0
  | 0 => by simp [comb]
  | n + 1 => by
    simp only [comb]
    rw [comb_single piv hb n]
    by_cases hnk : n = k
    · have h1 : b n = true := (hb n).2 hnk
      have h2 : ¬ k < n := by omega
      have h3 : k < n + 1 := by omega
      rw [if_pos h1, if_neg h2, if_pos h3, Nat.xor_zero, hnk]
    · have h1 : ¬ b n = true := fun h => hnk ((hb n).1 h)
      rw [if_neg h1, Nat.zero_xor]
      by_cases hkn : k < n
      · have h3 : k < n + 1 := by omega
        rw [if_pos hkn, if_pos h3]
      · have h3 : ¬ k < n + 1 := by omega
        rw [if_neg hkn, if_neg h3]

private theorem inSpan_zero (M : ℕ) (piv : Array ℕ) : InSpan M piv 0 :=
  ⟨fun _ => false, comb_false piv M⟩

private theorem inSpan_xor {M : ℕ} {piv : Array ℕ} {x y : ℕ} (hx : InSpan M piv x)
    (hy : InSpan M piv y) : InSpan M piv (x ^^^ y) := by
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨c, rfl⟩ := hy
  exact ⟨fun k => b k ^^ c k, (comb_xor piv b c M).symm⟩

private theorem inSpan_entry {M : ℕ} {piv : Array ℕ} (hM : piv.size = M) (k : ℕ) :
    InSpan M piv piv[k]! := by
  by_cases hk : k < M
  · refine ⟨fun j => decide (j = k), ?_⟩
    have hb : ∀ j, (fun j => decide (j = k)) j = true ↔ j = k := fun j => by simp
    rw [comb_single piv hb M, if_pos hk]
  · rw [getElem!_eq_zero (by omega)]
    exact inSpan_zero M piv

private theorem inSpan_lt {M : ℕ} {piv : Array ℕ} (h : Lead piv) {x : ℕ}
    (hx : InSpan M piv x) : x < 2 ^ M := by
  obtain ⟨b, rfl⟩ := hx
  exact comb_lt h b M

private theorem inSpan_lead {M : ℕ} {piv : Array ℕ} (h : Lead piv) {x : ℕ}
    (hx : InSpan M piv x) (hx0 : x ≠ 0) : piv[Nat.log2 x]! ≠ 0 := by
  obtain ⟨b, rfl⟩ := hx
  exact comb_lead h b M hx0

private theorem inSpan_comb {M : ℕ} {piv piv' : Array ℕ} (h : ∀ k : ℕ, InSpan M piv' piv[k]!)
    (b : ℕ → Bool) : ∀ n, InSpan M piv' (comb piv b n)
  | 0 => by
    simp only [comb]
    exact inSpan_zero M piv'
  | n + 1 => by
    simp only [comb]
    refine inSpan_xor ?_ (inSpan_comb h b n)
    split
    · exact h n
    · exact inSpan_zero M piv'

private theorem reduce_spec {M : ℕ} {piv : Array ℕ} (hM : piv.size = M) (h : Lead piv) :
    ∀ fuel x, x < 2 ^ fuel →
      InSpan M piv (reduceF piv fuel x ^^^ x) ∧
        (reduceF piv fuel x = 0 ∨ piv[Nat.log2 (reduceF piv fuel x)]! = 0)
  | 0, x, hx => by
    have hx0 : x = 0 := by simpa using hx
    have e : reduceF piv 0 x = x := by rw [reduceF]
    rw [e, Nat.xor_self]
    exact ⟨inSpan_zero M piv, Or.inl hx0⟩
  | fuel + 1, x, hx => by
    by_cases h0 : x = 0
    · have e : reduceF piv (fuel + 1) x = 0 := by rw [reduceF, if_pos h0]
      rw [e, Nat.zero_xor, h0]
      exact ⟨inSpan_zero M piv, Or.inl rfl⟩
    by_cases hp : piv[Nat.log2 x]! = 0
    · have e : reduceF piv (fuel + 1) x = x := by rw [reduceF, if_neg h0, if_pos hp]
      rw [e, Nat.xor_self]
      exact ⟨inSpan_zero M piv, Or.inr hp⟩
    have e : reduceF piv (fuel + 1) x = reduceF piv fuel (x ^^^ piv[Nat.log2 x]!) := by
      rw [reduceF, if_neg h0, if_neg hp]
    rw [e]
    have hn : Nat.log2 piv[Nat.log2 x]! = Nat.log2 x := h _ hp
    have hxn : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
    have hbit : (x ^^^ piv[Nat.log2 x]!).testBit (Nat.log2 x) = false := by
      have h1 := Nat.testBit_log2 h0
      have h2 := Nat.testBit_log2 hp
      rw [hn] at h2
      simp [Nat.testBit_xor, h1, h2]
    have hlow : x ^^^ piv[Nat.log2 x]! < 2 ^ Nat.log2 x := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rcases Nat.eq_or_lt_of_le hi with hi | hi
      · rw [← hi]
        exact hbit
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hxn (entry_lt h _))
          (Nat.pow_le_pow_right (by omega) hi))
    have hlog : Nat.log2 x < fuel + 1 := (Nat.log2_lt h0).2 hx
    obtain ⟨hs, hr⟩ := reduce_spec hM h fuel _
      (Nat.lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by omega) (by omega)))
    refine ⟨?_, hr⟩
    have := inSpan_xor hs (inSpan_entry hM (Nat.log2 x))
    rwa [Nat.xor_assoc, Nat.xor_xor_cancel_right] at this

private theorem reduceF_eq_zero {M fuel : ℕ} {piv : Array ℕ} (hM : piv.size = M) (h : Lead piv)
    (hMf : M ≤ fuel) {x : ℕ} (hx : InSpan M piv x) : reduceF piv fuel x = 0 := by
  obtain ⟨hs, hr⟩ := reduce_spec hM h fuel x
    (Nat.lt_of_lt_of_le (inSpan_lt h hx) (Nat.pow_le_pow_right (by omega) hMf))
  have hrs := inSpan_xor hs hx
  rw [Nat.xor_xor_cancel_right] at hrs
  rcases hr with hr | hr
  · exact hr
  · by_contra hne
    exact inSpan_lead h hrs hne hr

private theorem insertF_spec {M fuel : ℕ} {piv : Array ℕ} (hM : piv.size = M) (h : Lead piv)
    (hMf : M ≤ fuel) {f : ℕ} (hf : f < 2 ^ M) :
    (insertF fuel piv f).size = M ∧ Lead (insertF fuel piv f) ∧
      (∀ x, InSpan M piv x → InSpan M (insertF fuel piv f) x) ∧
        InSpan M (insertF fuel piv f) f := by
  obtain ⟨hs, hr⟩ := reduce_spec hM h fuel f
    (Nat.lt_of_lt_of_le hf (Nat.pow_le_pow_right (by omega) hMf))
  simp only [insertF]
  generalize reduceF piv fuel f = r at hs hr ⊢
  by_cases h0 : r = 0
  · rw [if_pos h0]
    rw [h0, Nat.zero_xor] at hs
    exact ⟨hM, h, fun _ hx => hx, hs⟩
  have hrlt : r < 2 ^ M := by
    have := Nat.xor_lt_two_pow (inSpan_lt h hs) hf
    rwa [Nat.xor_xor_cancel_right] at this
  have hlog : Nat.log2 r < piv.size := by
    rw [hM]
    exact (Nat.log2_lt h0).2 hrlt
  have hr0 : piv[Nat.log2 r]! = 0 := hr.resolve_left h0
  rw [if_neg h0, if_pos hlog]
  have hsize : (piv.set! (Nat.log2 r) r).size = M := by rw [Array.size_set!, hM]
  have hself : (piv.set! (Nat.log2 r) r)[Nat.log2 r]! = r := Array.getElem!_set!_self _ _ _ hlog
  have hne : ∀ k, Nat.log2 r ≠ k → (piv.set! (Nat.log2 r) r)[k]! = piv[k]! :=
    fun k hk => Array.getElem!_set!_ne _ _ _ _ hk
  have hlead : Lead (piv.set! (Nat.log2 r) r) := by
    intro k hk
    by_cases hkr : Nat.log2 r = k
    · subst hkr
      rw [hself]
    · rw [hne k hkr] at hk ⊢
      exact h k hk
  have hentry : ∀ k : ℕ, InSpan M (piv.set! (Nat.log2 r) r) piv[k]! := by
    intro k
    by_cases hkr : Nat.log2 r = k
    · rw [← hkr, hr0]
      exact inSpan_zero _ _
    · rw [← hne k hkr]
      exact inSpan_entry hsize k
  have hsub : ∀ x, InSpan M piv x → InSpan M (piv.set! (Nat.log2 r) r) x := by
    rintro x ⟨b, rfl⟩
    exact inSpan_comb hentry b M
  refine ⟨hsize, hlead, hsub, ?_⟩
  have hr' : InSpan M (piv.set! (Nat.log2 r) r) r := by
    have := inSpan_entry hsize (Nat.log2 r)
    rwa [hself] at this
  have := inSpan_xor hr' (hsub _ hs)
  rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this

private theorem foldl_spec {M fuel : ℕ} (hMf : M ≤ fuel) :
    ∀ (fs : List ℕ) (piv : Array ℕ), (∀ f ∈ fs, f < 2 ^ M) → piv.size = M → Lead piv →
      (fs.foldl (insertF fuel) piv).size = M ∧ Lead (fs.foldl (insertF fuel) piv) ∧
        (∀ x, InSpan M piv x → InSpan M (fs.foldl (insertF fuel) piv) x) ∧
          ∀ f ∈ fs, InSpan M (fs.foldl (insertF fuel) piv) f
  | [], piv, _, hM, h => ⟨hM, h, fun _ hx => hx, fun f hf => by simp at hf⟩
  | g :: fs, piv, hfs, hM, h => by
    obtain ⟨hM', h', hsub, hg⟩ := insertF_spec hM h hMf (hfs g (List.mem_cons_self ..))
    obtain ⟨hM'', h'', hsub', hspan⟩ := foldl_spec hMf fs (insertF fuel piv g)
      (fun f hf => hfs f (List.mem_cons_of_mem _ hf)) hM' h'
    rw [List.foldl_cons]
    refine ⟨hM'', h'', fun x hx => hsub' x (hsub x hx), ?_⟩
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hsub' _ hg
    · exact hspan f hf

private theorem lead_replicate (M : ℕ) : Lead (Array.replicate M 0) := by
  intro k hk
  exfalso
  apply hk
  by_cases hkM : k < M
  · simp [hkM]
  · simp [hkM]

theorem reduceF_gePivots_xor {fuel M : ℕ} {fs : List ℕ} (hfs : ∀ f ∈ fs, f < 2 ^ M)
    (hfuel : M + 1 ≤ fuel) (ks : List ℕ) :
    reduceF (gePivots fuel M fs) fuel (ks.foldr (fun k acc => fs.getD k 0 ^^^ acc) 0) = 0 := by
  have hMf : M ≤ fuel := by omega
  obtain ⟨hM, h, -, hspan⟩ := foldl_spec hMf fs (Array.replicate M 0) hfs Array.size_replicate
    (lead_replicate M)
  unfold gePivots
  have hget : ∀ k, InSpan M (fs.foldl (insertF fuel) (Array.replicate M 0)) (fs.getD k 0) := by
    intro k
    by_cases hk : k < fs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact hspan _ (List.getElem_mem hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      exact inSpan_zero _ _
  refine reduceF_eq_zero hM h hMf ?_
  induction ks with
  | nil => exact inSpan_zero _ _
  | cons k ks ih =>
    simp only [List.foldr_cons]
    exact inSpan_xor (hget k) ih

end CFSG.KC.LQT.Cov.Ge

end
