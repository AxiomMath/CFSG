module

public import Certificates.Data.Kernel.U20K
public import CFSG.Certificates.Kernel.MonsterB.GaussInvSound
public import CFSG.Certificates.Kernel.Co1BMulSound

public section

namespace CFSG.KC.U20

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W
open CFSG.Monster.B.TwoA.Unitary

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => getL_eq x L i

theorem size_unpackR (d M : Nat) : (unpackR d M).size = d := by simp [unpackR]

theorem getElem!_unpackR {d M i : Nat} (hi : i < d) : (unpackR d M)[i]! = M / 2 ^ (d * i) % 2 ^ d := by
  simp [unpackR, hi]

theorem actGoR_eq (B : Array ℕ) (c : ℕ) : ∀ n, actGoR B c n =
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if c.testBit k then B[k]! ^^^ acc else acc) n
  | 0 => rfl
  | n + 1 => by
    rw [actGoR, actGoR_eq B c n]
    change _ = if c.testBit n then _ else _
    cases c.testBit n
    · simp
    · simp [Nat.xor_comm]

theorem getD_getElem? (B : Array ℕ) (j : ℕ) : B[j]?.getD 0 = B[j]! := by
  by_cases h : j < B.size
  · simp [h]
  · simp [h]

theorem actR_eq (B : Array ℕ) (c : ℕ) : actR B c = CFSG.Sporadic.SmallF2.Native.vecMulN 20 B c := by
  rw [actR, actGoR_eq, CFSG.Sporadic.SmallF2.Native.vecMulN,
    foldl_range_xor (fun j => B[j]!) (fun j => B[j]?.getD 0) c.testBit 20 fun j _ => getD_getElem? B j]

theorem rowsMul_eq {A : Array ℕ} (hA : A.size = 20) (B : Array ℕ) :
    rowsMul A B = CFSG.Sporadic.SmallF2.Native.mulRows 20 A B := by
  apply Array.ext
  · simp [rowsMul, CFSG.Sporadic.SmallF2.Native.mulRows, hA]
  · intro i h1 h2
    have hi : i < A.size := by simpa [CFSG.Sporadic.SmallF2.Native.mulRows] using h2
    simp only [rowsMul, CFSG.Sporadic.SmallF2.Native.mulRows, List.getElem_toArray, List.getElem_map,
      List.getElem_range, Array.getElem_map, actR_eq]
    rw [getElem!_pos A i hi]

theorem idRows_eq : CFSG.Monster.B.TwoA.Unitary.idRows = unpackR 20 (idF 20) := by
  apply Array.ext
  · simp [CFSG.Monster.B.TwoA.Unitary.idRows, size_unpackR]
  · intro i h1 h2
    have hi : i < 20 := by simpa [size_unpackR] using h2
    have hf : ∀ j < 20, pw2 j < 2 ^ 20 := fun j hj => by
      rw [pw2_eq]
      exact Nat.pow_lt_pow_right (by omega) hj
    have h : rowF 20 (idF 20) i = pw2 i := rowF_orN 20 (f := pw2) hf hi
    rw [rowF_eq, pw2_eq] at h
    simp only [CFSG.Monster.B.TwoA.Unitary.idRows, List.getElem_toArray, List.getElem_map,
      List.getElem_range, unpackR, Array.getElem_ofFn]
    rw [h, Nat.one_shiftLeft]

theorem gensK_sound : ∀ {G : List Nat} {L : List (Array Nat)}, gensK G L = true →
    List.Forall₂ (fun g r => r = unpackR 20 g) G L
  | [], [], _ => .nil
  | [], _ :: _, h => absurd h (by simp [gensK])
  | _ :: _, [], h => absurd h (by simp [gensK])
  | g :: G, r :: L, h => by
    have h' : andB (packB 20 r.toList g) (gensK G L) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    refine .cons ?_ (gensK_sound h2)
    rw [← packB_sound h1, Array.toArray_toList]

theorem flatK_sound : ∀ {F : List Nat} {L : List (Array Nat)}, flatK F L = true →
    List.Forall₂ (fun f r => f < 2 ^ 400 ∧ r = unpackR 20 f) F L
  | [], [], _ => .nil
  | [], _ :: _, h => absurd h (by simp [flatK])
  | _ :: _, [], h => absurd h (by simp [flatK])
  | f :: F, r :: L, h => by
    have h' : andB (andB (Nat.blt f (pw2 400)) (packB 20 r.toList f)) (flatK F L) = true := h
    obtain ⟨h0, h2⟩ := andB_true h'
    obtain ⟨h1, h3⟩ := andB_true h0
    refine .cons ⟨?_, ?_⟩ (flatK_sound h2)
    · rw [pw2_eq] at h1
      exact Nat.blt_eq.mp h1
    · rw [← packB_sound h3, Array.toArray_toList]

theorem lettersK_sound : ∀ {w : List Nat}, lettersK w = true → ∀ k ∈ w, k < 17
  | [], _ => by simp
  | k :: w, h => by
    have h' : andB (Nat.blt k 17) (lettersK w) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.blt_eq.mp h1
    · exact lettersK_sound h2 x hx

theorem wordsK_sound {G : List Nat} : ∀ {F : List Nat} {W : List (List Nat)}, wordsK G F W = true →
    List.Forall₂ (fun w f => (∀ k ∈ w, k < 17) ∧ wordK G w = f) W F
  | [], [], _ => .nil
  | _ :: _, [], h => absurd h (by simp [wordsK])
  | [], _ :: _, h => absurd h (by simp [wordsK])
  | f :: F, w :: W, h => by
    have h' : andB (andB (lettersK w) (Nat.beq (wordK G w) f)) (wordsK G F W) = true := h
    obtain ⟨h0, h2⟩ := andB_true h'
    obtain ⟨h1, h3⟩ := andB_true h0
    exact .cons ⟨lettersK_sound h1, Nat.eq_of_beq_eq_true h3⟩ (wordsK_sound h2)

theorem wordRows_eq {G : List Nat} (hG : List.Forall₂ (fun g r => r = unpackR 20 g) G u20Gens.toList) :
    ∀ w : List Nat, (∀ k ∈ w, k < 17) → wordRows w = unpackR 20 (wordK G w)
  | [], _ => by
    rw [wordRows, idRows_eq]
    rfl
  | k :: w, hw => by
    have hk : k < 17 := hw k (by simp)
    have hlen : u20Gens.toList.length = 17 := rfl
    have hkG : k < G.length := by rw [hG.length_eq, hlen]; exact hk
    have hkL : k < u20Gens.toList.length := by rw [hlen]; exact hk
    have hg : u20Gens[k]! = unpackR 20 (getL 0 G k) := by
      rw [getL_eq, List.getElem?_eq_getElem hkG, Option.getD_some]
      have := hG.get hkG hkL
      simp only [List.get_eq_getElem, Array.getElem_toList] at this
      rw [← this]
      exact getElem!_pos u20Gens k (by simpa using hkL)
    rw [wordRows, hg, wordRows_eq hG w fun x hx => hw x (by simp [hx]),
      rowsMul_eq (size_unpackR 20 _), mulRows_unpackR]
    rfl

theorem flatRows_go (P : ℕ) : ∀ n, (List.range n).foldl
    (fun acc i => acc ||| ((unpackR 20 P)[i]! <<< (20 * i))) 0 = P % 2 ^ (20 * min n 20)
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, flatRows_go P n]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hn : n < 20
    · rw [getElem!_unpackR hn, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
      have hlt : P % 2 ^ (20 * n) < 2 ^ (20 * n) := Nat.mod_lt _ (by positivity)
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq,
        show 20 * (n + 1) = 20 * n + 20 by ring, Nat.pow_add, Nat.mod_mul]
      ring
    · have h20 : (unpackR 20 P)[n]! = 0 := by
        simp [unpackR, hn]
      rw [h20, Nat.zero_shiftLeft, Nat.or_zero, Nat.min_eq_right (by omega),
        Nat.min_eq_right (by omega)]

theorem flatRows_unpackR {P : ℕ} (hP : P < 2 ^ 400) : flatRows (unpackR 20 P) = P := by
  have h : 20 * min 20 20 = 400 := rfl
  rw [flatRows, flatRows_go, h]
  exact Nat.mod_eq_of_lt hP

theorem rowsXor_unpackR (X Y : ℕ) : rowsXor (unpackR 20 X) (unpackR 20 Y) = unpackR 20 (X ^^^ Y) := by
  apply Array.ext
  · simp [rowsXor, size_unpackR]
  · intro i h1 h2
    have hi : i < 20 := by simpa [size_unpackR] using h2
    simp only [rowsXor, List.getElem_toArray, List.getElem_map, List.getElem_range]
    rw [getElem!_unpackR hi, getElem!_unpackR hi]
    simp only [unpackR, Array.getElem_ofFn]
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

theorem zeroRows_eq : zeroRows = unpackR 20 0 := by
  apply Array.ext
  · simp [zeroRows, size_unpackR]
  · intro i h1 h2
    simp only [zeroRows, List.getElem_toArray, List.getElem_map, unpackR, Array.getElem_ofFn]
    simp

theorem combRows_go {rows : Array ℕ}
    (hR : ∀ j < 400, u20RecRows[j]! = unpackR 20 rows[j]!) (s : ℕ) : ∀ n ≤ 400,
    (List.range n).foldl (fun acc j => if s.testBit j then rowsXor acc u20RecRows[j]! else acc)
      zeroRows = unpackR 20 ((List.range n).foldl
        (fun acc j => if s.testBit j then acc ^^^ rows[j]! else acc) 0)
  | 0, _ => by simp [zeroRows_eq]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_append, combRows_go hR s n (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    split
    · rw [hR n (by omega), rowsXor_unpackR]
    · rfl

theorem combRows_eq {rows : Array ℕ} (hR : ∀ j < 400, u20RecRows[j]! = unpackR 20 rows[j]!)
    (s : ℕ) : combRows s = unpackR 20 (selXor 400 rows s) :=
  combRows_go hR s 400 le_rfl

theorem eRows_eq {c : ℕ} (hc : c < 400) : eRows c = unpackR 20 (2 ^ c) := by
  apply Array.ext
  · simp [eRows, size_unpackR]
  · intro i h1 h2
    have hi : i < 20 := by simpa [size_unpackR] using h2
    simp only [eRows, List.getElem_toArray, List.getElem_map, List.getElem_range, unpackR,
      Array.getElem_ofFn]
    split
    · rename_i h
      have hp : (2 : ℕ) ^ c = 2 ^ (20 * i) * 2 ^ (c % 20) := by
        rw [← Nat.pow_add, h, Nat.div_add_mod]
      have hm : (2 : ℕ) ^ (c % 20) < 2 ^ 20 := Nat.pow_lt_pow_right (by omega) (Nat.mod_lt _ (by omega))
      rw [hp, Nat.mul_div_cancel_left _ (by positivity), Nat.mod_eq_of_lt hm, Nat.one_shiftLeft]
    · rename_i h
      by_cases hlt : c < 20 * i
      · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlt), Nat.zero_mod]
      · have hk : c = 20 * i + 20 + (c - (20 * i + 20)) := by omega
        have hp : (2 : ℕ) ^ c = 2 ^ (20 * i) * (2 ^ 20 * 2 ^ (c - (20 * i + 20))) := by
          rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.add_assoc, ← hk]
        rw [hp, Nat.mul_div_cancel_left _ (by positivity), Nat.mul_mod_right]

theorem selFrom_eq (s : ℕ) : ∀ (F : List ℕ) (i : ℕ), selFrom s F i =
    (List.range F.length).foldl (fun acc j => if s.testBit (i + j) then acc ^^^ F[j]! else acc) 0 := by
  intro F
  induction F with
  | nil => intro i; simp [selFrom]
  | cons f F ih =>
    intro i
    change Nat.xor (Bool.rec 0 f (bit s i)) (selFrom s F (i + 1)) = _
    rw [ih, bit_eq, List.length_cons, List.range_succ_eq_map, List.foldl_cons]
    simp only [List.foldl_map, Nat.add_zero, List.getElem!_cons_zero, List.getElem!_cons_succ,
      Nat.add_succ, Nat.succ_add]
    generalize hT : (if s.testBit i then (0 : ℕ) ^^^ f else 0) = t
    have key : ∀ (L : List ℕ) (a : ℕ), L.foldl (fun acc j => if s.testBit (i + j + 1) then
        acc ^^^ F[j]! else acc) (t ^^^ a) = t ^^^ L.foldl (fun acc j =>
          if s.testBit (i + j + 1) then acc ^^^ F[j]! else acc) a := by
      intro L
      induction L with
      | nil => intro a; rfl
      | cons x L ihL =>
        intro a
        simp only [List.foldl_cons]
        rw [← ihL]
        congr 1
        split <;> simp [Nat.xor_assoc]
    have h0 := key (List.range F.length) 0
    rw [Nat.xor_zero] at h0
    rw [h0, ← hT]
    cases s.testBit i <;> simp [Nat.zero_xor]

theorem selK_eq {F : List ℕ} {rows : Array ℕ} (hlen : F.length = 400)
    (hR : ∀ j < 400, rows[j]! = F[j]!) (s : ℕ) : selK F s = selXor 400 rows s := by
  rw [selK, selFrom_eq, hlen, selXor]
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  simp only [Nat.zero_add]
  rw [hR j (List.mem_range.mp hj)]

theorem invFrom_sound (F : List ℕ) : ∀ (D : List ℕ) (i : ℕ), invFrom F D i = true →
    i + D.length = 400 ∧ ∀ k < D.length, selK F D[k]! = 2 ^ (i + k)
  | [], i, h => by
    refine ⟨?_, fun k hk => absurd hk (by simp)⟩
    simpa using Nat.eq_of_beq_eq_true h
  | d :: D, i, h => by
    have h' : andB (Nat.beq (selK F d) (pw2 i)) (invFrom F D (i + 1)) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    obtain ⟨hl, hk⟩ := invFrom_sound F D (i + 1) h2
    refine ⟨by simp; omega, fun k hk' => ?_⟩
    cases k with
    | zero =>
      rw [List.getElem!_cons_zero, Nat.eq_of_beq_eq_true h1, pw2_eq, Nat.add_zero]
    | succ k =>
      rw [List.getElem!_cons_succ, hk k (by simp at hk'; omega)]
      congr 1
      omega

theorem invK_sound {F D : List ℕ} (h : invK F D = true) :
    D.length = 400 ∧ ∀ c < 400, selK F D[c]! = 2 ^ c := by
  obtain ⟨hl, hk⟩ := invFrom_sound F D 0 h
  refine ⟨by omega, fun c hc => ?_⟩
  rw [hk c (by omega), Nat.zero_add]

end CFSG.KC.U20

end
