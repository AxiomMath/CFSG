module

public import Certificates.Data.Kernel.SporSch.Co1Tern
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

namespace CFSG.KS.SporSch.Tern

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Mathieu Matrix

theorem foldr_add (g : Nat → Nat) : ∀ (l : List Nat) (s : Nat),
    l.foldr (fun j s => Nat.add s (g j)) s = s + (l.map g).sum
  | [], s => by simp
  | j :: l, s => by
    rw [List.foldr_cons, foldr_add g l s, List.map_cons, List.sum_cons, Nat.add_eq]
    omega

theorem range_sum (g : Nat → Nat) (n : Nat) :
    ((List.range n).map g).sum = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem foldN_add (n : Nat) (g : Nat → Nat) :
    foldN n (fun j s => Nat.add s (g j)) 0 = ∑ j ∈ Finset.range n, g j := by
  rw [foldN_eq, foldr_add, range_sum, Nat.zero_add]

theorem nget_eq (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change nget l i = _
      rw [ih]
      simp

theorem dig_eq (b i : Nat) : dig b i = b / 3 ^ i % 3 := rfl

def msg (m : Nat) : Fin 6 → ZMod 3 := fun i => ((m / 3 ^ (i : Nat) % 3 : Nat) : ZMod 3)

def enc (b : Fin 6 → ZMod 3) : Nat := ∑ i, (b i).val * 3 ^ (i : Nat)

theorem msg_enc (f : Fin 6 → ZMod 3) : msg (enc f) = f := by
  funext j
  have h : ∀ i, (f i).val < 3 := fun i => ZMod.val_lt (f i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have key : enc f / 3 ^ j.val % 3 = (f j).val := by
    simp only [enc, Fin.sum_univ_six]
    fin_cases j <;> simp <;> omega
  rw [msg, key, ZMod.natCast_zmod_val]

theorem enc_lt (f : Fin 6 → ZMod 3) : enc f < 729 := by
  have h : ∀ i, (f i).val < 3 := fun i => ZMod.val_lt (f i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp only [enc, Fin.sum_univ_six]
  simp
  omega

theorem enc_msg {m : Nat} (hm : m < 729) : enc (msg m) = m := by
  simp only [enc, msg, Fin.sum_univ_six, ZMod.val_natCast]
  simp
  omega

noncomputable def rowAux (P i : Nat) (r : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 12))
    (fun x _ ih j => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ j)) (Nat.beq x (ent P i j)))
      (Nat.blt x (nat_lit 3))) r

theorem rowAux_spec (P i : Nat) : ∀ (r : List Nat) (j0 : Nat), rowAux P i r j0 = true →
    ∀ k, j0 ≤ k → k < 12 → r.getD (k - j0) 0 = ent P i k
  | [], j0, h, k, hk, hk' => by
    have h' : Nat.beq j0 12 = true := h
    rw [Nat.beq_eq] at h'
    omega
  | x :: r, j0, h, k, hk, hk' => by
    have h' : (Nat.blt x 3 && (Nat.beq x (ent P i j0) && rowAux P i r (j0 + 1))) = true := by
      have e : rowAux P i (x :: r) j0 = Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (rowAux P i r (j0 + 1))
            (Nat.beq x (ent P i j0))) (Nat.blt x 3) := rfl
      rw [e] at h
      simpa only [bAnd_eq] using h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    rcases Nat.eq_or_lt_of_le hk with e | e
    · subst e
      simp [h'.2.1]
    · have e2 : k - j0 = (k - (j0 + 1)) + 1 := by omega
      rw [e2, List.getD_cons_succ]
      exact rowAux_spec P i r (j0 + 1) h'.2.2 k e hk'

noncomputable def rowsAux (P : Nat) (rows : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 6))
    (fun r _ ih i => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ i)) (rowOK P i r)) rows

theorem rowsAux_spec (P : Nat) : ∀ (rows : List (List Nat)) (i0 : Nat), rowsAux P rows i0 = true →
    ∀ i, i0 ≤ i → i < 6 → rowOK P i (rows.getD (i - i0) []) = true
  | [], i0, h, i, hi, hi' => by
    have h' : Nat.beq i0 6 = true := h
    rw [Nat.beq_eq] at h'
    omega
  | r :: rows, i0, h, i, hi, hi' => by
    have h' : (rowOK P i0 r && rowsAux P rows (i0 + 1)) = true := by
      have e : rowsAux P (r :: rows) i0 = Bool.rec (motive := fun _ => Bool) false
          (rowsAux P rows (i0 + 1)) (rowOK P i0 r) := rfl
      rw [e] at h
      simpa only [bAnd_eq] using h
    simp only [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le hi with e | e
    · subst e
      simpa using h'.1
    · have e2 : i - i0 = (i - (i0 + 1)) + 1 := by omega
      rw [e2, List.getD_cons_succ]
      exact rowsAux_spec P rows (i0 + 1) h'.2 i e hi'

theorem rows_ent {rows : List (List Nat)} {P : Nat} (h : rowsOK P rows = true) (i : Fin 6)
    (j : Fin 12) : (rows.getD i.val []).getD j.val 0 = ent P i j := by
  have hr := rowsAux_spec P rows 0 h i (Nat.zero_le _) i.isLt
  rw [Nat.sub_zero] at hr
  have := rowAux_spec P i _ 0 hr j (Nat.zero_le _) j.isLt
  rwa [Nat.sub_zero] at this

theorem cw_eq (P b j : Nat) : cw P b j = (∑ i ∈ Finset.range 6, dig b i * ent P i j) % 3 := by
  have e : cw P b j =
      Nat.mod (foldN 6 (fun i s => Nat.add s (Nat.mul (dig b i) (ent P i j))) 0) 3 := rfl
  rw [e, foldN_add]
  rfl

theorem vecMul_msg {P : Nat} {Rm : Matrix (Fin 6) (Fin 12) (ZMod 3)}
    (hRm : ∀ i j, Rm i j = (ent P i j : ZMod 3)) (m : Nat) (j : Fin 12) :
    (msg m ᵥ* Rm) j = ((∑ i ∈ Finset.range 6, dig m i * ent P i j : Nat) : ZMod 3) := by
  rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => ((dig m i * ent P i j : Nat) : ZMod 3))]
  simp only [Matrix.vecMul, dotProduct, hRm, msg, Nat.cast_mul, dig_eq]

theorem cw_eq_zero_iff {P : Nat} {Rm : Matrix (Fin 6) (Fin 12) (ZMod 3)}
    (hRm : ∀ i j, Rm i j = (ent P i j : ZMod 3)) (m : Nat) (j : Fin 12) :
    cw P m j = 0 ↔ (msg m ᵥ* Rm) j = 0 := by
  rw [vecMul_msg hRm, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, cw_eq]

theorem testBit_foldr (c : Nat → Bool) (k : Nat) : ∀ l : List Nat,
    (l.foldr (fun j s => if c j = true then s else s ||| 1 <<< j) 0).testBit k = true ↔
      k ∈ l ∧ c k = false
  | [] => by simp
  | j :: l => by
    rw [List.foldr_cons]
    cases hj : c j
    · rw [ite_eq_right_of_eq_false _ _ (by simp), Nat.testBit_or, Nat.one_shiftLeft,
        Nat.testBit_two_pow, Bool.or_eq_true, testBit_foldr c k l, decide_eq_true_iff, List.mem_cons]
      constructor
      · rintro (⟨h1, h2⟩ | h1)
        · exact ⟨Or.inr h1, h2⟩
        · subst h1
          exact ⟨Or.inl rfl, hj⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inr h1.symm
        · exact Or.inl ⟨h1, h2⟩
    · rw [ite_eq_left_of_eq_true _ _ (by simp), testBit_foldr c k l, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1
          rw [hj] at h2
          exact absurd h2 (by decide)
        · exact ⟨h1, h2⟩

theorem testBit_supp (P b k : Nat) : (supp P b).testBit k = true ↔ k < 12 ∧ cw P b k ≠ 0 := by
  have e : supp P b = foldN 12 (fun j s => Bool.rec (motive := fun _ => Nat)
      (Nat.lor s (Nat.shiftLeft 1 j)) s (Nat.beq (cw P b j) 0)) 0 := rfl
  have hf : (fun j s => Bool.rec (motive := fun _ => Nat) (Nat.lor s (Nat.shiftLeft 1 j)) s
      (Nat.beq (cw P b j) 0)) =
      fun j s => if Nat.beq (cw P b j) 0 = true then s else s ||| 1 <<< j := by
    funext j s
    cases Nat.beq (cw P b j) 0 <;> rfl
  rw [e, foldN_eq, hf, testBit_foldr, List.mem_range]
  simp only [Bool.eq_false_iff, ne_eq, Nat.beq_eq]

theorem supp_lt (P b : Nat) : supp P b < 4096 := by
  have : supp P b < 2 ^ 12 := Nat.lt_pow_two_of_testBit _ fun i hi => by
    cases h : (supp P b).testBit i
    · rfl
    · exact absurd ((testBit_supp P b i).1 h).1 (by omega)
  simpa using this

def toFs (x : Nat) : Finset (Fin 12) := Finset.univ.filter fun j => x.testBit j = true

theorem toFs_inj {x y : Nat} (hx : x < 4096) (hy : y < 4096) (h : toFs x = toFs y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i 12 with hi | hi
  · have e := congrArg (fun s => (⟨i, hi⟩ : Fin 12) ∈ s) h
    simp only [toFs, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at e
    exact Bool.eq_iff_iff.2 e
  · have h2 : (4096 : Nat) ≤ 2 ^ i := by
      calc (4096 : Nat) = 2 ^ 12 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem toFs_surj (F : Finset (Fin 12)) : ∃ x < 4096, toFs x = F := by
  have hb : Function.Bijective (fun x : Fin 4096 => toFs x.val) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨fun x y hxy => Fin.ext (toFs_inj x.isLt y.isLt hxy), by simp⟩
  obtain ⟨x, hx⟩ := hb.2 F
  exact ⟨x.val, x.isLt, hx⟩

theorem pop12_eq (x : Nat) : pop12 x = (toFs x).card := by
  have e : pop12 x = foldN 12 (fun j s => Nat.add s ((fun j => Nat.land (Nat.shiftRight x j) 1) j))
      0 := rfl
  rw [e, foldN_add, toFs, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun j => Nat.land (Nat.shiftRight x j) 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  change x >>> (j : Nat) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ (j : Nat)) with h | h <;> simp [h]

theorem toFs_supp {P : Nat} {Rm : Matrix (Fin 6) (Fin 12) (ZMod 3)}
    (hRm : ∀ i j, Rm i j = (ent P i j : ZMod 3)) (m : Nat) :
    toFs (supp P m) = Finset.univ.filter fun j => (msg m ᵥ* Rm) j ≠ 0 := by
  ext j
  simp only [toFs, Finset.mem_filter, Finset.mem_univ, true_and, testBit_supp, ne_eq,
    cw_eq_zero_iff hRm]
  exact ⟨fun h => h.2, fun h => ⟨j.isLt, h⟩⟩

theorem wt_eq {P : Nat} {Rm : Matrix (Fin 6) (Fin 12) (ZMod 3)}
    (hRm : ∀ i j, Rm i j = (ent P i j : ZMod 3)) (m : Nat) :
    wt P m = (Finset.univ.filter fun j => (msg m ᵥ* Rm) j ≠ 0).card := by
  rw [wt, pop12_eq, toFs_supp hRm]

theorem cnt_eq (P n : Nat) : cnt P n = ((Finset.range 729).filter fun m => wt P m = n).card := by
  have e : cnt P n = foldN 729 (fun b s => Bool.rec (motive := fun _ => Nat) s (Nat.succ s)
      (Nat.beq (wt P b) n)) 0 := rfl
  have hf : (fun b s => Bool.rec (motive := fun _ => Nat) s (Nat.succ s) (Nat.beq (wt P b) n)) =
      fun b s => Nat.add s ((fun b => if wt P b = n then 1 else 0) b) := by
    funext b s
    by_cases hb : wt P b = n <;> simp [hb]
  rw [e, hf, foldN_add, Finset.card_filter]

theorem memL_iff (x : Nat) : ∀ S : List Nat, memL x S = true ↔ x ∈ S
  | [] => by simp [memL]
  | y :: S => by
    have e : memL x (y :: S) = Bool.rec (motive := fun _ => Bool) (memL x S) true (Nat.beq x y) :=
      rfl
    rw [e, List.mem_cons, ← memL_iff x S]
    by_cases h : x = y
    · simp [h]
    · have : Nat.beq x y = false := by
        cases hb : Nat.beq x y
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) h
      rw [this]
      simp [h]

noncomputable def covAux (P : Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => Bool.rec (motive := fun _ => Bool) false ih
      (Bool.rec (motive := fun _ => Bool) true false (allN (nat_lit 729) (fun b =>
        Bool.rec (motive := fun _ => Bool) true false
          (Bool.rec (motive := fun _ => Bool) false (Nat.beq (supp P b) s)
            (Nat.beq (wt P b) (nat_lit 6))))))) S

theorem covAux_spec (P : Nat) : ∀ S : List Nat, covAux P S = true →
    ∀ s ∈ S, ∃ b < 729, wt P b = 6 ∧ supp P b = s
  | [], _ => by simp
  | s :: S, h => by
    have e : covAux P (s :: S) = Bool.rec (motive := fun _ => Bool) false (covAux P S)
        (Bool.rec (motive := fun _ => Bool) true false (allN 729 (fun b =>
          Bool.rec (motive := fun _ => Bool) true false
            (Bool.rec (motive := fun _ => Bool) false (Nat.beq (supp P b) s)
              (Nat.beq (wt P b) 6))))) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · by_contra hn
      have hall : allN 729 (fun b => Bool.rec (motive := fun _ => Bool) true false
          (Bool.rec (motive := fun _ => Bool) false (Nat.beq (supp P b) t)
            (Nat.beq (wt P b) 6))) = true := by
        rw [allN_iff]
        intro b hb
        have hb' : ¬ (wt P b = 6 ∧ supp P b = t) := fun hc => hn ⟨b, hb, hc⟩
        cases h1 : Nat.beq (wt P b) 6
        · rfl
        · cases h2 : Nat.beq (supp P b) t
          · rfl
          · simp only [Nat.beq_eq] at h1 h2
            exact absurd ⟨h1, h2⟩ hb'
      rw [hall] at h
      exact absurd h.1 (by decide)
    · exact covAux_spec P S h.2 t ht

theorem incL_spec : ∀ (S : List Nat) (p : Nat), incL S p = true →
    (∀ y ∈ S, p ≤ y) ∧ S.Pairwise (· < ·)
  | [], _, _ => by simp
  | y :: S, p, h => by
    have e : incL (y :: S) p = Bool.rec (motive := fun _ => Bool) false (incL S (Nat.succ y))
        (Nat.ble p y) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2⟩ := incL_spec S (y + 1) h.2
    refine ⟨fun z hz => ?_, List.Pairwise.cons (fun z hz => by have := h1 z hz; omega) h2⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h.1
    · have := h1 z hz
      omega

theorem cntS_eq (F : Nat) : ∀ S : List Nat,
    cntS F S = (S.filter fun s => Nat.beq (Nat.land F s) F).length
  | [] => rfl
  | s :: S => by
    have e : cntS F (s :: S) = Bool.rec (motive := fun _ => Nat) (cntS F S) (Nat.succ (cntS F S))
        (Nat.beq (Nat.land F s) F) := rfl
    rw [e, List.filter_cons, cntS_eq F S]
    cases Nat.beq (Nat.land F s) F <;> rfl

theorem subset_iff_land {F : Nat} (hF : F < 4096) (s : Nat) :
    toFs F ⊆ toFs s ↔ Nat.land F s = F := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    change (F &&& s).testBit i = F.testBit i
    rw [Nat.testBit_and]
    cases hi : F.testBit i
    · rfl
    · have hi12 : i < 12 := by
        by_contra hc
        have h2 : (4096 : Nat) ≤ 2 ^ i := by
          calc (4096 : Nat) = 2 ^ 12 := rfl
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow (by omega)] at hi
        exact absurd hi (by decide)
      have hm : (⟨i, hi12⟩ : Fin 12) ∈ toFs F := by simp [toFs, hi]
      have := h hm
      simp only [toFs, Finset.mem_filter, Finset.mem_univ, true_and] at this
      rw [this]
      rfl
  · intro h j hj
    simp only [toFs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have e := congrArg (fun x => x.testBit j) h
    change (F &&& s).testBit j = F.testBit j at e
    rw [Nat.testBit_and, hj, Bool.true_and] at e
    exact e

public theorem ternK_sound {rows : List (List Nat)} {P : Nat} {C S : List Nat}
    {Rm : Matrix (Fin 6) (Fin 12) (ZMod 3)}
    (hR : Rm = Matrix.of fun i j => (((rows.getD i.val []).getD j.val 0 : ℕ) : ZMod 3))
    (h : ternK rows P C S = true) :
    (∀ n < 13, (Finset.univ.filter fun b : Fin 6 → ZMod 3 =>
        (Finset.univ.filter fun j => (b ᵥ* Rm) j ≠ 0).card = n).card = C.getD n 0) ∧
    ((Finset.univ.filter fun b : Fin 6 → ZMod 3 =>
        (Finset.univ.filter fun j => (b ᵥ* Rm) j ≠ 0).card = 6).image
          (fun b => Finset.univ.filter fun j => (b ᵥ* Rm) j ≠ 0)).card = S.length ∧
    ∀ F ∈ (Finset.univ : Finset (Fin 12)).powersetCard 5,
      (((Finset.univ.filter fun b : Fin 6 → ZMod 3 =>
          (Finset.univ.filter fun j => (b ᵥ* Rm) j ≠ 0).card = 6).image
            (fun b => Finset.univ.filter fun j => (b ᵥ* Rm) j ≠ 0)).filter
              fun s => F ⊆ s).card = 1 := by
  unfold ternK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hRm : ∀ i j, Rm i j = (ent P i j : ZMod 3) := by
    intro i j
    rw [hR, Matrix.of_apply, rows_ent h1]
  have key := wt_eq hRm
  have hC : ∀ n < 13, cnt P n = C.getD n 0 := by
    intro n hn
    have := (allN_iff.1 h2) n hn
    rwa [Nat.beq_eq, nget_eq] at this
  have hS3 : ∀ b < 729, wt P b = 6 → supp P b ∈ S := by
    intro b hb hw
    have := (allN_iff.1 h3) b hb
    have hw' : Nat.beq (wt P b) 6 = true := by simp [hw]
    rw [hw'] at this
    exact (memL_iff _ S).1 this
  have hS4 : ∀ s ∈ S, ∃ b < 729, wt P b = 6 ∧ supp P b = s := covAux_spec P S h4
  have hS5 : S.Nodup := ((incL_spec S 0 h5).2).imp Nat.ne_of_lt
  have hS6 : ∀ F < 4096, pop12 F = 5 → cntS F S = 1 := by
    intro F hF hp
    have := (allN_iff.1 h6) F hF
    have hp' : Nat.beq (pop12 F) 5 = true := by simp [hp]
    rw [hp'] at this
    simpa using this
  have hSlt : ∀ s ∈ S, s < 4096 := by
    intro s hs
    obtain ⟨b, _, _, rfl⟩ := hS4 s hs
    exact supp_lt P b
  have hnd : (S.map toFs).Nodup :=
    hS5.map_on fun x hx y hy hxy => toFs_inj (hSlt x hx) (hSlt y hy) hxy
  have himg : ((Finset.univ.filter fun b : Fin 6 → ZMod 3 =>
        (Finset.univ.filter fun j => (b ᵥ* Rm) j ≠ 0).card = 6).image
          (fun b => Finset.univ.filter fun j => (b ᵥ* Rm) j ≠ 0)) = (S.map toFs).toFinset := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨supp P (enc b), hS3 _ (enc_lt b) (by rw [key, msg_enc, hb]), ?_⟩
      rw [toFs_supp hRm, msg_enc]
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨m, hm, hw, rfl⟩ := hS4 s hs
      exact ⟨msg m, by rw [← key, hw], (toFs_supp hRm m).symm⟩
  refine ⟨fun n hn => ?_, ?_, fun F hF => ?_⟩
  · rw [← hC n hn, cnt_eq]
    refine Finset.card_nbij' enc msg ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hb ⊢
      exact ⟨enc_lt b, by rw [key, msg_enc, hb]⟩
    · intro m hm
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hm ⊢
      rw [← key, hm.2]
    · intro b _
      exact msg_enc b
    · intro m hm
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hm
      exact enc_msg hm.1
  · rw [himg, List.toFinset_card_of_nodup hnd, List.length_map]
  · obtain ⟨F', hF', rfl⟩ := toFs_surj F
    have h5' : (toFs F').card = 5 := (Finset.mem_powersetCard.1 hF).2
    rw [himg, List.filter_toFinset, List.toFinset_card_of_nodup (hnd.filter _), List.filter_map,
      List.length_map, ← hS6 F' hF' (by rw [pop12_eq, h5']), cntS_eq]
    congr 1
    apply List.filter_congr
    intro s _
    exact Bool.eq_iff_iff.2 (decide_eq_true_iff.trans
      ((subset_iff_land hF' s).trans Nat.beq_eq.symm.to_iff))

end CFSG.KS.SporSch.Tern
