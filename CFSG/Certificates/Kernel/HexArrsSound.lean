module

public import Certificates.Data.Kernel.HexArrs
public import Certificates.Data.B3Spor3Checks
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.HexText
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.HexArrs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PackFld CFSG.KS.HexText CFSG.KS.HexNums

@[expose] noncomputable def numL (cs : List Char) (o : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => numL cs o c * 16 + hexL (Char.toNat cs[o + c]!)

theorem hexL_ite (c : Nat) : hexL c = if c < 48 then 16 else if c < 58 then c - 48 else
    if c < 97 then 16 else if c < 103 then c - 87 else 16 := by
  unfold hexL
  rw [blt_dec, blt_dec, blt_dec, blt_dec, nrec_dec, nrec_dec, nrec_dec, nrec_dec]
  rfl

theorem hexL_dig {c : Nat} (h : hexL c < 16) :
    (48 ≤ c ∧ c < 58 ∧ hexL c = c - 48) ∨ (97 ≤ c ∧ c < 103 ∧ hexL c = c - 87) := by
  rw [hexL_ite] at h ⊢
  by_cases h1 : c < 48
  · rw [iteT h1] at h
    omega
  · rw [iteF h1] at h ⊢
    by_cases h2 : c < 58
    · rw [iteT h2] at h ⊢
      omega
    · rw [iteF h2] at h ⊢
      by_cases h3 : c < 97
      · rw [iteT h3] at h
        omega
      · rw [iteF h3] at h ⊢
        by_cases h4 : c < 103
        · rw [iteT h4] at h ⊢
          omega
        · rw [iteF h4] at h
          omega

private theorem char_le (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat := UInt32.le_iff_toNat_le

theorem hexDigit_eq {c : Char} (h : hexL c.toNat < 16) :
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexDigit c = hexL c.toNat := by
  unfold CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexDigit
  have h0 : ('0' ≤ c ∧ c ≤ '9') ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    rw [char_le, char_le]
    rfl
  rcases hexL_dig h with ⟨a, b, e⟩ | ⟨a, b, e⟩
  · rw [if_pos (h0.2 ⟨a, by omega⟩), e]
  · rw [if_neg (fun hc => by have := (h0.1 hc).2; omega), e]

private noncomputable def stepH (d n w N : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (j e t v acc : Nat) : Bool :=
  bIf(Nat.beq j N, true,
    strictB (hexL (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
      bIf(Nat.beq (Nat.succ t) d,
        bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
          strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
            bIf(Nat.beq (Nat.succ e) n,
              bAnd(Nat.beq acc' (F j),
                ih (Nat.succ j) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
              ih j (Nat.succ e) (nat_lit 0) (nat_lit 0) acc')),
          false),
        ih j e (Nat.succ t) v' acc)),
      false)))

private theorem run_cons (d n w N : Nat) (F : Nat → Nat) (ch : Char) (L : List Char)
    (j e t v acc : Nat) :
    run d n w N F (ch :: L) j e t v acc = stepH d n w N F ch (run d n w N F L) j e t v acc := rfl

private theorem run_nil (d n w N : Nat) (F : Nat → Nat) (j e t v acc : Nat) :
    run d n w N F [] j e t v acc = Nat.beq j N := rfl

section Steps

variable {d n w N : Nat} {F : Nat → Nat} {ch : Char} {ih : Nat → Nat → Nat → Nat → Nat → Bool}
  {j e t v acc : Nat}

private theorem stepH_bad (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexL (Char.toNat ch)) 16 = false) :
    stepH d n w N F ch ih j e t v acc = false := by
  unfold stepH
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]

private theorem stepH_dig (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexL (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = false) :
    stepH d n w N F ch ih j e t v acc =
      ih j e (Nat.succ t) (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) acc := by
  unfold stepH
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]

private theorem stepH_big (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexL (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.shiftLeft 1 w) = false) :
    stepH d n w N F ch ih j e t v acc = false := by
  unfold stepH
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]

private theorem stepH_ent (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexL (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.shiftLeft 1 w) = true)
    (he : Nat.beq (Nat.succ e) n = false) :
    stepH d n w N F ch ih j e t v acc =
      ih j (Nat.succ e) 0 0
        (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.mul w e))) := by
  unfold stepH
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [he]

private theorem stepH_tab (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexL (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.shiftLeft 1 w) = true)
    (he : Nat.beq (Nat.succ e) n = true) :
    stepH d n w N F ch ih j e t v acc =
      bAnd(Nat.beq (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch)))
        (Nat.mul w e))) (F j), ih (Nat.succ j) 0 0 0 0) := by
  unfold stepH
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [he]

end Steps

private theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem digits {cs : List Char} {d n w N : Nat} {F : Nat → Nat} {j e o acc : Nat}
    (hj : j < N) : ∀ c t, t + c = d → t < d →
    run d n w N F (cs.drop (o + t)) j e t (numL cs o t) acc = true →
    (∀ s, t ≤ s → s < d → o + s < cs.length ∧ hexL (Char.toNat cs[o + s]!) < 16) ∧
    numL cs o d < 2 ^ w ∧
    (e + 1 = n → Nat.lor acc (Nat.shiftLeft (numL cs o d) (Nat.mul w e)) = F j ∧
      run d n w N F (cs.drop (o + d)) (j + 1) 0 0 0 0 = true) ∧
    (e + 1 ≠ n → run d n w N F (cs.drop (o + d)) j (e + 1) 0 0
      (Nat.lor acc (Nat.shiftLeft (numL cs o d) (Nat.mul w e))) = true) := by
  intro c
  induction c with
  | zero => intro t h1 h2; omega
  | succ c ih =>
    intro t hc htd hr
    have hjN : Nat.beq j N = false := beq_false (by omega)
    have hlen : o + t < cs.length := by
      apply Nat.lt_of_not_le
      intro hl
      rw [List.drop_eq_nil_of_le hl, run_nil, hjN] at hr
      exact Bool.false_ne_true hr
    rw [List.drop_eq_getElem_cons hlen, run_cons] at hr
    have hget : cs[o + t]! = cs[o + t] := getElem!_pos cs (o + t) hlen
    have hv' : Nat.add (Nat.mul (numL cs o t) 16) (hexL (Char.toNat cs[o + t])) =
        numL cs o (t + 1) := by
      rw [numL, hget]
      rfl
    cases hh : Nat.blt (hexL (Char.toNat cs[o + t])) 16
    · rw [stepH_bad hjN hh] at hr
      exact absurd hr Bool.false_ne_true
    have hdig : hexL (Char.toNat cs[o + t]!) < 16 := by
      rw [hget]
      exact Nat.blt_eq.mp hh
    cases ht : Nat.beq (Nat.succ t) d
    · have htd' : t + 1 < d := by
        have := false_of_beq ht
        omega
      rw [stepH_dig hjN hh ht, hv'] at hr
      have e1 : o + t + 1 = o + (t + 1) := by omega
      rw [e1] at hr
      obtain ⟨a, b, c1, c2⟩ := ih (t + 1) (by omega) htd' hr
      refine ⟨fun s hs1 hs2 => ?_, b, c1, c2⟩
      rcases Nat.lt_or_ge s (t + 1) with hs | hs
      · have : s = t := by omega
        subst this
        exact ⟨hlen, hdig⟩
      · exact a s hs hs2
    · have htd' : t + 1 = d := Nat.eq_of_beq_eq_true ht
      have hch : ∀ s, t ≤ s → s < d → o + s < cs.length ∧ hexL (Char.toNat cs[o + s]!) < 16 := by
        intro s hs1 hs2
        have : s = t := by omega
        subst this
        exact ⟨hlen, hdig⟩
      cases hv : Nat.blt (Nat.add (Nat.mul (numL cs o t) 16) (hexL (Char.toNat cs[o + t])))
          (Nat.shiftLeft 1 w)
      · rw [stepH_big hjN hh ht hv] at hr
        exact absurd hr Bool.false_ne_true
      have hV : numL cs o d < 2 ^ w := by
        have := Nat.blt_eq.mp hv
        rw [hv', htd', shl_eq, Nat.one_mul] at this
        exact this
      have hdrop : o + t + 1 = o + d := by omega
      cases he : Nat.beq (Nat.succ e) n
      · rw [stepH_ent hjN hh ht hv he, hv', htd', hdrop] at hr
        exact ⟨hch, hV, fun h => absurd h (false_of_beq he), fun _ => hr⟩
      · rw [stepH_tab hjN hh ht hv he, hv', htd', hdrop] at hr
        simp only [bAnd_iff] at hr
        exact ⟨hch, hV, fun _ => ⟨Nat.eq_of_beq_eq_true hr.1, hr.2⟩,
          fun h => absurd (Nat.eq_of_beq_eq_true he) h⟩

private theorem table {cs : List Char} {d n w N : Nat} {F : Nat → Nat} {j : Nat} (hj : j < N)
    (hd : 0 < d) : ∀ r e acc, e + r = n → e < n →
    Fld w acc (fun i => if i < e then numL cs (d * (n * j + i)) d else 0) →
    run d n w N F (cs.drop (d * (n * j + e))) j e 0 0 acc = true →
    (∀ i, e ≤ i → i < n → numL cs (d * (n * j + i)) d < 2 ^ w ∧
      ∀ s < d, d * (n * j + i) + s < cs.length ∧
        hexL (Char.toNat cs[d * (n * j + i) + s]!) < 16) ∧
    Fld w (F j) (fun i => if i < n then numL cs (d * (n * j + i)) d else 0) ∧
    run d n w N F (cs.drop (d * (n * (j + 1)))) (j + 1) 0 0 0 0 = true := by
  intro r
  induction r with
  | zero => intro e acc h1 h2; omega
  | succ r ih =>
    intro e acc hr he hacc hrun
    obtain ⟨hch, hV, hlast, hmid⟩ := digits (cs := cs) (o := d * (n * j + e)) (acc := acc)
      (e := e) hj d 0 (by omega) hd (by rw [Nat.add_zero]; exact hrun)
    have hacc' : Fld w (Nat.lor acc (Nat.shiftLeft (numL cs (d * (n * j + e)) d) (Nat.mul w e)))
        (fun i => if i < e + 1 then numL cs (d * (n * j + i)) d else 0) := by
      refine fld_congr (fld_or hacc (fld_shl e (fld_one hV))) ?_
      intro i
      by_cases h1 : i < e
      · have h2 : ¬ e ≤ i := by omega
        have h3 : i < e + 1 := by omega
        rw [iteT h1, iteF h2, iteT h3, Nat.or_zero]
      · by_cases h2 : i = e
        · subst h2
          have h3 : i < i + 1 := by omega
          rw [iteF h1, iteT (Nat.le_refl i), Nat.sub_self, iteT rfl, iteT h3, Nat.zero_or]
        · have h3 : ¬ i < e + 1 := by omega
          have h4 : i - e ≠ 0 := by omega
          rw [iteF h1, iteF h3, Nat.zero_or]
          by_cases h5 : e ≤ i
          · rw [iteT h5, iteF h4]
          · rw [iteF h5]
    have hstep : d * (n * j + e) + d = d * (n * j + (e + 1)) := by
      rw [← Nat.add_assoc, Nat.mul_succ]
    have hnow : ∀ s < d, d * (n * j + e) + s < cs.length ∧
        hexL (Char.toNat cs[d * (n * j + e) + s]!) < 16 :=
      fun s hs => hch s (Nat.zero_le s) hs
    by_cases hl : e + 1 = n
    · obtain ⟨hF, hnext⟩ := hlast hl
      have hjn : d * (n * j + e) + d = d * (n * (j + 1)) := by
        rw [hstep, Nat.mul_succ n j, hl]
      rw [hjn] at hnext
      refine ⟨fun i hi1 hi2 => ?_, ?_, hnext⟩
      · have : i = e := by omega
        subst this
        exact ⟨hV, hnow⟩
      · rw [← hF]
        refine fld_congr hacc' ?_
        intro i
        rw [hl]
    · have hnext := hmid hl
      rw [hstep] at hnext
      obtain ⟨a, b, c⟩ := ih (e + 1) _ (by omega) (by omega) hacc' hnext
      refine ⟨fun i hi1 hi2 => ?_, b, c⟩
      rcases Nat.lt_or_ge i (e + 1) with h | h
      · have : i = e := by omega
        subst this
        exact ⟨hV, hnow⟩
      · exact a i h hi2

private theorem tables {cs : List Char} {d n w N : Nat} {F : Nat → Nat} (hd : 0 < d)
    (hn : 0 < n) : ∀ r j, j + r = N →
    run d n w N F (cs.drop (d * (n * j))) j 0 0 0 0 = true →
    ∀ j', j ≤ j' → j' < N →
      (∀ i < n, numL cs (d * (n * j' + i)) d < 2 ^ w ∧
        ∀ s < d, d * (n * j' + i) + s < cs.length ∧
          hexL (Char.toNat cs[d * (n * j' + i) + s]!) < 16) ∧
      Fld w (F j') (fun i => if i < n then numL cs (d * (n * j' + i)) d else 0) := by
  intro r
  induction r with
  | zero => intro j h1 _ j' h2 h3; omega
  | succ r ih =>
    intro j hr hrun j' hj1 hj2
    have hjN : j < N := by omega
    have h0 : Fld w 0 (fun i => if i < 0 then numL cs (d * (n * j + i)) d else 0) :=
      fld_congr (fld_zero w) (fun i => (iteF (Nat.not_lt_zero i)).symm)
    obtain ⟨a, b, c⟩ := table (cs := cs) (F := F) hjN hd n 0 0 (by omega) hn h0
      (by rw [Nat.add_zero]; exact hrun)
    rcases Nat.lt_or_ge j j' with h | h
    · exact ih (j + 1) (by omega) c j' h hj2
    · have : j' = j := by omega
      subst this
      exact ⟨fun i hi => a i (Nat.zero_le i) hi, b⟩

private theorem fold_num {cs : List Char} {o : Nat} : ∀ c, (∀ s < c, o + s < cs.length ∧ hexL (Char.toNat cs[o + s]!) < 16) →
      (List.range c).foldl (fun acc t =>
        acc * 16 + ((cs.map CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexDigit).toArray)[o + t]!)
        0 = numL cs o c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
    intro h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (fun s hs => h s (by omega)), numL]
    obtain ⟨hl, hx⟩ := h c (Nat.lt_succ_self c)
    congr 1
    rw [getElem!_pos _ (o + c) (by simpa using hl), getElem!_pos cs (o + c) hl] at *
    simp only [List.getElem_toArray, List.getElem_map]
    exact hexDigit_eq hx

theorem hexArrs_sound {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : hexArrsK cs d n w N F = true) :
    (CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexArrs n d (String.ofList cs)).size = N ∧
      ∀ j < N, (CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexArrs n d
        (String.ofList cs))[j]! = unpack n w (F j) := by
  unfold hexArrsK at h
  simp only [bAnd_iff] at h
  obtain ⟨hlen, hd, hn, hr⟩ := h
  have hlen' : cs.length = d * (n * N) := Nat.eq_of_beq_eq_true hlen
  have hd' : 0 < d := Nat.blt_eq.mp hd
  have hn' : 0 < n := Nat.blt_eq.mp hn
  have T := tables (cs := cs) (F := F) (w := w) (N := N) hd' hn' N 0 (Nat.zero_add N)
    (by rw [Nat.mul_zero, Nat.mul_zero, List.drop_zero]; exact hr)
  have hsz : (CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexArrs n d
      (String.ofList cs)).size = N := by
    unfold CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexArrs
    simp only [Array.size_ofFn, String.toList_ofList, List.size_toArray, List.length_map, hlen']
    have e : d * (n * N) = N * (n * d) := by ring
    rw [e]
    exact Nat.mul_comm n d ▸ Nat.mul_div_cancel N (Nat.mul_pos hn' hd')
  refine ⟨hsz, fun j hj => ?_⟩
  obtain ⟨hA, hF⟩ := T j (Nat.zero_le _) hj
  rw [getElem!_pos _ j (by rw [hsz]; exact hj)]
  apply Array.ext
  · simp [CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexArrs, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexArrs] using h1
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hexArrs, Array.getElem_ofFn, unpack,
      String.toList_ofList]
    rw [pg_of_fld hF (by simp only [hi, ↓reduceIte]; exact (hA i hi).1)]
    simp only [hi, ↓reduceIte]
    have ho : (j * n + i) * d = d * (n * j + i) := by ring
    rw [ho]
    exact fold_num d (hA i hi).2

end CFSG.KC.HexArrs

end
