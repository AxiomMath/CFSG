module

public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.Monster.B.Fischer.InducedData
public import Certificates.Data.CFSGNative.SmallOddCore.Check
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.HexText
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PackFld CFSG.KS.HexText
open CFSG.KS.Text (hexV)

private noncomputable def stepH (d n w N : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (j e t v acc : Nat) : Bool :=
  bIf(Nat.beq j N, true,
    strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
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
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = false) :
    stepH d n w N F ch ih j e t v acc = false := by
  unfold stepH
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]

private theorem stepH_dig (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = false) :
    stepH d n w N F ch ih j e t v acc =
      ih j e (Nat.succ t) (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) acc := by
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
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) = false) :
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
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) = true)
    (he : Nat.beq (Nat.succ e) n = false) :
    stepH d n w N F ch ih j e t v acc =
      ih j (Nat.succ e) 0 0
        (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.mul w e))) := by
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
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) = true)
    (he : Nat.beq (Nat.succ e) n = true) :
    stepH d n w N F ch ih j e t v acc =
      bAnd(Nat.beq (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch)))
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
    run d n w N F (cs.drop (o + t)) j e t (numA cs o t) acc = true →
    (∀ s, t ≤ s → s < d → o + s < cs.length ∧ hexV (Char.toNat cs[o + s]!) < 16) ∧
    numA cs o d < 2 ^ w ∧
    (e + 1 = n → Nat.lor acc (Nat.shiftLeft (numA cs o d) (Nat.mul w e)) = F j ∧
      run d n w N F (cs.drop (o + d)) (j + 1) 0 0 0 0 = true) ∧
    (e + 1 ≠ n → run d n w N F (cs.drop (o + d)) j (e + 1) 0 0
      (Nat.lor acc (Nat.shiftLeft (numA cs o d) (Nat.mul w e))) = true) := by
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
    have hv' : Nat.add (Nat.mul (numA cs o t) 16) (hexV (Char.toNat cs[o + t])) =
        numA cs o (t + 1) := by
      rw [numA, hget]
      rfl
    cases hh : Nat.blt (hexV (Char.toNat cs[o + t])) 16
    · rw [stepH_bad hjN hh] at hr
      exact absurd hr Bool.false_ne_true
    have hdig : hexV (Char.toNat cs[o + t]!) < 16 := by
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
      have hch : ∀ s, t ≤ s → s < d → o + s < cs.length ∧ hexV (Char.toNat cs[o + s]!) < 16 := by
        intro s hs1 hs2
        have : s = t := by omega
        subst this
        exact ⟨hlen, hdig⟩
      cases hv : Nat.blt (Nat.add (Nat.mul (numA cs o t) 16) (hexV (Char.toNat cs[o + t])))
          (Nat.shiftLeft 1 w)
      · rw [stepH_big hjN hh ht hv] at hr
        exact absurd hr Bool.false_ne_true
      have hV : numA cs o d < 2 ^ w := by
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
    Fld w acc (fun i => if i < e then numA cs (d * (n * j + i)) d else 0) →
    run d n w N F (cs.drop (d * (n * j + e))) j e 0 0 acc = true →
    (∀ i, e ≤ i → i < n → numA cs (d * (n * j + i)) d < 2 ^ w ∧
      ∀ s < d, d * (n * j + i) + s < cs.length ∧
        hexV (Char.toNat cs[d * (n * j + i) + s]!) < 16) ∧
    Fld w (F j) (fun i => if i < n then numA cs (d * (n * j + i)) d else 0) ∧
    run d n w N F (cs.drop (d * (n * (j + 1)))) (j + 1) 0 0 0 0 = true := by
  intro r
  induction r with
  | zero => intro e acc h1 h2; omega
  | succ r ih =>
    intro e acc hr he hacc hrun
    obtain ⟨hch, hV, hlast, hmid⟩ := digits (cs := cs) (o := d * (n * j + e)) (acc := acc)
      (e := e) hj d 0 (by omega) hd (by rw [Nat.add_zero]; exact hrun)
    have hacc' : Fld w (Nat.lor acc (Nat.shiftLeft (numA cs (d * (n * j + e)) d) (Nat.mul w e)))
        (fun i => if i < e + 1 then numA cs (d * (n * j + i)) d else 0) := by
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
        hexV (Char.toNat cs[d * (n * j + e) + s]!) < 16 :=
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
      (∀ i < n, numA cs (d * (n * j' + i)) d < 2 ^ w ∧
        ∀ s < d, d * (n * j' + i) + s < cs.length ∧
          hexV (Char.toNat cs[d * (n * j' + i) + s]!) < 16) ∧
      Fld w (F j') (fun i => if i < n then numA cs (d * (n * j' + i)) d else 0) := by
  intro r
  induction r with
  | zero => intro j h1 _ j' h2 h3; omega
  | succ r ih =>
    intro j hr hrun j' hj1 hj2
    have hjN : j < N := by omega
    have h0 : Fld w 0 (fun i => if i < 0 then numA cs (d * (n * j + i)) d else 0) :=
      fld_congr (fld_zero w) (fun i => (iteF (Nat.not_lt_zero i)).symm)
    obtain ⟨a, b, c⟩ := table (cs := cs) (F := F) hjN hd n 0 0 (by omega) hn h0
      (by rw [Nat.add_zero]; exact hrun)
    rcases Nat.lt_or_ge j j' with h | h
    · exact ih (j + 1) (by omega) c j' h hj2
    · have : j' = j := by omega
      subst this
      exact ⟨fun i hi => a i (Nat.zero_le i) hi, b⟩

private theorem decode {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : hexFlat cs d n w N F = true) :
    (∀ k < d * n * N, k < cs.length ∧ (cs[k]!).toNat < 128) ∧
    ∀ j < N, ∀ i < n, pg w (mask w) (F j) i = numA cs (d * (n * j + i)) d ∧
      ∀ s < d, d * (n * j + i) + s < d * n * N := by
  unfold hexFlat at h
  simp only [bAnd_iff] at h
  obtain ⟨hd, hn, hr⟩ := h
  have hd' : 0 < d := Nat.blt_eq.mp hd
  have hn' : 0 < n := Nat.blt_eq.mp hn
  have T := tables (cs := cs) (F := F) (w := w) (N := N) hd' hn' N 0 (Nat.zero_add N)
    (by rw [Nat.mul_zero, Nat.mul_zero, List.drop_zero]; exact hr)
  have hpos : ∀ j < N, ∀ i < n, ∀ s < d, d * (n * j + i) + s < d * n * N := by
    intro j hj i hi s hs
    have h1 : n * j + i + 1 ≤ n * N := by
      have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ] at this
      omega
    have h2 := Nat.mul_le_mul_left d h1
    rw [Nat.mul_succ] at h2
    rw [Nat.mul_assoc]
    omega
  refine ⟨fun k hk => ?_, fun j hj i hi => ⟨?_, hpos j hj i hi⟩⟩
  · have hq : k / d < n * N := by
      rw [Nat.div_lt_iff_lt_mul hd']
      rw [Nat.mul_comm (n * N) d, ← Nat.mul_assoc]
      exact hk
    have hjj : k / d / n < N := by
      rw [Nat.div_lt_iff_lt_mul hn']
      rw [Nat.mul_comm N n]
      exact hq
    have ek : k = d * (n * (k / d / n) + k / d % n) + k % d := by
      rw [Nat.div_add_mod (k / d) n, Nat.div_add_mod k d]
    obtain ⟨hA, -⟩ := T (k / d / n) (Nat.zero_le _) hjj
    obtain ⟨-, hB⟩ := hA (k / d % n) (Nat.mod_lt _ hn')
    obtain ⟨hl, hx⟩ := hB (k % d) (Nat.mod_lt _ hd')
    rw [← ek] at hl hx
    refine ⟨hl, ?_⟩
    rcases hexV_dig hx with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  · obtain ⟨hA, hF⟩ := T j (Nat.zero_le _) hj
    rw [pg_of_fld hF (by simp only [hi, ↓reduceIte]; exact (hA i hi).1)]
    simp only [hi, ↓reduceIte]

private theorem digits_of {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : hexFlat cs d n w N F = true) : ∀ k < d * n * N, hexV (Char.toNat cs[k]!) < 16 := by
  unfold hexFlat at h
  simp only [bAnd_iff] at h
  obtain ⟨hd, hn, hr⟩ := h
  have hd' : 0 < d := Nat.blt_eq.mp hd
  have hn' : 0 < n := Nat.blt_eq.mp hn
  have T := tables (cs := cs) (F := F) (w := w) (N := N) hd' hn' N 0 (Nat.zero_add N)
    (by rw [Nat.mul_zero, Nat.mul_zero, List.drop_zero]; exact hr)
  intro k hk
  have hq : k / d < n * N := by
    rw [Nat.div_lt_iff_lt_mul hd']
    rw [Nat.mul_comm (n * N) d, ← Nat.mul_assoc]
    exact hk
  have hjj : k / d / n < N := by
    rw [Nat.div_lt_iff_lt_mul hn']
    rw [Nat.mul_comm N n]
    exact hq
  have ek : k = d * (n * (k / d / n) + k / d % n) + k % d := by
    rw [Nat.div_add_mod (k / d) n, Nat.div_add_mod k d]
  obtain ⟨hA, -⟩ := T (k / d / n) (Nat.zero_le _) hjj
  obtain ⟨-, hB⟩ := hA (k / d % n) (Nat.mod_lt _ hn')
  obtain ⟨-, hx⟩ := hB (k % d) (Nat.mod_lt _ hd')
  rw [← ek] at hx
  exact hx

theorem hexTable3_sound {cs : List Char} {n w N : Nat} {F : Nat → Nat}
    (h : hexFlat cs 3 n w N F = true) :
    ∀ j < N, CFSG.Monster.B.Fischer.hexTable3 n (n * j) (String.ofList cs) = unpack n w (F j) := by
  obtain ⟨hasc, hF⟩ := decode h
  have hdig := digits_of h
  intro j hj
  apply Array.ext
  · simp [CFSG.Monster.B.Fischer.hexTable3, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [CFSG.Monster.B.Fischer.hexTable3] using h1
    simp only [CFSG.Monster.B.Fischer.hexTable3, unpack, Array.getElem_ofFn]
    obtain ⟨e1, e2⟩ := hF j hj i hi
    rw [e1]
    exact num_bytes (o := 3 * (n * j + i)) hasc
      (fun c => CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 (3 * (n * j + i)) c)
      rfl (fun c => rfl) 3 (by have := e2 2 (by omega); omega) (fun s hs => hdig _ (e2 s hs))

theorem hexTable_sound {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : hexFlat cs d n w N F = true) :
    ∀ j < N, CFSG.Monster.B.Co2.Native.hexTable d n (n * j) (String.ofList cs) =
      unpack n w (F j) := by
  obtain ⟨hasc, hF⟩ := decode h
  have hdig := digits_of h
  intro j hj
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    simp only [CFSG.Monster.B.Co2.Native.hexTable, unpack, Array.getElem_ofFn]
    obtain ⟨e1, e2⟩ := hF j hj i hi
    have hd : 0 < d := by
      unfold hexFlat at h
      simp only [bAnd_iff] at h
      exact Nat.blt_eq.mp h.1
    rw [e1]
    exact num_bytes (o := d * (n * j + i)) hasc
      (fun c => CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8 (d * (n * j + i)) c)
      rfl (fun c => rfl) d (by have := e2 (d - 1) (by omega); omega) (fun s hs => hdig _ (e2 s hs))

theorem hexT_sound {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : hexFlat cs d n w N F = true) (hw : w ≤ 32) :
    ∀ j < N, CFSG.Sporadic.SmallOddCore.Native.natArr
      (CFSG.Sporadic.SmallOddCore.Native.hexT d n (n * j) (String.ofList cs)) =
        unpack n w (F j) := by
  obtain ⟨hasc, hF⟩ := decode h
  have hdig := digits_of h
  intro j hj
  apply Array.ext
  · simp [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.Sporadic.SmallOddCore.Native.hexT,
      unpack]
  · intro i h1 _
    have hi : i < n := by
      simpa [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.Sporadic.SmallOddCore.Native.hexT]
        using h1
    simp only [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.Sporadic.SmallOddCore.Native.hexT,
      unpack, Array.getElem_ofFn, Array.getElem_map]
    obtain ⟨e1, e2⟩ := hF j hj i hi
    have hd : 0 < d := by
      unfold hexFlat at h
      simp only [bAnd_iff] at h
      exact Nat.blt_eq.mp h.1
    have hnum := num_bytes (o := d * (n * j + i)) hasc
      (fun c => CFSG.Sporadic.SmallOddCore.Native.hexNum (String.ofList cs).toUTF8
        (d * (n * j + i)) c)
      rfl (fun c => rfl) d (by have := e2 (d - 1) (by omega); omega) (fun s hs => hdig _ (e2 s hs))
    have hlt : pg w (mask w) (F j) i < UInt32.size :=
      Nat.lt_of_lt_of_le (pg_lt _ _ _) (Nat.pow_le_pow_right (by omega) hw)
    rw [hnum, ← e1, UInt32.toNat_ofNat_of_lt' hlt]

end CFSG.KC.Misc.HexFlat

end
