
module

public import Certificates.Data.Kernel.SporSch.J4SText
public import CFSG.Certificates.Kernel.SporSch.J4SBfsSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SporSch.C11

open CFSG.Sporadic.Schreier.PairText CFSG.KC.Enum CFSG.KS.PackFld

private noncomputable def run (w n k : Nat) (T : Nat → Nat) (L : List Int) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun j c _ => bAnd(Nat.beq j k, Nat.beq c (nat_lit 0)))
    (fun x _ ih j c acc => bIf(Nat.beq j k, true,
      strictB (natOf w x) (fun v => bAnd(Nat.blt v (Nat.shiftLeft (nat_lit 1) w),
        strictB (Nat.lor acc (Nat.shiftLeft v (Nat.mul w c))) (fun acc' =>
          bIf(Nat.beq (Nat.succ c) n,
            bAnd(Nat.beq acc' (T j), ih (Nat.succ j) (nat_lit 0) (nat_lit 0)),
            ih j (Nat.succ c) acc'))))))
    L

private theorem toArr_get {L : List Int} {i : Nat} {x : Int} {rest : List Int}
    (h : L.drop i = x :: rest) : L.toArray[i]! = x := by
  have h1 : L[i]? = some x := by
    have := congrArg (fun l : List Int => l[0]?) h
    simpa [List.getElem?_drop] using this
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.1 h1
  rw [getElem!_pos L.toArray i (by simpa using hi)]
  simpa using hx

private theorem drop_succ {L : List Int} {i : Nat} {x : Int} {rest : List Int}
    (h : L.drop i = x :: rest) : L.drop (i + 1) = rest := by
  rw [← List.drop_drop, h]
  rfl

private theorem ent_eq (w P i : Nat) : ent w P i = pg w (mask w) P i := rfl

private theorem run_sound {w n k : Nat} {T : Nat → Nat} {L : List Int} :
    ∀ (rest : List Int) (j c acc : Nat), run w n k T rest j c acc = true →
    L.drop (n * j + c) = rest → c < n →
    Fld w acc (fun e => if e < c then (L.toArray[n * j + e]!).toNat else 0) →
    (∀ e < c, (L.toArray[n * j + e]!).toNat < 2 ^ w) → acc < 2 ^ (w * c) →
    ∀ j', j ≤ j' → j' < k →
      (∀ e < n, ent w (T j') e = (L.toArray[n * j' + e]!).toNat) ∧ T j' < 2 ^ (w * n)
  | [], j, c, acc, h, _, _, _, _, _, j', hj, hk => by
    change bAnd(Nat.beq j k, Nat.beq c (nat_lit 0)) = true at h
    rw [bAnd_iff, Nat.beq_eq] at h
    omega
  | x :: rest, j, c, acc, h, hd, hc, hF, hv, hacc, j', hj, hk => by
    have hjk : Nat.beq j k = false := Bool.eq_false_iff.2 (by rw [Ne, Nat.beq_eq]; omega)
    change bIf(Nat.beq j k, true,
      strictB (natOf w x) (fun v => bAnd(Nat.blt v (Nat.shiftLeft (nat_lit 1) w),
        strictB (Nat.lor acc (Nat.shiftLeft v (Nat.mul w c))) (fun acc' =>
          bIf(Nat.beq (Nat.succ c) n,
            bAnd(Nat.beq acc' (T j), run w n k T rest (Nat.succ j) (nat_lit 0) (nat_lit 0)),
            run w n k T rest j (Nat.succ c) acc'))))) = true at h
    rw [hjk, strictB_eqP, bAnd_iff, strictB_eqP] at h
    obtain ⟨hlt, h⟩ := h
    have hw : Nat.shiftLeft 1 w = 2 ^ w := by rw [shl_eq, Nat.one_mul]
    rw [hw, Nat.blt_eq] at hlt
    have hx : natOf w x = (L.toArray[n * j + c]!).toNat := by
      rw [toArr_get hd]
      cases x with
      | ofNat v => rfl
      | negSucc m =>
        change Nat.shiftLeft 1 w < 2 ^ w at hlt
        rw [hw] at hlt
        omega
    have hv' : ∀ e < c + 1, (L.toArray[n * j + e]!).toNat < 2 ^ w := by
      intro e he
      rcases Nat.lt_or_ge e c with h1 | h1
      · exact hv e h1
      · have : e = c := by omega
        rw [this, ← hx]
        exact hlt
    have hF' : Fld w (Nat.lor acc (Nat.shiftLeft (natOf w x) (Nat.mul w c)))
        (fun e => if e < c + 1 then (L.toArray[n * j + e]!).toNat else 0) := by
      refine fld_congr (fld_or hF (fld_shl c (fld_one hlt))) fun e => ?_
      by_cases h1 : e < c
      · have h2 : ¬ c ≤ e := by omega
        simp [h1, h2, Nat.lt_succ_of_lt h1]
      · by_cases h2 : e = c
        · subst h2
          simp [hx]
        · have h3 : ¬ e < c + 1 := by omega
          have h4 : e - c ≠ 0 := by omega
          simp [h1, h3, h4]
    have hacc' : Nat.lor acc (Nat.shiftLeft (natOf w x) (Nat.mul w c)) < 2 ^ (w * (c + 1)) := by
      refine Nat.or_lt_two_pow (Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_left w (Nat.le_succ c)))) ?_
      change natOf w x <<< (w * c) < _
      rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm (2 ^ (w * c))]
      exact Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
    have hd' : L.drop (n * j + c + 1) = rest := drop_succ hd
    by_cases hn : c + 1 = n
    · have e1 : Nat.beq (Nat.succ c) n = true := by rw [Nat.beq_eq]; exact hn
      rw [e1, bAnd_iff, Nat.beq_eq] at h
      obtain ⟨hT, h⟩ := h
      rcases Nat.lt_or_ge j j' with hjj | hjj
      · refine run_sound rest (j + 1) 0 0 h ?_ (by omega) (fld_congr (fld_zero w) (by simp))
          (by simp) (by simp) j' hjj hk
        rw [← hd', Nat.add_zero, Nat.mul_succ, ← hn, Nat.add_assoc]
      · have : j' = j := by omega
        subst this
        rw [← hT]
        refine ⟨fun e he => ?_, by rw [← hn]; exact hacc'⟩
        rw [ent_eq, pg_of_fld hF' (by simp only [hn, he, ↓reduceIte]; exact hv' e (by omega))]
        simp [hn, he]
    · have e1 : Nat.beq (Nat.succ c) n = false := Bool.eq_false_iff.2 (by rw [Ne, Nat.beq_eq]; omega)
      rw [e1] at h
      exact run_sound rest j (c + 1) _ h (by rw [← Nat.add_assoc]; exact hd') (by omega) hF' hv'
        hacc' j' hj hk

private theorem permsK_fields {w n k : Nat} {L : List Int} {T : Nat → Nat}
    (h : permsK w n k L T = true) : ∀ j < k,
      (∀ e < n, ent w (T j) e = (L.toArray[n * j + e]!).toNat) ∧ T j < 2 ^ (w * n) := by
  intro j hj
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exfalso
    have key : ∀ (rest : List Int) (c acc : Nat), run w 0 k T rest 0 c acc = false := by
      intro rest
      induction rest with
      | nil =>
        intro c acc
        change bAnd(Nat.beq 0 k, Nat.beq c (nat_lit 0)) = false
        have : Nat.beq 0 k = false := Bool.eq_false_iff.2 (by rw [Ne, Nat.beq_eq]; omega)
        rw [this]
      | cons x rest ih =>
        intro c acc
        change bIf(Nat.beq 0 k, true,
          strictB (natOf w x) (fun v => bAnd(Nat.blt v (Nat.shiftLeft (nat_lit 1) w),
            strictB (Nat.lor acc (Nat.shiftLeft v (Nat.mul w c))) (fun acc' =>
              bIf(Nat.beq (Nat.succ c) 0,
                bAnd(Nat.beq acc' (T 0), run w 0 k T rest (Nat.succ 0) (nat_lit 0) (nat_lit 0)),
                run w 0 k T rest 0 (Nat.succ c) acc'))))) = false
        have : Nat.beq 0 k = false := Bool.eq_false_iff.2 (by rw [Ne, Nat.beq_eq]; omega)
        rw [this, strictB_eqP, strictB_eqP]
        have e2 : Nat.beq (Nat.succ c) 0 = false := rfl
        rw [e2, ih]
        cases Nat.blt (natOf w x) (Nat.shiftLeft 1 w) <;> rfl
    have h' : run w 0 k T L 0 0 0 = true := h
    rw [key] at h'
    exact Bool.false_ne_true h'
  · exact run_sound L 0 0 0 h (by simp) hn (fld_congr (fld_zero w) (by simp)) (by simp)
      (by simp) j (Nat.zero_le _) hj

theorem permsK_sound {w n k : Nat} {L : List Int} {T : Nat → Nat} (h : permsK w n k L T = true) :
    (tokPerms n L.toArray 0 k).1.size = k ∧
      ∀ j < k, (tokPerms n L.toArray 0 k).1[j]! = unpackW w n (T j) := by
  refine ⟨by simp [tokPerms], fun j hj => ?_⟩
  have hf := (permsK_fields h j hj).1
  simp only [tokPerms]
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  apply Array.ext
  · simp [tokNats, unpackW]
  · intro e h1 _
    have he : e < n := by simpa [tokNats] using h1
    simp [tokNats, unpackW, hf e he]

theorem natsK_sound {w k : Nat} {L : List Int} {T : Nat → Nat} (h : permsK w 1 k L T = true) :
    tokNats L.toArray 0 k = tabA k T := by
  apply Array.ext
  · simp [tokNats, tabA]
  · intro j h1 _
    have hj : j < k := by simpa [tokNats] using h1
    obtain ⟨hf, hlt⟩ := permsK_fields h j hj
    have e0 := hf 0 Nat.one_pos
    rw [ent_eq, Nat.one_mul, Nat.add_zero] at e0
    have e1 : pg w (mask w) (T j) 0 = T j := by
      rw [Nat.mul_one] at hlt
      have := pg_of_fld (w := w) (X := T j) (g := fun i => if i = 0 then T j else 0) (i := 0)
        (fld_one hlt) (by simpa using hlt)
      simpa using this
    rw [e1] at e0
    simp [tokNats, tabA, e0]

end CFSG.KS.SporSch.C11

end
