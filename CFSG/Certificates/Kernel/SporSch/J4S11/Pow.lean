module

public import Certificates.Data.Kernel.SporSch.J4S11
public import CFSG.Sporadic.Schreier.J4SElevenData
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.SporSch.J4SRunSound

public section

namespace CFSG.KS.SporSch.J4E.PowPf

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ
open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem get!_eq' (X : Array Nat) (i : Nat) : X[i]! = X[i]?.getD 0 := by
  by_cases h : i < X.size
  · rw [getElem!_pos X i h, getElem?_pos X i h, Option.getD_some]
  · rw [getElem!_neg X i h, getElem?_neg X i h, Option.getD_none]
    rfl

private theorem row_lt' {X : Array Nat} (hX : WfN X) {i : Nat} (hi : i < 112) :
    X[i]?.getD 0 < 2 ^ 112 := by
  rw [← get!_eq']
  exact hX.2 i hi

private theorem tb_unit (t n : Nat) : (1 <<< t).testBit n = decide (n = t) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : n = t
  · simp [h]
  · simp [h, Ne.symm h]

private theorem foldl_unit (R : Array Nat) (t : Nat) : ∀ (n : Nat),
    (List.range n).foldl (fun acc j => if (1 <<< t).testBit j then acc ^^^ (R[j]?.getD 0) else acc) 0 =
      if t < n then R[t]?.getD 0 else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_unit R t n, List.foldl_cons, List.foldl_nil,
      tb_unit]
    by_cases h : n = t
    · subst h
      simp
    · have h' : ¬ t = n := fun e => h e.symm
      simp only [h, decide_false, Bool.false_eq_true, if_false]
      by_cases ht : t < n
      · simp [ht, show t < n + 1 by omega]
      · simp [ht, show ¬ t < n + 1 by omega, show t ≠ n from h']

private theorem vec_unit {Z : Array Nat} {t : Nat} (ht : t < 112) :
    vecMulN 112 Z (1 <<< t) = Z[t]?.getD 0 := by
  unfold vecMulN
  rw [foldl_unit]
  simp [ht]

private theorem vne_of_ne {a b : Nat} (ha : a < 2 ^ 112) (hb : b < 2 ^ 112) (h : a ≠ b) :
    (List.range 112).any (fun j => a.testBit j != b.testBit j) = true := by
  rw [List.any_eq_true]
  by_contra hc
  apply h
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 112
  · by_contra hne
    exact hc ⟨j, List.mem_range.2 hj, by simpa [bne_iff_ne] using hne⟩
  · have h1 : a.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : b.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, h2]

theorem vne_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Z : Array Nat} (hZ : WfN Z)
    (h : notB (Nat.beq (vecJ rm (nat_lit 1) (encN Z)) (nat_lit 1)) = true) :
    O.vne (O.vmul (O.unit 0) Z) (O.unit 0) = true := by
  have hv : vecMulN 112 Z 1 = vecJ rm 1 (encN Z) := vec_enc hK hZ 1
  have hne : vecMulN 112 Z 1 ≠ 1 := by
    intro e
    rw [e] at hv
    have : Nat.beq (vecJ rm (nat_lit 1) (encN Z)) (nat_lit 1) = true := by
      rw [← hv]; exact Nat.beq_refl _
    rw [this] at h
    exact absurd h (by decide)
  have hz : vecMulN 112 Z (1 <<< 0) = Z[0]?.getD 0 := vec_unit (by omega)
  have hlt : vecMulN 112 Z 1 < 2 ^ 112 := by
    have := row_lt' hZ (i := 0) (by omega)
    rw [← hz] at this
    exact this
  have key := vne_of_ne hlt (Nat.one_lt_two_pow (n := 112) (by omega)) hne
  have hO : ∀ u w : Nat, O.vne u w = (List.range 112).any (fun j => u.testBit j != w.testBit j) :=
    fun u w => by
      simp only [O, ops2fr]
  have hV : O.vmul (O.unit 0) Z = vecMulN 112 Z (1 <<< 0) := by
    simp only [O, ops2fr]
  have hU : O.unit 0 = 1 <<< 0 := by
    simp only [O, ops2fr]
  have e2 : (1 : Nat) <<< 0 = 1 := Nat.shiftLeft_zero
  rw [hV, hU, hO, e2]
  exact key

private theorem beq_false' {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.J4Q.strictB y k = k y := by
  cases y <;> rfl

private theorem pow_one_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat}
    (hX : WfN X) {e : Nat} (h : Nat.beq (powJ c rm one (encN X) e) one = true) :
    O.eq (O.pow X e) O.one = true := by
  have m := pow_enc hK hX e
  have i := J4B.id_enc hK
  have e' : O.pow X e = idRows 112 :=
    enc_inj m.1 i.1 (by rw [m.2, i.2]; exact Nat.eq_of_beq_eq_true h)
  change (O.pow X e == idRows 112) = true
  rw [e']
  exact beq_self_eq_true _

theorem expK_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y Z : Array Nat}
    (hX : WfN X) (hY : WfN Y) (hZ : WfN Z)
    (h : expK c rm one (encN X) (encN Y) (encN Z) = true) : expOK X Y Z = true := by
  unfold expOK
  rw [List.all_eq_true]
  intro t ht
  have h1 := CFSG.KS.allN_spec h t (List.mem_range.1 ht)
  obtain ⟨wa, ea⟩ := pow_enc hK hX (t % 11)
  obtain ⟨wb, eb⟩ := pow_enc hK hY (t / 11 % 11)
  obtain ⟨wc, ec⟩ := pow_enc hK hZ (t / 121 % 11)
  have m1 := mul_enc hK wa wb
  have m2 := mul_enc hK m1.1 wc
  refine pow_one_sound' hK m2.1 ?_
  rw [m2.2, m1.2, ea, eb, ec]
  exact h1

private theorem ne_rowsDiffer {M N : Array Nat} (hM : WfN M) (hN : WfN N) (h : M ≠ N) :
    rowsDiffer M N = true := by
  have hex : ∃ t, t < 112 ∧ M[t]?.getD 0 ≠ N[t]?.getD 0 := by
    by_contra hne
    apply h
    apply Array.ext
    · rw [hM.1, hN.1]
    · intro i h1 h2
      have hi : i < 112 := by rw [hM.1] at h1; exact h1
      have : M[i]?.getD 0 = N[i]?.getD 0 := by
        by_contra hh
        exact hne ⟨i, hi, hh⟩
      rwa [getElem?_pos M i h1, getElem?_pos N i h2, Option.getD_some, Option.getD_some] at this
  obtain ⟨t, ht, hne⟩ := hex
  unfold rowsDiffer
  rw [List.any_eq_true]
  refine ⟨t, List.mem_range.2 ht, ?_⟩
  have hO : ∀ u w : Nat, O.vne u w = (List.range 112).any (fun j => u.testBit j != w.testBit j) :=
    fun u w => by simp only [O, ops2fr]
  have hV : ∀ (Z : Array Nat), O.vmul (O.unit t) Z = vecMulN 112 Z (1 <<< t) := fun Z => by
    simp only [O, ops2fr]
  rw [hO, hV, hV, vec_unit ht, vec_unit ht]
  exact vne_of_ne (row_lt' hM ht) (row_lt' hN ht) hne

private theorem notB_andB' {p q : Bool} (h : notB (andB p q) = true) : p = false ∨ q = false := by
  cases p <;> cases q <;> first
    | (left; rfl)
    | (right; rfl)
    | exact absurd h (by decide)

private theorem center_aux (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y A : Array Nat}
    (hX : WfN X) (hY : WfN Y) (hA : WfN A)
    (h : notB (andB (Nat.beq (mulJ c rm (encN A) (encN X)) (mulJ c rm (encN X) (encN A)))
      (Nat.beq (mulJ c rm (encN A) (encN Y)) (mulJ c rm (encN Y) (encN A)))) = true) :
    (rowsDiffer (O.mul A X) (O.mul X A) || rowsDiffer (O.mul A Y) (O.mul Y A)) = true := by
  rw [Bool.or_eq_true]
  rcases notB_andB' h with hp | hq
  · left
    refine ne_rowsDiffer (mul_enc hK hA hX).1 (mul_enc hK hX hA).1 ?_
    intro e
    have e2 := congrArg encN e
    rw [(mul_enc hK hA hX).2, (mul_enc hK hX hA).2] at e2
    rw [e2, Nat.beq_refl] at hp
    exact absurd hp (by decide)
  · right
    refine ne_rowsDiffer (mul_enc hK hA hY).1 (mul_enc hK hY hA).1 ?_
    intro e
    have e2 := congrArg encN e
    rw [(mul_enc hK hA hY).2, (mul_enc hK hY hA).2] at e2
    rw [e2, Nat.beq_refl] at hq
    exact absurd hq (by decide)

theorem centerK_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y : Array Nat}
    (hX : WfN X) (hY : WfN Y)
    (h : centerK c rm one (encN X) (encN Y) = true) : centerOK X Y = true := by
  unfold centerOK
  rw [List.all_eq_true]
  intro t ht
  have h1 := CFSG.KS.allN_spec h t (List.mem_range.1 ht)
  obtain ⟨wa, ea⟩ := pow_enc hK hX ((t + 1) % 11)
  obtain ⟨wb, eb⟩ := pow_enc hK hY ((t + 1) / 11 % 11)
  have mA := mul_enc hK wa wb
  rw [strictB_eq'] at h1
  dsimp only
  refine center_aux hK hX hY mA.1 ?_
  rw [mA.2, ea, eb]
  exact h1

end CFSG.KS.SporSch.J4E.PowPf

end
