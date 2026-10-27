module

public import Certificates.Data.Kernel.SporSch.J1Vec
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.SporSch.J1Vec

open CFSG.KC.Enum CFSG.KS

private theorem bIf_false_of_true {c : Bool}
    (h : Bool.rec (motive := fun _ => Bool) true false c = true) : c = false := by
  cases c <;> simp_all

private theorem rowK_nil (v : Nat) (j : Nat) : rowK v [] j = Nat.beq j 7 := rfl

private theorem rowK_cons (v a : Nat) (x : List Nat) (j : Nat) :
    rowK v (a :: x) j =
      bAnd(Nat.blt a 11, bAnd(Nat.beq a (vf v j), rowK v x (j + 1))) := rfl

private theorem rowK_sound {v : Nat} {x : List Nat} {j : Nat} (h : rowK v x j = true) :
    x.length + j = 7 ∧
      ∀ t < x.length, x.getD t 0 < 11 ∧ x.getD t 0 = vf v (j + t) := by
  induction x generalizing j with
  | nil =>
    rw [rowK_nil, Nat.beq_eq] at h
    refine ⟨by simpa using h, ?_⟩
    intro t ht
    exact absurd ht (Nat.not_lt_zero t)
  | cons a x ih =>
    rw [rowK_cons] at h
    obtain ⟨ha, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨haeq, hrest⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    have ha' : a < 11 := by rwa [Nat.blt_eq] at ha
    have hae' : a = vf v j := Nat.eq_of_beq_eq_true haeq
    obtain ⟨hlen, hspec⟩ := ih hrest
    refine ⟨by simp; omega, ?_⟩
    intro t ht
    cases t with
    | zero =>
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact ⟨ha', by simpa using hae'⟩
    | succ t =>
      have htx : t < x.length := by simpa using ht
      obtain ⟨hlt, heq⟩ := hspec t htx
      exact ⟨by simpa using hlt,
        by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq⟩

private theorem vbindFrom_nil (VT : Nat → Nat) (i N : Nat) :
    vbindFrom VT [] i N = Nat.beq i N := rfl

private theorem vbindFrom_cons (VT : Nat → Nat) (x : List Nat) (xs : List (List Nat))
    (i N : Nat) :
    vbindFrom VT (x :: xs) i N =
      strictB (VT i) (fun v =>
        bAnd(Nat.beq (Nat.shiftRight v 28) 0,
          bAnd(rowK v x 0, vbindFrom VT xs (i + 1) N))) := rfl

private theorem vbindFrom_sound {VT : Nat → Nat} {L : List (List Nat)} {i N : Nat}
    (h : vbindFrom VT L i N = true) :
    i + L.length = N ∧
      ∀ k < L.length,
        (L.getD k []).length = 7 ∧
          (∀ j < 7, (L.getD k []).getD j 0 = vf (VT (i + k)) j) ∧
            Nat.shiftRight (VT (i + k)) 28 = 0 := by
  induction L generalizing i N with
  | nil =>
    rw [vbindFrom_nil, Nat.beq_eq] at h
    refine ⟨by simpa using h, ?_⟩
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  | cons x xs ih =>
    rw [vbindFrom_cons, CFSG.KS.PackFld.strictB_eqP] at h
    obtain ⟨hshift, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨hrow, hrest⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    have hshift' : Nat.shiftRight (VT i) 28 = 0 := Nat.eq_of_beq_eq_true hshift
    obtain ⟨hxlen, hxspec⟩ := rowK_sound hrow
    obtain ⟨hlen, hspec⟩ := ih hrest
    refine ⟨by simp; omega, ?_⟩
    intro k hk
    cases k with
    | zero =>
      refine ⟨by simpa using hxlen, ?_, by simpa using hshift'⟩
      intro j hj
      have hjx : j < x.length := by omega
      have hxj := hxspec j hjx
      simpa using hxj.2
    | succ k =>
      have hkx : k < xs.length := by simpa using hk
      obtain ⟨hkl, hkf, hks⟩ := hspec k hkx
      refine ⟨by simpa using hkl, ?_, ?_⟩
      · intro j hj
        have hkj := hkf j hj
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkj
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hks

theorem vbindK_sound {L : List (List Nat)} {VT : Nat → Nat} {N : Nat} (h : vbindK L VT N = true) :
    L.length = N ∧ ∀ i < N, (L.getD i []).length = 7 ∧
      (∀ j < 7, (L.getD i []).getD j 0 = vf (VT i) j) ∧ Nat.shiftRight (VT i) 28 = 0 := by
  obtain ⟨hlen, hspec⟩ := vbindFrom_sound h
  have hN : L.length = N := by simpa using hlen
  refine ⟨hN, ?_⟩
  intro i hi
  have hiL : i < L.length := by omega
  obtain ⟨hil, hif, his⟩ := hspec i hiL
  exact ⟨hil, by simpa using hif, by simpa using his⟩

private theorem vf_eq_pg (v j : Nat) : vf v j = pg 4 (mask 4) v j := by
  unfold vf pg
  rw [CFSG.KS.PackFld.mask_eq]

private theorem fld_vf (v : Nat) : CFSG.KS.PackFld.Fld 4 v (vf v) := by
  intro j k hk
  rw [vf_eq_pg, CFSG.KS.PackFld.testBit_pgM]
  simp [hk]

private theorem lt_two_pow_of_shiftRight_eq_zero {v n : Nat}
    (h : Nat.shiftRight v n = 0) : v < 2 ^ n := by
  change v >>> n = 0 at h
  rw [Nat.shiftRight_eq_div_pow v n] at h
  exact Nat.lt_of_div_eq_zero (Nat.two_pow_pos n) h

private theorem eq_of_vf_eq {v w : Nat} (hv : Nat.shiftRight v 28 = 0)
    (hw : Nat.shiftRight w 28 = 0) (h : ∀ j < 7, vf v j = vf w j) : v = w := by
  have hvlt : v < 2 ^ 28 := lt_two_pow_of_shiftRight_eq_zero hv
  have hwlt : w < 2 ^ 28 := lt_two_pow_of_shiftRight_eq_zero hw
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 28
  · have hq : k / 4 < 7 := by omega
    have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have e1 := fld_vf v (k / 4) (k % 4) hr
    have e2 := fld_vf w (k / 4) (k % 4) hr
    rw [h (k / 4) hq] at e1
    have hk' : 4 * (k / 4) + k % 4 = k := Nat.div_add_mod k 4
    rw [hk'] at e1 e2
    rw [e1, e2]
  · have hk28 : 28 ≤ k := by omega
    have hv0 : v.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hvlt (Nat.pow_le_pow_right (by norm_num) hk28))
    have hw0 : w.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hwlt (Nat.pow_le_pow_right (by norm_num) hk28))
    rw [hv0, hw0]

private theorem sortFrom_nil (VT : Nat → Nat) (N c M prev : Nat) :
    sortFrom VT N [] c M prev = Nat.beq c N := rfl

private theorem sortFrom_cons (VT : Nat → Nat) (N k : Nat) (O : List Nat) (c M prev : Nat) :
    sortFrom VT N (k :: O) c M prev =
      strictB (VT k) (fun v =>
        bAnd(Nat.blt k N,
          bAnd(bIf(hasBit M k, false, true),
            bAnd(Nat.blt prev (Nat.succ v),
              strictB (Nat.lor M (Nat.shiftLeft (nat_lit 1) k))
                (fun M' => sortFrom VT N O (Nat.succ c) M' (Nat.succ v)))))) := rfl

private theorem hasBit_eq (M l : Nat) : hasBit M l = M.testBit l := by
  have e1 : Nat.shiftLeft 1 l = 2 ^ l := Nat.one_shiftLeft l
  change Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 l)) = M.testBit l
  rw [e1]
  cases hM : M.testBit l with
  | false =>
    have h0 : Nat.land M (2 ^ l) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      change (M &&& 2 ^ l).testBit i = (0 : Nat).testBit i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hli : l = i
      · subst hli
        simp [hM]
      · simp [hli]
    rw [h0]
    rfl
  | true =>
    have h1 : Nat.land M (2 ^ l) = 2 ^ l := by
      apply Nat.eq_of_testBit_eq
      intro i
      change (M &&& 2 ^ l).testBit i = (2 ^ l).testBit i
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hli : l = i
      · subst hli
        simp [hM]
      · simp [hli]
    rw [h1, Nat.blt_eq]
    exact Nat.two_pow_pos l

private theorem hasBit_lor_left {M M' x : Nat} (h : hasBit M x = true) :
    hasBit (Nat.lor M M') x = true := by
  rw [hasBit_eq] at h ⊢
  change (M ||| M').testBit x = true
  rw [Nat.testBit_or]
  simp [h]

private theorem hasBit_lor_self (M k : Nat) :
    hasBit (Nat.lor M (Nat.shiftLeft 1 k)) k = true := by
  rw [hasBit_eq]
  change (M ||| 1 <<< k).testBit k = true
  rw [Nat.testBit_or, Nat.one_shiftLeft]
  simp [Nat.testBit_two_pow]

private theorem sortFrom_mask {VT : Nat → Nat} {N : Nat} {O : List Nat} {c M prev : Nat}
    (h : sortFrom VT N O c M prev = true) :
    (∀ x ∈ O, hasBit M x = false) ∧
      (∀ P : List Nat, (∀ x ∈ P, hasBit M x = true) → O.Nodup) := by
  induction O generalizing c M prev with
  | nil => exact ⟨by simp, fun P hP => List.nodup_nil⟩
  | cons k O ih =>
    rw [sortFrom_cons, CFSG.KS.PackFld.strictB_eqP] at h
    obtain ⟨-, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨hfresh, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    obtain ⟨-, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h3
    have hbk : hasBit M k = false := bIf_false_of_true hfresh
    rw [CFSG.KS.PackFld.strictB_eqP] at h4
    obtain ⟨hfalse, hnodup⟩ := ih h4
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hxO
      · exact hbk
      · cases hbM : hasBit M x with
        | false => rfl
        | true =>
          have hxM' : hasBit (Nat.lor M (Nat.shiftLeft 1 k)) x = true := hasBit_lor_left hbM
          have hxM := hfalse x hxO
          rw [hxM'] at hxM
          exact Bool.noConfusion hxM
    · intro P hP
      have hP' : ∀ x ∈ P ++ [k], hasBit (Nat.lor M (Nat.shiftLeft 1 k)) x = true := by
        intro x hx
        rcases List.mem_append.1 hx with hxP | hxk
        · exact hasBit_lor_left (hP x hxP)
        · have hxk' : x = k := by simpa using hxk
          rw [hxk']
          exact hasBit_lor_self M k
      have hOnd := hnodup (P ++ [k]) hP'
      refine List.nodup_cons.2 ⟨?_, hOnd⟩
      intro hkO
      have hfalsek := hfalse k hkO
      rw [hasBit_lor_self M k] at hfalsek
      exact Bool.noConfusion hfalsek

private theorem sortFrom_spec {VT : Nat → Nat} {N : Nat} {O : List Nat} {c M prev : Nat}
    (h : sortFrom VT N O c M prev = true) :
    c + O.length = N ∧ (∀ x ∈ O, x < N) ∧
      O.Pairwise (fun a b => VT a < VT b) ∧ (∀ x ∈ O, prev ≤ VT x) := by
  induction O generalizing c M prev with
  | nil =>
    rw [sortFrom_nil, Nat.beq_eq] at h
    refine ⟨by simpa using h, by simp, List.Pairwise.nil, by simp⟩
  | cons k O ih =>
    rw [sortFrom_cons, CFSG.KS.PackFld.strictB_eqP] at h
    obtain ⟨hk, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨-, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    obtain ⟨hprev, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h3
    have hk' : k < N := by rwa [Nat.blt_eq] at hk
    have hpv : prev ≤ VT k := by
      have := hprev
      rw [Nat.blt_eq] at this
      omega
    rw [CFSG.KS.PackFld.strictB_eqP] at h4
    obtain ⟨hlen, hlt, hpair, htail⟩ := ih h4
    refine ⟨by simp; omega, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hxO
      · exact hk'
      · exact hlt x hxO
    · refine List.pairwise_cons.2 ⟨?_, hpair⟩
      intro x hx
      have := htail x hx
      omega
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hxO
      · exact hpv
      · have := htail x hxO
        omega

private theorem sortK_spec {VT : Nat → Nat} {O : List Nat} {N : Nat}
    (h : sortK VT O N = true) :
    O.length = N ∧ O.Nodup ∧ (∀ x ∈ O, x < N) ∧
      O.Pairwise (fun a b => VT a < VT b) := by
  have hs := sortFrom_spec h
  have hlen : O.length = N := by simpa using hs.1
  exact ⟨hlen, (sortFrom_mask h).2 [] (by simp), hs.2.1, hs.2.2.1⟩

private theorem mem_of_nodup_length {O : List Nat} {N : Nat} (hnd : O.Nodup)
    (hlen : O.length = N) (hlt : ∀ x ∈ O, x < N) : ∀ i < N, i ∈ O := by
  intro i hi
  have hsub : O.toFinset ⊆ Finset.range N := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.2 (hlt x hx)
  have hcard : O.toFinset.card = N := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq : O.toFinset = Finset.range N := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard, Finset.card_range]
  have hi' : i ∈ O.toFinset := by
    rw [heq]
    exact Finset.mem_range.2 hi
  exact List.mem_toFinset.1 hi'

theorem nodup_sound {L : List (List Nat)} {VT : Nat → Nat} {N : Nat} {O : List Nat}
    (hb : vbindK L VT N = true) (hs : sortK VT O N = true) : L.Nodup := by
  obtain ⟨hlen, hvb⟩ := vbindK_sound hb
  obtain ⟨hlenO, hndO, hltO, hpairO⟩ := sortK_spec hs
  have hmem : ∀ i < N, i ∈ O := mem_of_nodup_length hndO hlenO hltO
  have hVT_inj : ∀ i j, i < N → j < N → VT i = VT j → i = j := by
    intro i j hi hj hij
    obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.1 (hmem i hi)
    obtain ⟨q, hq, hqe⟩ := List.mem_iff_getElem.1 (hmem j hj)
    have hpq : p = q := by
      rcases Nat.lt_trichotomy p q with hlt | heq | hgt
      · have hrel := hpairO.rel_getElem_of_lt hp hq hlt
        rw [hpe, hqe] at hrel
        omega
      · exact heq
      · have hrel := hpairO.rel_getElem_of_lt hq hp hgt
        rw [hpe, hqe] at hrel
        omega
    subst hpq
    exact hpe.symm.trans hqe
  rw [List.nodup_iff_injective_getElem]
  intro a b hab
  have haN : a.val < N := by rw [← hlen]; exact a.isLt
  have hbN : b.val < N := by rw [← hlen]; exact b.isLt
  change L[a.val] = L[b.val] at hab
  have hget : ∀ j < 7, vf (VT a.val) j = vf (VT b.val) j := by
    intro j hj
    have ha' := (hvb a.val haN).2.1 j hj
    have hb' := (hvb b.val hbN).2.1 j hj
    rw [List.getD_eq_getElem (l := L) (d := []) a.isLt] at ha'
    rw [List.getD_eq_getElem (l := L) (d := []) b.isLt] at hb'
    rw [hab] at ha'
    exact ha'.symm.trans hb'
  have hVT : VT a.val = VT b.val :=
    eq_of_vf_eq (hvb a.val haN).2.2 (hvb b.val hbN).2.2 hget
  exact Fin.ext (hVT_inj a.val b.val haN hbN hVT)

theorem nzK_sound {VT : Nat → Nat} {N : Nat} (h : nzK VT N = true) :
    ∀ i < N, (fun j : Fin 7 => ((vf (VT i) j : Nat) : ZMod 11)) ≠ 0 := by
  intro i hi hzero
  have hi' := CFSG.KS.allN_spec h i hi
  rw [CFSG.KS.PackFld.strictB_eqP] at hi'
  obtain ⟨hshift, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 hi'
  obtain ⟨hpos, hfields⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  have hshift0 : Nat.shiftRight (VT i) 28 = 0 := Nat.eq_of_beq_eq_true hshift
  have hpos' : 0 < VT i := by rwa [Nat.blt_eq] at hpos
  have hfields' : ∀ j < 7, vf (VT i) j < 11 := by
    intro j hj
    have := CFSG.KS.allN_spec hfields j hj
    rwa [Nat.blt_eq] at this
  have hex : ∃ j < 7, vf (VT i) j ≠ 0 := by
    by_contra hcon
    have hall : ∀ j < 7, vf (VT i) j = 0 := by
      intro j hj
      by_contra hne
      exact hcon ⟨j, hj, hne⟩
    have hz : VT i = 0 := by
      refine eq_of_vf_eq hshift0 (by norm_num) (fun j hj => ?_)
      rw [hall j hj]
      simp [vf]
    omega
  obtain ⟨j, hj, hne⟩ := hex
  have hcomp : ((vf (VT i) j : Nat) : ZMod 11) ≠ 0 := by
    intro hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    exact hne (Nat.eq_zero_of_dvd_of_lt hz (hfields' j hj))
  exact hcomp (congrFun hzero ⟨j, hj⟩)

private theorem foldBlk_succ (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) :
    foldBlk b f (len + 1) s = foldBlk b f len (f (b + len) s) := by
  change strictN (f (b + len) s) (foldBlk b f len) = _
  rw [CFSG.KS.PackFld.strictN_eqP]

private theorem foldN_seven (f : Nat → Nat → Nat) (s : Nat) :
    foldN 7 f s = foldBlk 0 f 7 s := by
  have hshift : Nat.shiftRight 7 6 = 0 := by decide
  have hland : Nat.land 7 63 = 7 := by decide
  unfold foldN
  rw [hshift, hland]
  change foldBlk 0 f 7 s = foldBlk 0 f 7 s
  rfl

private theorem add_swap (a b c : Nat) : (a + b) + c = a + (c + b) := by omega

private theorem foldBlk_add (MP v r : Nat) :
    ∀ (b len s : Nat),
      foldBlk b (fun c s => Nat.add s (Nat.mul (me MP r c) (vf v c))) len s =
        Nat.add s (∑ c ∈ Finset.range len, Nat.mul (me MP r (b + c)) (vf v (b + c)))
  | b, 0, s => by
    rw [show foldBlk b (fun c s => Nat.add s (Nat.mul (me MP r c) (vf v c))) 0 s = s from rfl]
    simp
  | b, len + 1, s => by
    rw [foldBlk_succ,
      foldBlk_add MP v r b len
        (Nat.add s (Nat.mul (me MP r (b + len)) (vf v (b + len)))),
      Finset.sum_range_succ]
    exact add_swap _ _ _

private theorem dotK_eq_sum (MP v r : Nat) :
    dotK MP v r = (∑ c ∈ Finset.range 7, Nat.mul (me MP r c) (vf v c)) % 11 := by
  unfold dotK
  rw [foldN_seven]
  change (foldBlk 0 (fun c s => Nat.add s (Nat.mul (me MP r c) (vf v c))) 7 0) % 11 =
    (∑ c ∈ Finset.range 7, Nat.mul (me MP r c) (vf v c)) % 11
  rw [foldBlk_add MP v r]
  simp

private theorem dotK_lt (MP v r : Nat) : dotK MP v r < 16 := by
  unfold dotK
  have h := Nat.mod_lt
    (foldN 7 (fun c s => Nat.add s (Nat.mul (me MP r c) (vf v c))) 0)
    (by norm_num : 0 < 11)
  exact lt_of_lt_of_le h (by norm_num : 11 ≤ 16)

private theorem fld_foldBlk_mul (g : Nat → Nat) (hg : ∀ r, g r < 16) :
    ∀ (b len : Nat) (s : Nat) (gs : Nat → Nat),
      CFSG.KS.PackFld.Fld 4 s gs →
      CFSG.KS.PackFld.Fld 4
        (foldBlk b (fun r s => Nat.lor s (Nat.shiftLeft (g r) (4 * r))) len s)
        (fun i => if b ≤ i ∧ i < b + len then gs i ||| g i else gs i)
  | b, 0, s, gs, hs => by
    refine CFSG.KS.PackFld.fld_congr hs (fun i => ?_)
    have hi : ¬ (b ≤ i ∧ i < b + 0) := by omega
    simp [hi]
  | b, len + 1, s, gs, hs => by
    rw [foldBlk_succ]
    set s' : Nat := Nat.lor s (Nat.shiftLeft (g (b + len)) (4 * (b + len))) with hs'def
    set gs' : Nat → Nat := fun i => gs i ||| (if i = b + len then g (b + len) else 0)
      with hgs'def
    have hsingle : CFSG.KS.PackFld.Fld 4 (g (b + len))
        (fun i => if i = 0 then g (b + len) else 0) :=
      CFSG.KS.PackFld.fld_one (hg (b + len))
    have hshift : CFSG.KS.PackFld.Fld 4 (Nat.shiftLeft (g (b + len)) (4 * (b + len)))
        (fun i => if i = b + len then g (b + len) else 0) := by
      refine CFSG.KS.PackFld.fld_congr
        (CFSG.KS.PackFld.fld_shl (b + len) hsingle) (fun i => ?_)
      by_cases hi : i = b + len
      · subst hi
        simp
      · by_cases hle : b + len ≤ i
        · have hne : i - (b + len) ≠ 0 := by omega
          simp [hi, hle, hne]
        · simp [hi, hle]
    have hs' : CFSG.KS.PackFld.Fld 4 s' gs' := by
      rw [hs'def, hgs'def]
      exact CFSG.KS.PackFld.fld_or hs hshift
    have ih := fld_foldBlk_mul g hg b len s' gs' hs'
    refine CFSG.KS.PackFld.fld_congr ih (fun i => ?_)
    by_cases hi : i = b + len
    · subst hi
      simp [hgs'def]
    · have hgs'i : gs' i = gs i := by simp [hgs'def, hi]
      rw [hgs'i]
      by_cases hlt : i < b + len
      · have hlt' : i < b + (len + 1) := by omega
        simp [hlt, hlt']
      · have hlt' : ¬ i < b + (len + 1) := by omega
        simp [hlt, hlt']

private theorem fld_mulK (MP v : Nat) :
    CFSG.KS.PackFld.Fld 4 (mulK MP v) (fun i => if i < 7 then dotK MP v i else 0) := by
  have h := fld_foldBlk_mul (fun i => dotK MP v i) (fun i => dotK_lt MP v i) 0 7 0
    (fun _ => 0) (CFSG.KS.PackFld.fld_zero 4)
  have hmul : mulK MP v =
      foldBlk 0 (fun r s => Nat.lor s (Nat.shiftLeft (dotK MP v r) (4 * r))) 7 0 := by
    unfold mulK
    exact foldN_seven _ _
  rw [hmul]
  refine CFSG.KS.PackFld.fld_congr h (fun i => ?_)
  by_cases hi : i < 7 <;> simp [hi]

private theorem vf_mulK (MP v : Nat) {j : Nat} (hj : j < 7) :
    vf (mulK MP v) j = dotK MP v j := by
  rw [vf_eq_pg]
  have h := CFSG.KS.PackFld.pg_of_fld (X := mulK MP v) (i := j)
    (g := fun i => if i < 7 then dotK MP v i else 0) (fld_mulK MP v)
    (by simpa [hj] using dotK_lt MP v j)
  simpa [hj] using h

theorem mvK_sound {MP : Nat} {VT : Nat → Nat} {P N : Nat} {M : Matrix (Fin 7) (Fin 7) (ZMod 11)}
    (hM : ∀ r c : Fin 7, M r c = ((me MP r c : Nat) : ZMod 11)) (h : mvK MP VT P N = true) :
    ∀ i < N, M.mulVec (fun j : Fin 7 => ((vf (VT i) j : Nat) : ZMod 11)) =
      fun j : Fin 7 => ((vf (VT (pg 12 (mask 12) P i)) j : Nat) : ZMod 11) := by
  intro i hi
  have hbeq := CFSG.KS.allN_spec h i hi
  have hcode : mulK MP (VT i) = VT (pg 12 (mask 12) P i) := Nat.eq_of_beq_eq_true hbeq
  funext r
  rw [Matrix.mulVec_apply_eq_sum]
  have hcast : (∑ j : Fin 7, M r j * ((vf (VT i) j : Nat) : ZMod 11)) =
      ((∑ j : Fin 7, me MP r j * vf (VT i) j : Nat) : ZMod 11) := by
    have hterm : ∀ j : Fin 7, M r j * ((vf (VT i) j : Nat) : ZMod 11) =
        ((me MP r j * vf (VT i) j : Nat) : ZMod 11) := by
      intro j
      rw [hM r j, ← Nat.cast_mul]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [← Nat.cast_sum]
  rw [hcast]
  have hvf : vf (VT (pg 12 (mask 12) P i)) r.val = dotK MP (VT i) r.val := by
    rw [← hcode]
    exact vf_mulK MP (VT i) r.isLt
  rw [hvf, dotK_eq_sum, ZMod.natCast_mod]
  rw [Finset.sum_range]
  rfl

end CFSG.KS.SporSch.J1Vec

end
