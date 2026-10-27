module

public import Certificates.Data.Kernel.J4Q.Comm
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import CFSG.Sporadic.J4.QTOutCommNative

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.KC.Loop

section Prim

theorem enc_xorMat {X Y : Array V2} (_hX : WfA X) (_hY : WfA Y) :
    WfA (xorMat X Y) ∧ encR (xorMat X Y) = Nat.xor (encR X) (encR Y) := by
  have heq : xorMat X Y = CFSG.Sporadic.J4.QT2A.addRows X Y := by
    unfold xorMat CFSG.Sporadic.J4.QT2A.addRows
    apply congrArg (Array.ofFn (n := 112))
    funext i
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rfl
  rw [heq]
  exact enc_addRows _hX _hY

theorem enc_zeroMat : WfA zeroMat ∧ encR zeroMat = 0 := by
  constructor
  · refine ⟨by simp [zeroMat], Array.all_eq_true.mpr ?_⟩
    intro i hi
    simpa only [zeroMat, Array.getElem_replicate] using V2.zero_wf
  · have hz (i : Nat) : zeroMat.getD i V2.zero = V2.zero := by
      by_cases hi : i < 112 <;>
        simp [zeroMat, Array.getD_eq_getD_getElem?, hi]
    have hp : v2N V2.zero = 0 := by
      simp [v2N, V2.zero, Nat.lor_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    have hid : ∀ l : List Nat, l.foldr (fun _ acc => acc) 0 = 0 := by
      intro l
      induction l <;> simp_all
    unfold encR
    simpa only [hz, hp, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.zero_mul,
      Nat.lor_eq, Nat.zero_or] using hid (List.range 112)

theorem enc_toArray (l : List V2) (_hl : l.length = 112) (_hw : ∀ v ∈ l, v.wf = true) :
    WfA l.toArray ∧ encR l.toArray = rowsJ fun i => v2N (l.getD i V2.zero) := by
  have hf : ∀ i < 112, (l.getD i V2.zero).wf = true := by
    intro i hi
    have hli : i < l.length := by omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hli,
      Option.getD_some] using _hw l[i] (List.getElem_mem hli)
  have heq : (Array.ofFn (n := 112) fun i => l.getD i.val V2.zero) = l.toArray := by
    apply Array.ext (by simp [_hl])
    intro i hi hj
    have hli : i < l.length := by simpa only [List.size_toArray] using hj
    simp only [Array.getElem_ofFn, List.getElem_toArray, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hli, Option.getD_some]
  simpa only [heq] using enc_ofFn (fun i => l.getD i V2.zero) hf

theorem v2N_ofFn (f : Nat → Bool) : v2N (V2.ofFn f) = bitsJ f := by
  have hrepr (a : V2) : v2N a = a.toNat := by
    unfold v2N V2.toNat
    rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt a.lo) a.hi.toNat,
      Nat.shiftLeft_eq]
    omega
  let B (n : Nat) := Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.lor acc (Nat.shiftLeft 1 j)) (f j)) n
  have hb : ∀ n j, (B n).testBit j = if j < n then f j else false := by
    intro n
    induction n with
    | zero => intro j; simp [B]
    | succ n ih =>
      intro j
      change (Bool.rec (motive := fun _ => Nat) (B n)
        (Nat.lor (B n) (Nat.shiftLeft 1 n)) (f n)).testBit j = _
      cases hn : f n with
      | false =>
        change (B n).testBit j = _
        rw [ih]
        by_cases hj : j < n
        · simp [hj, show j < n + 1 by omega]
        · by_cases he : j = n
          · subst j; simp [hn]
          · simp [hj, show ¬j < n + 1 by omega]
      | true =>
        change (Nat.lor (B n) (Nat.shiftLeft 1 n)).testBit j = _
        rw [Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', Nat.one_shiftLeft,
          Nat.testBit_two_pow, ih]
        by_cases hj : j < n
        · simp [hj, show j < n + 1 by omega, show n ≠ j by omega]
        · by_cases he : j = n
          · subst j; simp [hn]
          · simp [hj, show ¬j < n + 1 by omega, show n ≠ j by omega]
  have hlt : v2N (V2.ofFn f) < 2 ^ 112 := by
    rw [hrepr]
    exact (V2.wf_iff_toNat_lt _).1 (V2.ofFn_wf f)
  apply Nat.eq_of_testBit_eq
  intro j
  change (v2N (V2.ofFn f)).testBit j = (B 112).testBit j
  rw [hb]
  by_cases hj : j < 112
  · have hv : (V2.ofFn f).testBit j = f j := by
      have hv' := V2.toVec_ofFn f ⟨j, hj⟩
      rw [V2.toVec_apply] at hv'
      cases h1 : (V2.ofFn f).testBit j <;> cases h2 : f j <;>
        simp [h1, h2] at hv' ⊢
    rw [if_pos hj, ← testBit_v2N _ (by omega)]
    exact hv
  · rw [if_neg hj, Nat.testBit_lt_two_pow
      (hlt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem wf_ofFn (f : Nat → Bool) : (V2.ofFn f).wf = true := by
  exact CFSG.Sporadic.J4.Native.V2.ofFn_wf f

end Prim

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem enc_powFuel (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    ∀ (fuel : Nat) (M : Array V2) (m e : Nat), WfA M ∧ encR M = m →
      WfA (powFuel M fuel e) ∧ encR (powFuel M fuel e) = powFuelK c rm one fuel m e
  | 0, _, _, _, _ => id_enc hK
  | fuel + 1, M, m, e, hM => by
    rw [powFuel]
    by_cases he : e = 0
    · subst he
      exact id_enc hK
    · have hb : Nat.beq e 0 = false := nbeq_false he
      have ih := enc_powFuel hK fuel (mulRows M M) (mulJ c rm m m) (e / 2) (mul_enc hK hM hM)
      change _ ∧ _ = Bool.rec (motive := fun _ => Nat)
        (strictN (powFuelK c rm one fuel (mulJ c rm m m) (Nat.div e 2)) fun r =>
          Bool.rec (motive := fun _ => Nat) r (mulJ c rm m r) (Nat.beq (Nat.mod e 2) 1)) one (Nat.beq e 0)
      rw [hb, strictN_eq]
      simp only [he, ↓reduceIte]
      by_cases h2 : e % 2 = 1
      · have : Nat.beq (Nat.mod e 2) 1 = true := by
          rw [Nat.beq_eq]
          exact h2
        simp only [h2, ↓reduceIte]
        rw [this]
        exact mul_enc hK hM ih
      · have : Nat.beq (Nat.mod e 2) 1 = false := nbeq_false h2
        simp only [h2, ↓reduceIte]
        rw [this]
        exact ih

end CFSG.KC.J4Q

end
