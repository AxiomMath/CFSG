module

public import Certificates.Data.Kernel.Spor.ONKWAB
public import CFSG.Certificates.Kernel.Spor.ONKWSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option exponentiation.threshold 600

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

theorem abTbHi {a i : Nat} (ha : a < 2 ^ 256) (hi : 256 ≤ i) : a.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hi))

theorem abAddP_lt {a b c d : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hc : c < 2 ^ 256)
    (hd : d < 2 ^ 256) : addP a b c d < 2 ^ 256 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    simp only [addP, hop_or, hop_and, hop_xor, abTbHi ha hi, abTbHi hb hi, abTbHi hc hi, abTbHi hd hi]
    rfl

theorem abAddM_lt {a b c d : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hc : c < 2 ^ 256)
    (hd : d < 2 ^ 256) : addM a b c d < 2 ^ 256 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    simp only [addM, hop_or, hop_and, hop_xor, abTbHi ha hi, abTbHi hb hi, abTbHi hc hi, abTbHi hd hi]
    rfl

theorem abLor_pair {a b x y : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    Nat.lor (2 ^ 256 * x + a) (2 ^ 256 * y + b) = 2 ^ 256 * Nat.lor x y + Nat.lor a b := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hab : Nat.lor a b < 2 ^ 256 := Nat.lt_pow_two_of_testBit _ fun i hi => by
    simp only [hop_or, abTbHi ha hi, abTbHi hb hi]
    rfl
  rw [hop_or, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ hab]
  split <;> simp

theorem abAddP_pair {a b c d a' b' c' d' : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hc : c < 2 ^ 256) (hd : d < 2 ^ 256) :
    addP (2 ^ 256 * a' + a) (2 ^ 256 * b' + b) (2 ^ 256 * c' + c) (2 ^ 256 * d' + d) =
      2 ^ 256 * addP a' b' c' d' + addP a b c d := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_two_pow_mul_add _ (abAddP_lt ha hb hc hd)]
  simp only [addP, hop_or, hop_and, hop_xor, Nat.testBit_two_pow_mul_add _ ha,
    Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hd]
  split <;> rfl

theorem abAddM_pair {a b c d a' b' c' d' : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hc : c < 2 ^ 256) (hd : d < 2 ^ 256) :
    addM (2 ^ 256 * a' + a) (2 ^ 256 * b' + b) (2 ^ 256 * c' + c) (2 ^ 256 * d' + d) =
      2 ^ 256 * addM a' b' c' d' + addM a b c d := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_two_pow_mul_add _ (abAddM_lt ha hb hc hd)]
  simp only [addM, hop_or, hop_and, hop_xor, Nat.testBit_two_pow_mul_add _ ha,
    Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hd]
  split <;> rfl

theorem abLor_shl {a b : Nat} (ha : a < 2 ^ 256) : Nat.lor a (Nat.shiftLeft b 256) = 2 ^ 256 * b + a := by
  change a ||| b <<< 256 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.mul_comm]

theorem abPair_lt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) : 2 ^ 256 * b + a < 2 ^ 512 := by
  have : 2 ^ 256 * b + a < 2 ^ 256 * (b + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  calc 2 ^ 256 * b + a < 2 ^ 256 * (b + 1) := this
    _ ≤ 2 ^ 256 * 2 ^ 256 := Nat.mul_le_mul_left _ hb
    _ = 2 ^ 512 := by rw [← Nat.pow_add]

theorem abSel_mul_pair (s x y : Nat) : s * (2 ^ 256 * y + x) = 2 ^ 256 * (s * y) + s * x := by
  rw [Nat.mul_add, Nat.mul_left_comm]

theorem abSel_lt (y j : Nat) {c : Nat} (hc : c < 2 ^ 256) : Nat.land (y >>> j) 1 * c < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul_right c (sel_le y j)) (by omega)) hc

theorem wmvAB_spec {n : Nat} {xp xm gp gm : Nat → Nat} (hxp : Bd n xp) (hxm : Bd n xm)
    (hgp : Bd n gp) (hgm : Bd n gm) (hd : ∀ i < n, xp i &&& xm i = 0) :
    ∀ (LA LB : List Nat) (j : Nat) (pa pb ma mb : Nat → Nat),
      (∀ i < n, pa i < 2 ^ 256 ∧ pb i < 2 ^ 256 ∧ ma i < 2 ^ 256 ∧ mb i < 2 ^ 256) →
      wmvAB (encF n (fun _ => 1)) (encF n xp) (encF n xm) (encF n gp) (encF n gm) LA LB j
        (encF n (fun i => 2 ^ 256 * pb i + pa i)) (encF n (fun i => 2 ^ 256 * mb i + ma i)) = true →
      ∀ i < n, gp i = 2 ^ 256 * (gp i / 2 ^ 256) + gp i % 2 ^ 256 ∧
        mvL LA (xp i >>> j) (xm i >>> j) (pa i) (ma i) = vmk (gp i % 2 ^ 256) (gm i % 2 ^ 256) ∧
        mvL LB (xp i >>> j) (xm i >>> j) (pb i) (mb i) = vmk (gp i / 2 ^ 256) (gm i / 2 ^ 256)
  | [], [], j, pa, pb, ma, mb, hb, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.beq (encF n (fun i => 2 ^ 256 * mb i + ma i)) (encF n gm))
      (Nat.beq (encF n (fun i => 2 ^ 256 * pb i + pa i)) (encF n gp)) = true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨b1, b2, b3, b4⟩ := hb i hi
    have bP : Bd n (fun i => 2 ^ 256 * pb i + pa i) := fun i hi =>
      abPair_lt (hb i hi).1 (hb i hi).2.1
    have bM : Bd n (fun i => 2 ^ 256 * mb i + ma i) := fun i hi =>
      abPair_lt (hb i hi).2.2.1 (hb i hi).2.2.2
    have e1 := enc_inj n _ _ bP hgp (Nat.eq_of_beq_eq_true h1) i hi
    have e2 := enc_inj n _ _ bM hgm (Nat.eq_of_beq_eq_true h2) i hi
    rw [← e1, ← e2]
    refine ⟨by omega, ?_, ?_⟩
    · have q1 : (2 ^ 256 * pb i + pa i) % 2 ^ 256 = pa i := by omega
      have q2 : (2 ^ 256 * mb i + ma i) % 2 ^ 256 = ma i := by omega
      rw [q1, q2]
      rfl
    · have q1 : (2 ^ 256 * pb i + pa i) / 2 ^ 256 = pb i := by omega
      have q2 : (2 ^ 256 * mb i + ma i) / 2 ^ 256 = mb i := by omega
      rw [q1, q2]
      rfl
  | [], _ :: _, j, pa, pb, ma, mb, hb, h, i, hi => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], j, pa, pb, ma, mb, hb, h, i, hi => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | a :: LA, b :: LB, j, pa, pb, ma, mb, hb, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
      (strictB (Nat.lor (vP a) (Nat.shiftLeft (vP b) 256)) fun cp =>
        strictB (Nat.lor (vM a) (Nat.shiftLeft (vM b) 256)) fun cm =>
        strictB (selW (encF n xp) (encF n (fun _ => 1)) j) fun sp =>
        strictB (selW (encF n xm) (encF n (fun _ => 1)) j) fun sm =>
        strictB (Nat.lor (Nat.mul sp cp) (Nat.mul sm cm)) fun tp =>
        strictB (Nat.lor (Nat.mul sp cm) (Nat.mul sm cp)) fun tm =>
        strictB (addP (encF n (fun i => 2 ^ 256 * pb i + pa i))
          (encF n (fun i => 2 ^ 256 * mb i + ma i)) tp tm) fun ap' =>
        strictB (addM (encF n (fun i => 2 ^ 256 * pb i + pa i))
          (encF n (fun i => 2 ^ 256 * mb i + ma i)) tp tm) fun am' =>
          wmvAB (encF n (fun _ => 1)) (encF n xp) (encF n xm) (encF n gp) (encF n gm) LA LB
            (Nat.succ j) ap' am')
      (Nat.blt j 512)) (Nat.blt b (Nat.shiftLeft 1 512))) (Nat.blt a (Nat.shiftLeft 1 512)) = true at h
    obtain ⟨ha, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hb', h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hj, h⟩ := (bAnd_iff _ _).1 h
    have ha : a < 2 ^ 512 := by
      have := Nat.blt_eq.mp ha
      rwa [PackFld.shl_eq, Nat.one_mul] at this
    have hb2 : b < 2 ^ 512 := by
      have := Nat.blt_eq.mp hb'
      rwa [PackFld.shl_eq, Nat.one_mul] at this
    have hj : j < 512 := Nat.blt_eq.mp hj
    simp only [PackFld.strictB_eqP] at h
    have h1 : (1 : Nat) < 2 ^ (512 - j) := Nat.one_lt_two_pow (by omega)
    have esp : selW (encF n xp) (encF n (fun _ => 1)) j = encF n (fun i => Nat.land (xp i >>> j) 1) :=
      enc_sel h1 n xp hxp
    have esm : selW (encF n xm) (encF n (fun _ => 1)) j = encF n (fun i => Nat.land (xm i >>> j) 1) :=
      enc_sel h1 n xm hxm
    rw [esp, esm, abLor_shl (vP_lt a), abLor_shl (vM_lt ha)] at h
    have hPa := vP_lt a
    have hPb := vP_lt b
    have hMa := vM_lt ha
    have hMb := vM_lt hb2
    have hcp := abPair_lt hPa hPb
    have hcm := abPair_lt hMa hMb
    have b1 : Bd n (fun i => Nat.land (xp i >>> j) 1 * (2 ^ 256 * vP b + vP a)) :=
      fun i _ => sel_mul_lt _ _ hcp
    have b2 : Bd n (fun i => Nat.land (xm i >>> j) 1 * (2 ^ 256 * vM b + vM a)) :=
      fun i _ => sel_mul_lt _ _ hcm
    have b3 : Bd n (fun i => Nat.land (xp i >>> j) 1 * (2 ^ 256 * vM b + vM a)) :=
      fun i _ => sel_mul_lt _ _ hcm
    have b4 : Bd n (fun i => Nat.land (xm i >>> j) 1 * (2 ^ 256 * vP b + vP a)) :=
      fun i _ => sel_mul_lt _ _ hcp
    rw [Nat.mul_eq, Nat.mul_eq, Nat.mul_eq, Nat.mul_eq, enc_mul, enc_mul, enc_mul, enc_mul,
      enc_or b1 b2, enc_or b3 b4] at h
    have bP : Bd n (fun i => 2 ^ 256 * pb i + pa i) := fun i hi =>
      abPair_lt (hb i hi).1 (hb i hi).2.1
    have bM : Bd n (fun i => 2 ^ 256 * mb i + ma i) := fun i hi =>
      abPair_lt (hb i hi).2.2.1 (hb i hi).2.2.2
    rw [enc_addP bP bM (b1.or b2) (b3.or b4), enc_addM bP bM (b1.or b2) (b3.or b4)] at h
    let s1 := fun i => Nat.land (xp i >>> j) 1
    let s2 := fun i => Nat.land (xm i >>> j) 1
    let tpA := fun i => Nat.lor (s1 i * vP a) (s2 i * vM a)
    let tmA := fun i => Nat.lor (s1 i * vM a) (s2 i * vP a)
    let tpB := fun i => Nat.lor (s1 i * vP b) (s2 i * vM b)
    let tmB := fun i => Nat.lor (s1 i * vM b) (s2 i * vP b)
    have etp : ∀ i, Nat.lor (s1 i * (2 ^ 256 * vP b + vP a)) (s2 i * (2 ^ 256 * vM b + vM a)) =
        2 ^ 256 * tpB i + tpA i := fun i => by
      rw [abSel_mul_pair, abSel_mul_pair, abLor_pair (abSel_lt _ _ hPa) (abSel_lt _ _ hMa)]
    have etm : ∀ i, Nat.lor (s1 i * (2 ^ 256 * vM b + vM a)) (s2 i * (2 ^ 256 * vP b + vP a)) =
        2 ^ 256 * tmB i + tmA i := fun i => by
      rw [abSel_mul_pair, abSel_mul_pair, abLor_pair (abSel_lt _ _ hMa) (abSel_lt _ _ hPa)]
    have btA : ∀ i, tpA i < 2 ^ 256 ∧ tmA i < 2 ^ 256 := fun i =>
      ⟨Nat.or_lt_two_pow (abSel_lt (xp i) j hPa) (abSel_lt (xm i) j hMa),
        Nat.or_lt_two_pow (abSel_lt (xp i) j hMa) (abSel_lt (xm i) j hPa)⟩
    have ep : encF n (fun i => addP (2 ^ 256 * pb i + pa i) (2 ^ 256 * mb i + ma i)
        (Nat.lor (s1 i * (2 ^ 256 * vP b + vP a)) (s2 i * (2 ^ 256 * vM b + vM a)))
        (Nat.lor (s1 i * (2 ^ 256 * vM b + vM a)) (s2 i * (2 ^ 256 * vP b + vP a)))) =
        encF n (fun i => 2 ^ 256 * addP (pb i) (mb i) (tpB i) (tmB i) +
          addP (pa i) (ma i) (tpA i) (tmA i)) :=
      enc_congr n _ _ fun i hi => by
        rw [etp, etm, abAddP_pair (hb i hi).1 (hb i hi).2.2.1 (btA i).1 (btA i).2]
    have em : encF n (fun i => addM (2 ^ 256 * pb i + pa i) (2 ^ 256 * mb i + ma i)
        (Nat.lor (s1 i * (2 ^ 256 * vP b + vP a)) (s2 i * (2 ^ 256 * vM b + vM a)))
        (Nat.lor (s1 i * (2 ^ 256 * vM b + vM a)) (s2 i * (2 ^ 256 * vP b + vP a)))) =
        encF n (fun i => 2 ^ 256 * addM (pb i) (mb i) (tpB i) (tmB i) +
          addM (pa i) (ma i) (tpA i) (tmA i)) :=
      enc_congr n _ _ fun i hi => by
        rw [etp, etm, abAddM_pair (hb i hi).1 (hb i hi).2.2.1 (btA i).1 (btA i).2]
    rw [ep, em] at h
    have btB : ∀ i, tpB i < 2 ^ 256 ∧ tmB i < 2 ^ 256 := fun i =>
      ⟨Nat.or_lt_two_pow (abSel_lt (xp i) j hPb) (abSel_lt (xm i) j hMb),
        Nat.or_lt_two_pow (abSel_lt (xp i) j hMb) (abSel_lt (xm i) j hPb)⟩
    have hb'' : ∀ i < n, addP (pa i) (ma i) (tpA i) (tmA i) < 2 ^ 256 ∧
        addP (pb i) (mb i) (tpB i) (tmB i) < 2 ^ 256 ∧
        addM (pa i) (ma i) (tpA i) (tmA i) < 2 ^ 256 ∧ addM (pb i) (mb i) (tpB i) (tmB i) < 2 ^ 256 :=
      fun i hi => ⟨abAddP_lt (hb i hi).1 (hb i hi).2.2.1 (btA i).1 (btA i).2,
        abAddP_lt (hb i hi).2.1 (hb i hi).2.2.2 (btB i).1 (btB i).2,
        abAddM_lt (hb i hi).1 (hb i hi).2.2.1 (btA i).1 (btA i).2,
        abAddM_lt (hb i hi).2.1 (hb i hi).2.2.2 (btB i).1 (btB i).2⟩
    obtain ⟨ih0, ihA, ihB⟩ := wmvAB_spec hxp hxm hgp hgm hd LA LB (Nat.succ j) _ _ _ _ hb'' h i hi
    refine ⟨ih0, ?_, ?_⟩
    · rw [mvL_cons, step_field (hd i hi)]
      exact ihA
    · rw [mvL_cons, step_field (hd i hi)]
      exact ihB

theorem abLor_mul {a b : Nat} (ha : a < 2 ^ 256) : Nat.lor a (b * 2 ^ 256) = 2 ^ 256 * b + a := by
  rw [← Nat.shiftLeft_eq]
  exact abLor_shl ha

theorem finAB_spec {LA LB : List Nat} {cnt : Nat} {fK fA fB : Nat → Nat} (hK : Bd cnt fK)
    (hA : Bd cnt fA) (hB : Bd cnt fB) (hc : ∀ i < cnt, canon (fK i) = true)
    (h : finAB LA LB cnt (encF cnt fK) (encF cnt fA) (encF cnt fB) = true) :
    ∀ i < cnt, mv LA (fK i) = fA i ∧ mv LB (fK i) = fB i := by
  unfold finAB at h
  simp only [PackFld.strictB_eqP, rep_eq] at h
  have hP : ∀ {f : Nat → Nat}, Bd cnt f →
      Nat.land (encF cnt f) (encF cnt (fun _ => mask 256)) = encF cnt (fun i => vP (f i)) := by
    intro f hf
    have := enc_sel lo_eq.1 cnt f hf
    rw [Nat.shiftRight_zero] at this
    change (encF cnt f &&& encF cnt (fun _ => mask 256)) = _
    rw [this]
    simp only [Nat.shiftRight_zero]
    rfl
  have hM : ∀ {f : Nat → Nat}, Bd cnt f →
      Nat.land (Nat.shiftRight (encF cnt f) 256) (encF cnt (fun _ => mask 256)) =
        encF cnt (fun i => vM (f i)) := by
    intro f hf
    have := enc_sel lo_eq.2 cnt f hf
    change (encF cnt f >>> 256) &&& encF cnt (fun _ => mask 256) = _
    rw [this]
    exact enc_congr cnt _ _ fun i hi => field_hi (hf i hi)
  rw [hP hK, hM hK, hP hA, hM hA, hP hB, hM hB] at h
  have bP : ∀ {f : Nat → Nat}, Bd cnt (fun i => vP (f i)) := fun _ _ => lt512_of_lt256 (vP_lt _)
  have bM : ∀ {f : Nat → Nat}, Bd cnt f → Bd cnt (fun i => vM (f i)) :=
    fun hf i hi => lt512_of_lt256 (vM_lt (hf i hi))
  have bS : ∀ {f : Nat → Nat}, (∀ i < cnt, f i < 2 ^ 256) → Bd cnt (fun i => f i * 2 ^ 256) :=
    fun {f} hf i hi => calc f i * 2 ^ 256 = 2 ^ 256 * f i + 0 := by rw [Nat.add_zero, Nat.mul_comm]
      _ < 2 ^ 512 := abPair_lt (Nat.two_pow_pos 256) (hf i hi)
  have eG : ∀ {f g : Nat → Nat}, (∀ i < cnt, f i < 2 ^ 256) → (∀ i < cnt, g i < 2 ^ 256) →
      Nat.lor (encF cnt f) (Nat.shiftLeft (encF cnt g) 256) =
        encF cnt (fun i => 2 ^ 256 * g i + f i) := by
    intro f g hf hg
    rw [PackFld.shl_eq, enc_mul, enc_or (fun i hi => lt512_of_lt256 (hf i hi)) (bS hg)]
    exact enc_congr cnt _ _ fun i hi => abLor_mul (hf i hi)
  have vMl : ∀ {f : Nat → Nat}, Bd cnt f → ∀ i < cnt, vM (f i) < 2 ^ 256 :=
    fun hf i hi => vM_lt (hf i hi)
  rw [eG (fun i _ => vP_lt (fA i)) (fun i _ => vP_lt (fB i)),
    eG (vMl hA) (vMl hB)] at h
  have hd : ∀ i < cnt, vP (fK i) &&& vM (fK i) = 0 := fun i hi => (canon_bits (hc i hi)).1
  have s := wmvAB_spec bP (bM hK) (fun i hi => abPair_lt (vP_lt (fA i)) (vP_lt (fB i)))
    (fun i hi => abPair_lt (vMl hA i hi) (vMl hB i hi)) hd LA LB 0 (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ _ => ⟨Nat.two_pow_pos 256, Nat.two_pow_pos 256,
      Nat.two_pow_pos 256, Nat.two_pow_pos 256⟩) (by simp only [Nat.mul_zero, Nat.add_zero, enc_zero]; exact h)
  intro i hi
  obtain ⟨-, sA, sB⟩ := s i hi
  have q1 := vP_lt (fA i)
  have q2 := vP_lt (fB i)
  have q3 := vMl hA i hi
  have q4 := vMl hB i hi
  have m1 : (2 ^ 256 * vP (fB i) + vP (fA i)) % 2 ^ 256 = vP (fA i) := by omega
  have m2 : (2 ^ 256 * vM (fB i) + vM (fA i)) % 2 ^ 256 = vM (fA i) := by omega
  have d1 : (2 ^ 256 * vP (fB i) + vP (fA i)) / 2 ^ 256 = vP (fB i) := by omega
  have d2 : (2 ^ 256 * vM (fB i) + vM (fA i)) / 2 ^ 256 = vM (fB i) := by omega
  rw [m1, m2] at sA
  rw [d1, d2] at sB
  have e : ∀ L, mv L (fK i) = mvL L (vP (fK i) >>> 0) (vM (fK i) >>> 0) 0 0 := by
    intro L
    simp only [mv, PackFld.strictN_eqP, Nat.shiftRight_zero]
  rw [e, e, sA, sB, vmk_vP_vM, vmk_vP_vM]
  exact ⟨rfl, rfl⟩

theorem mvRangeAB_imp {K : Nat → Nat} {LA LB : List Nat} {A B : Nat → Nat} {n lo cnt : Nat}
    (h : mvRangeAB K LA LB A B n lo cnt = true) : mvRange K LA LB A B n lo cnt = true := by
  obtain ⟨h1, h2⟩ := ptsW_spec cnt 0 0 0 h
  simp only [Nat.mul_zero, Nat.add_zero] at h2
  have hf := finAB_spec (fun i _ => key_lt K _) (fun i _ => key_lt K _) (fun i _ => key_lt K _)
    (fun i hi => (h1 i hi).1) h2
  refine allBlk_of fun l hl => ?_
  obtain ⟨hc, ha, hb⟩ := h1 l hl
  obtain ⟨eA, eB⟩ := hf l hl
  unfold mvAt
  simp only [PackFld.strictB_eqP]
  rw [hc, Nat.blt_eq.mpr ha, Nat.blt_eq.mpr hb, eA, eB]
  simp [Nat.beq_refl]

end CFSG.KS.ONW

end
