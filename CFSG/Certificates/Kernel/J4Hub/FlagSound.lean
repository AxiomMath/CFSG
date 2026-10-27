module

public import CFSG.Certificates.Kernel.J4Hub.BlockSound
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

@[expose] def LowerUni {p d : Nat} (A : Matrix (Fin d) (Fin d) (ZMod p)) : Prop :=
  (∀ i j : Fin d, i < j → A i j = 0) ∧ ∀ i : Fin d, A i i = 1

theorem LowerUni.mul {p d : Nat} {A B : Matrix (Fin d) (Fin d) (ZMod p)} (hA : LowerUni A)
    (hB : LowerUni B) : LowerUni (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hB.1 k j (lt_of_le_of_lt h hij), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hB.1 k i h, mul_zero]
      · rw [hA.1 i k h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem LowerUni.one {p d : Nat} : LowerUni (1 : Matrix (Fin d) (Fin d) (ZMod p)) :=
  ⟨fun _ _ hij => Matrix.one_apply_ne (ne_of_lt hij), fun i => Matrix.one_apply_eq i⟩

theorem LowerUni.pow_eq_one {p d : Nat} [hp : Fact p.Prime] {A : Matrix (Fin d) (Fin d) (ZMod p)}
    (hA : LowerUni A) : A ^ (p ^ d) = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set N := A - 1 with hN
  have hN0 : ∀ i j : Fin d, i ≤ j → N i j = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | h
    · rw [hN, Matrix.sub_apply, hA.2 i, Matrix.one_apply_eq, sub_self]
    · rw [hN, Matrix.sub_apply, hA.1 i j h, Matrix.one_apply_ne (ne_of_lt h), sub_self]
  have hpow : ∀ m : Nat, ∀ i j : Fin d, i.val < j.val + m → (N ^ m) i j = 0 := by
    intro m
    induction m with
    | zero =>
      intro i j h
      rw [pow_zero, Matrix.one_apply_ne (fun e => by rw [e] at h; omega)]
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hjk : j.val < k.val
      · rw [ih i k (by omega), zero_mul]
      · rw [hN0 k j (Fin.le_iff_val_le_val.2 (by omega)), mul_zero]
  have hNd : N ^ d = 0 := by
    ext i j
    rw [hpow d i j (by have := i.isLt; omega), Matrix.zero_apply]
  have hle : d ≤ p ^ d := (Nat.lt_pow_self hp.out.one_lt).le
  have hNp : N ^ (p ^ d) = 0 := pow_eq_zero_of_le hle hNd
  have e : A = 1 + N := by
    rw [hN]
    abel
  rw [e, add_pow_char_pow_of_commute p d (Commute.one_left N), one_pow, hNp, add_zero]

@[expose] def luSub (p d : Nat) [Fact p.Prime] : Subgroup (GL (Fin d) (ZMod p)) where
  carrier := {g | LowerUni ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p))}
  one_mem' := LowerUni.one
  mul_mem' := fun ha hb => by
    change LowerUni (_ * _)
    exact LowerUni.mul ha hb
  inv_mem' := by
    intro g hg
    have hg1 : g ^ (p ^ d) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hg.pow_eq_one)
    have hpos : 0 < p ^ d := Nat.pow_pos (Fact.out : p.Prime).pos
    have hinv : g⁻¹ = g ^ (p ^ d - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel hpos, hg1]
    change LowerUni ((g⁻¹ : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p))
    rw [hinv, Units.val_pow_eq_pow_val]
    have key : ∀ k : Nat, LowerUni (((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) ^ k) := by
      intro k
      induction k with
      | zero => rw [pow_zero]; exact LowerUni.one
      | succ k ih => rw [pow_succ]; exact LowerUni.mul ih hg
    exact key _

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

theorem upMask_bit {w d i j k : Nat} (hij : i < j) (hj : j < d) (hk : k < w) :
    (upMask w (d * w) d).testBit (d * w * i + w * j + k) = true := by
  let term : Nat → Nat := fun i => Nat.shiftLeft
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w (Nat.sub (Nat.sub d i) (nat_lit 1)))) (nat_lit 1))
      (Nat.add (Nat.mul (d * w) i) (Nat.mul w (Nat.succ i)))
  have hmono : ∀ m b, i < m → (term i).testBit b = true →
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.lor acc (term i)) m).testBit b
        = true := by
    intro m b
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h ht
      change (Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => Nat.lor acc (term i)) m) (term m)).testBit b = true
      change ((Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => Nat.lor acc (term i)) m) ||| (term m)).testBit b = true
      rw [Nat.testBit_or]
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
      · rw [ih h ht, Bool.true_or]
      · rw [ht, Bool.or_true]
  have hb : (term i).testBit (d * w * i + w * j + k) = true := by
    change ((1 <<< (w * (d - i - 1)) - 1) <<< (d * w * i + w * (i + 1))).testBit
      (d * w * i + w * j + k) = true
    have e1 : w * j = w * (i + 1) + w * (j - i - 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have e2 : w * (j - i - 1) + w ≤ w * (d - i - 1) := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [Nat.testBit_shiftLeft, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rw [e1]
      omega
    · rw [e1]
      omega
  exact hmono d _ (by omega) hb

theorem lane_zero {w M X t : Nat} (h : M &&& X = 0) (hX : ∀ k < w, X.testBit (w * t + k) = true) :
    lane w M t = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  unfold lane
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit]
  by_cases hk : k < w
  · have h1 := congrArg (fun y => Nat.testBit y (w * t + k)) h
    simp only [Nat.testBit_and, hX k hk, Bool.and_true, Nat.zero_testBit] at h1
    rw [Nat.add_comm k, h1]
    simp
  · simp [hk]

theorem flag_mat (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {M : Nat}
    (hM : Canon p d w M) (hup : Nat.land M (upMask w S d) = 0)
    (hdg : Nat.land M (Nat.mul ONE (Nat.sub (Nat.shiftLeft 1 w) 1)) = ONE) :
    LowerUni (ordMat p d w S M) := by
  obtain ⟨hp, hS, hw, -, hT, -, -, -, -, -, hONE⟩ := consts_facts hc
  subst hS
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  have hent : ∀ i j : Fin d, ordMat p d w (d * w) M i j = ((lane w M (d * i.val + j.val) : Nat) : ZMod p) := by
    intro i j
    unfold ordMat lane
    congr 3
    ring
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hent, lane_zero hup fun k hk => ?_]
    · simp
    · have := upMask_bit (w := w) (d := d) (k := k) hij j.isLt hk
      rwa [show d * w * i.val + w * j.val + k = w * (d * i.val + j.val) + k by ring] at this
  · obtain ⟨a, rfl, ha⟩ : ∃ a, M = pk w (d * d) a ∧ ∀ t < d * d, a t < 2 ^ w :=
      ⟨lane w M, pk_lane hw hM.1, fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)⟩
    have hδ : ∀ t < d * d, (if t / d = t % d then 1 else 0) * (2 ^ w - 1) < 2 ^ w := by
      intro t _
      have := Nat.two_pow_pos w
      split <;> omega
    have hOne : ONE * (2 ^ w - 1) = pk w (d * d) (fun t => (if t / d = t % d then 1 else 0) * (2 ^ w - 1)) := by
      rw [hONE, pk_mul]
    have hdg' : pk w (d * d) a &&& (ONE * (2 ^ w - 1)) = ONE := by
      have := hdg
      change pk w (d * d) a &&& (ONE * ((1 <<< w) - 1)) = ONE at this
      rwa [Nat.shiftLeft_eq, Nat.one_mul] at this
    rw [hOne] at hdg'
    have hF := fld_and (fld_pk ha) (fld_pk hδ)
    rw [hdg'] at hF
    have ht : d * i.val + i.val < d * d := by
      have := i.isLt
      have : d * i.val + d ≤ d * d := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
      omega
    obtain ⟨e1, e2'⟩ : (d * i.val + i.val) / d = i.val ∧ (d * i.val + i.val) % d = i.val :=
      dm_eq i.isLt
    have hl := lane_of_fld hF (s := d * i.val + i.val) (by
      simp only [ht, ↓reduceIte, e1, e2']
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp))
    simp only [ht, ↓reduceIte, e1, e2', one_mul] at hl
    rw [hONE, lane_pk (fun t _ => by split <;> omega) ht] at hl
    simp only [e1, e2', ↓reduceIte] at hl
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (ha _ ht)] at hl
    have hlane : lane w (pk w (d * d) a) (d * i.val + i.val) = 1 := by
      rw [lane_pk ha ht]
      exact hl.symm
    rw [hent, hlane, Nat.cast_one]

theorem sylowFlag_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {n PR nbl BL UP Cm Ci : Nat} (hp : p.Prime)
    (hpr : regsIn PR n nreg = true)
    (hfl : flagOK (mulR p w S d T L H CM RM) (validM p nb L H) w S d ONE UP Cm Ci = true)
    (hun : uniOK RB (mulR p w S d T L H CM RM) w ONE UP Cm Ci PR 0 n = true)
    (hbl : BlocksOK p d w S T RM LV HV RB PR n p nbl BL) :
    p ^ n ∣ Nat.card G := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_GL (d := d) hp.two_le
  obtain ⟨hO1, hO2⟩ := CFSG.KS.Ord.one_sound hc
  obtain ⟨hUP, hf⟩ := andT' hfl
  obtain ⟨hCm, hf⟩ := andT' hf
  obtain ⟨hCi, hCC⟩ := andT' hf
  have hUP' : UP = upMask w S d := Nat.eq_of_beq_eq_true hUP
  subst hUP'
  have cCm : Canon p d w Cm := by subst hnb; exact validM_canon hc hCm
  have cCi : Canon p d w Ci := by subst hnb; exact validM_canon hc hCi
  have hCC' : ordMat p d w S Cm * ordMat p d w S Ci = 1 := by
    rw [← (mulR_sound hc cCm cCi).2, Nat.eq_of_beq_eq_true hCC, hO2]
  let c : GL (Fin d) (ZMod p) := ⟨ordMat p d w S Cm, ordMat p d w S Ci, hCC', mul_eq_one_comm.mp hCC'⟩
  let U : Subgroup (GL (Fin d) (ZMod p)) := (luSub p d).comap (MulAut.conj c).toMonoidHom
  have hle : pcSub p d w S RB PR 0 n ≤ U := by
    refine (Subgroup.closure_le U).2 ?_
    rintro g ⟨k, -, hk, eg⟩
    obtain ⟨cpc, -⟩ := pc_reg hnb hc hR hpr hk
    have hk' := rec_and' (f := fun k => Bool.rec (motive := fun _ => Bool) true
      ((fun M => andB (Nat.beq (Nat.land M (upMask w S d)) (nat_lit 0))
        (Nat.beq (Nat.land M (Nat.mul ONE (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))) ONE))
        (mulR p w S d T L H CM RM (mulR p w S d T L H CM RM Cm (RB (at16 PR k))) Ci))
      (Nat.ble 0 k)) n hun k hk
    rw [Nat.ble_eq_true_of_le (Nat.zero_le k)] at hk'
    obtain ⟨h1, h2⟩ := andT' hk'
    obtain ⟨c1, e1⟩ := mulR_sound hc cCm cpc
    obtain ⟨c2, e2⟩ := mulR_sound hc c1 cCi
    have hLU := flag_mat hc c2 (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
    change LowerUni ((c * g * c⁻¹ : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p))
    rw [e2, e1] at hLU
    have hv : ((c * g * c⁻¹ : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) =
        ordMat p d w S Cm * ordMat p d w S (RB (at16 PR k)) * ordMat p d w S Ci := by
      rw [Units.val_mul, Units.val_mul, eg]
      rfl
    rw [hv]
    exact hLU
  have hpg : IsPGroup p (pcSub p d w S RB PR 0 n) := by
    intro g
    refine ⟨d, Subtype.ext ?_⟩
    have hU := hle g.2
    change LowerUni ((c * (g : GL (Fin d) (ZMod p)) * c⁻¹ : GL (Fin d) (ZMod p)) :
      Matrix (Fin d) (Fin d) (ZMod p)) at hU
    have h1 : (c * (g : GL (Fin d) (ZMod p)) * c⁻¹) ^ (p ^ d) = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hU.pow_eq_one)
    rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
    simpa using h1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  have hlo := blocks_le hc hnb hR hpr hbl
  rw [hm] at hlo
  have hnm : n ≤ m := (Nat.pow_le_pow_iff_right hp.two_le).1 hlo
  calc p ^ n ∣ p ^ m := Nat.pow_dvd_pow p hnm
    _ = Nat.card (pcSub p d w S RB PR 0 n) := hm.symm
    _ ∣ Nat.card G := Subgroup.card_dvd_of_le (pcSub_le hnb hc hR hpr 0)

end CFSG.KS.J4Hub

end
