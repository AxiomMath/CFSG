module

public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LocalQT.Steps

public section

namespace CFSG.KC.LQT.SecS

open CFSG.KS.Ord CFSG.KS.PackFld
open scoped Matrix

@[expose] def VCanon (p d w v : Nat) : Prop := v < 2 ^ (w * d) ∧ ∀ j < d, lane w v j < p

@[expose] noncomputable def toVec (p d w v : Nat) : Fin d → ZMod p :=
  fun j => ((lane w v j.val : Nat) : ZMod p)

theorem andT {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KC.Ord.andB]

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem allLt_spec {m : Nat} {f : Nat → Bool} (h : allLt m f = true) : ∀ i < m, f i = true := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    obtain ⟨h1, h2⟩ := andT h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

private theorem consts_v {p w S d T L H CM RM ONE LV HV : Nat}
    (hc : CFSG.KC.Ord.constsOK p w S d T L H CM RM ONE LV HV = true) (hw : 0 < w) :
    LV = pk w d (fun _ => 1) ∧ HV = pk w d (fun _ => 2 ^ (w - 1)) := by
  unfold CFSG.KC.Ord.constsOK at hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨-, hc⟩ := andT hc
  obtain ⟨hLV, hHV⟩ := andT hc
  have hLV' : LV = pk w d (fun _ => 1) := by
    have h : LV = CFSG.KC.Ord.rep1 w d := Nat.eq_of_beq_eq_true hLV
    rw [h, rep1_eq (Or.inl hw)]
    simp [pk]
  refine ⟨hLV', ?_⟩
  have h : HV = LV <<< (w - 1) := Nat.eq_of_beq_eq_true hHV
  rw [h, Nat.shiftLeft_eq, hLV', pk_mul]
  exact pk_congr fun _ _ => Nat.one_mul _

private theorem vcanon_pk {p d w : Nat} {g : Nat → Nat} (hg : ∀ t < d, g t < p) (hp : p ≤ 2 ^ w) :
    VCanon p d w (pk w d g) := by
  have hg' : ∀ t < d, g t < 2 ^ w := fun t ht => Nat.lt_of_lt_of_le (hg t ht) hp
  refine ⟨pk_lt hg', fun t ht => ?_⟩
  rw [lane_pk hg' ht]
  exact hg t ht

theorem vecU_eq (w S d RM v M : Nat) : CFSG.KC.Ord.vecU w S d RM v M =
    ∑ k ∈ Finset.range d, CFSG.KC.Ord.bitsN v (w * k) w * ((M >>> (S * k)) &&& RM) := by
  unfold CFSG.KC.Ord.vecU
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem bitsN_lane (v w k : Nat) : CFSG.KC.Ord.bitsN v (w * k) w = lane w v k := by
  unfold CFSG.KC.Ord.bitsN lane
  change (v >>> (w * k)) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem sum_pk (w n d : Nat) (a : Nat → Nat) (g : Nat → Nat → Nat) :
    ∑ k ∈ Finset.range d, a k * pk w n (g k) =
      pk w n (fun j => ∑ k ∈ Finset.range d, a k * g k j) := by
  unfold pk
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem vecR_sound {p w S d T L H CM RM ONE LV HV v M : Nat}
    (hc : CFSG.KC.Ord.constsOK p w S d T L H CM RM ONE LV HV = true) (hv : VCanon p d w v)
    (hM : Canon p d w M) :
    VCanon p d w (CFSG.KC.Ord.vecR p w S d T LV HV RM v M) ∧
      toVec p d w (CFSG.KC.Ord.vecR p w S d T LV HV RM v M) = toVec p d w v ᵥ* ordMat p d w S M := by
  obtain ⟨hp, hS, hw, hdp, hT, hT2, -, -, -, hRM, -⟩ := consts_facts hc
  obtain ⟨hLV, hHV⟩ := consts_v hc hw
  subst hS hRM hLV hHV
  obtain ⟨a, rfl, ha⟩ : ∃ a, v = pk w d a ∧ ∀ t < d, a t < p :=
    ⟨lane w v, pk_lane hw hv.1, hv.2⟩
  obtain ⟨b, rfl, hb⟩ : ∃ b, M = pk w (d * d) b ∧ ∀ t < d * d, b t < p :=
    ⟨lane w M, pk_lane hw hM.1, hM.2⟩
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  have ha' : ∀ t < d, a t < 2 ^ w := fun t ht => Nat.lt_of_lt_of_le (ha t ht) hpw
  have hb' : ∀ t < d * d, b t < 2 ^ w := fun t ht => Nat.lt_of_lt_of_le (hb t ht) hpw
  have hC : ∀ j < d, ∑ k ∈ Finset.range d, a k * b (d * k + j) ≤ d * ((p - 1) * (p - 1)) := by
    intro j hj
    calc _ ≤ ∑ _k ∈ Finset.range d, (p - 1) * (p - 1) :=
          Finset.sum_le_sum fun k hk => by
            have hk' := Finset.mem_range.1 hk
            have x1 := ha k hk'
            have x2 := hb _ (idx_lt hk' hj)
            exact Nat.mul_le_mul (by omega) (by omega)
      _ = d * ((p - 1) * (p - 1)) := by simp
  have hU : CFSG.KC.Ord.vecU w (d * w) d (2 ^ (w * d) - 1) (pk w d a) (pk w (d * d) b) =
      pk w d (fun j => ∑ k ∈ Finset.range d, a k * b (d * k + j)) := by
    rw [vecU_eq]
    refine Eq.trans ?_ (sum_pk w d d a fun k j => b (d * k + j))
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [bitsN_lane, lane_pk ha' hk', row_eq hw hb' hk']
  have e : CFSG.KC.Ord.vecR p w (d * w) d T (pk w d fun _ => 1) (pk w d fun _ => 2 ^ (w - 1))
      (2 ^ (w * d) - 1) (pk w d a) (pk w (d * d) b) =
      pk w d (fun j => (∑ k ∈ Finset.range d, a k * b (d * k + j)) % p) := by
    unfold CFSG.KC.Ord.vecR
    rw [hU]
    exact redP_pk hw hT (fun t ht => by have := hC t ht; omega)
      (fun t ht => by have := hC t ht; omega)
  have hCp : ∀ t < d, (∑ k ∈ Finset.range d, a k * b (d * k + t)) % p < p :=
    fun t _ => Nat.mod_lt _ (by omega)
  have hCp' : ∀ t < d, (∑ k ∈ Finset.range d, a k * b (d * k + t)) % p < 2 ^ w :=
    fun t ht => Nat.lt_of_lt_of_le (hCp t ht) hpw
  rw [e]
  refine ⟨vcanon_pk hCp hpw, ?_⟩
  funext j
  simp only [toVec, Matrix.vecMul, dotProduct]
  rw [lane_pk hCp' j.isLt, ZMod.natCast_mod, Nat.cast_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, lane_pk ha' k.isLt, ordMat_pk hb' k j]

theorem vec_inj {p d w : Nat} (hw : 0 < w) {u v : Nat} (hu : VCanon p d w u)
    (hv : VCanon p d w v) (h : toVec p d w u = toVec p d w v) : u = v := by
  rw [pk_lane hw hu.1, pk_lane hw hv.1]
  refine pk_congr fun t ht => ?_
  have h3 := congrFun h ⟨t, ht⟩
  simp only [toVec] at h3
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  rwa [Nat.mod_eq_of_lt (hu.2 t ht), Nat.mod_eq_of_lt (hv.2 t ht)] at h3

theorem unit_canon (c : Lay) (hc : c.ok = true) {t : Nat} (ht : t < c.d) :
    VCanon c.p c.d c.w (c.unit t) := by
  obtain ⟨hp, -, hw, -, hT, -⟩ := consts_facts hc
  have hp2 : c.p ≤ 2 ^ (c.w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right c.p (Nat.two_pow_pos c.T)) hT
  have e2 := two_pow_pred hw
  have e : c.unit t = pk c.w c.d (fun j => if j = t then 1 else 0) := by
    unfold Lay.unit
    change 1 <<< (c.w * t) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    unfold pk
    simp [ht]
  rw [e]
  exact vcanon_pk (g := fun j => if j = t then 1 else 0) (fun j _ => by split <;> omega)
    (by omega)

theorem lay_w_pos (c : Lay) (hc : c.ok = true) : 0 < c.w :=
  (consts_facts hc).2.2.1

theorem ne_of_notB {x y : Nat} (h : CFSG.KC.Ord.notB (Nat.beq x y) = true) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  cases hb : Nat.beq y y
  · exact Nat.ne_of_beq_eq_false hb rfl
  · rw [hb] at h
    exact absurd h (by decide)

theorem vec_sound (c : Lay) (hc : c.ok = true) {v M : Nat} (hv : VCanon c.p c.d c.w v)
    (hM : Canon c.p c.d c.w M) :
    VCanon c.p c.d c.w (c.vec v M) ∧
      toVec c.p c.d c.w (c.vec v M) = toVec c.p c.d c.w v ᵥ* ordMat c.p c.d c.w c.S M :=
  vecR_sound hc hv hM

theorem mul_sound (c : Lay) (hc : c.ok = true) {A B : Nat} (hA : Canon c.p c.d c.w A)
    (hB : Canon c.p c.d c.w B) :
    Canon c.p c.d c.w (c.mul A B) ∧
      ordMat c.p c.d c.w c.S (c.mul A B) = ordMat c.p c.d c.w c.S A * ordMat c.p c.d c.w c.S B :=
  mulR_sound hc hA hB

theorem vpow_spec (c : Lay) (hc : c.ok = true) {X : Nat} (hX : Canon c.p c.d c.w X) :
    ∀ (e : Nat) {v : Nat}, VCanon c.p c.d c.w v →
      VCanon c.p c.d c.w (c.vpow X v e) ∧
        toVec c.p c.d c.w (c.vpow X v e) = toVec c.p c.d c.w v ᵥ* ordMat c.p c.d c.w c.S X ^ e
  | 0, v, hv => ⟨hv, by
      change toVec c.p c.d c.w v = _
      rw [pow_zero, Matrix.vecMul_one]⟩
  | e + 1, v, hv => by
    obtain ⟨h1, h2⟩ := vpow_spec c hc hX e hv
    obtain ⟨h3, h4⟩ := vec_sound c hc h1 hX
    change VCanon c.p c.d c.w (c.vec (c.vpow X v e) X) ∧
      toVec c.p c.d c.w (c.vec (c.vpow X v e) X) = _
    refine ⟨h3, ?_⟩
    rw [h4, h2, Matrix.vecMul_vecMul, ← pow_succ]

theorem digApp_spec (c : Lay) (hc : c.ok = true) (X : Nat → Nat) :
    ∀ (m i : Nat), (∀ q < m, Canon c.p c.d c.w (X (i + q))) →
      ∀ (a : Fin m → Fin 3) {v : Nat}, VCanon c.p c.d c.w v →
        VCanon c.p c.d c.w (digApp c 3 X m i (CFSG.SectionRank.enc m a) v) ∧
          toVec c.p c.d c.w (digApp c 3 X m i (CFSG.SectionRank.enc m a) v) =
            toVec c.p c.d c.w v ᵥ*
              (List.ofFn fun q : Fin m => ordMat c.p c.d c.w c.S (X (i + q)) ^ (a q : Nat)).prod
  | 0, i, _, a, v, hv => ⟨hv, by
      change toVec c.p c.d c.w v = _
      simp⟩
  | m + 1, i, hX, a, v, hv => by
    have h0 := (a 0).isLt
    have hd : CFSG.SectionRank.enc (m + 1) a % 3 = (a 0 : Nat) := by
      rw [CFSG.SectionRank.enc]
      omega
    have hq : CFSG.SectionRank.enc (m + 1) a / 3 = CFSG.SectionRank.enc m (Fin.tail a) := by
      rw [CFSG.SectionRank.enc]
      omega
    have hXi : Canon c.p c.d c.w (X i) := by simpa using hX 0 (by omega)
    obtain ⟨w1, f1⟩ := vpow_spec c hc hXi (a 0 : Nat) hv
    obtain ⟨w2, f2⟩ := digApp_spec c hc X m (i + 1)
      (fun q hq' => by
        have := hX (q + 1) (by omega)
        have e : i + (q + 1) = i + 1 + q := by omega
        rwa [e] at this) (Fin.tail a) w1
    change VCanon c.p c.d c.w (digApp c 3 X m (i + 1) (CFSG.SectionRank.enc (m + 1) a / 3)
        (c.vpow (X i) v (CFSG.SectionRank.enc (m + 1) a % 3))) ∧
      toVec c.p c.d c.w (digApp c 3 X m (i + 1) (CFSG.SectionRank.enc (m + 1) a / 3)
        (c.vpow (X i) v (CFSG.SectionRank.enc (m + 1) a % 3))) = _
    rw [hd, hq, List.ofFn_succ, List.prod_cons]
    refine ⟨w2, ?_⟩
    rw [f2, f1, Matrix.vecMul_vecMul]
    refine congrArg (toVec c.p c.d c.w v ᵥ* ·) (congrArg₂ (· * ·) (by simp)
      (congrArg List.prod (congrArg List.ofFn (funext fun q => ?_))))
    have e : i + 1 + (q : Nat) = i + ((Fin.succ q : Fin (m + 1)) : Nat) := by
      rw [Fin.val_succ]
      omega
    rw [e]
    rfl

theorem isWs_eq (c : Char) :
    isWs c.toNat = CFSG.Blueprint.NativeSporadic.asciiWhitespace c := by
  rw [← ws_eq]
  unfold isWs CFSG.KC.Ord.ws CFSG.KC.Ord.orB
  cases CFSG.KC.Ord.andB (Nat.ble 9 c.toNat) (Nat.ble c.toNat 13) <;>
    cases Nat.beq c.toNat 32 <;> rfl

private theorem digit_eq (p : Nat) (c : Char) : Nat.mod (digitV c.toNat) p = dgv c % p := by
  rw [← ent_eq]
  unfold digitV CFSG.KC.Ord.ent
  cases CFSG.KC.Ord.andB (Nat.ble 48 c.toNat) (Nat.ble c.toNat 57)
  · exact Nat.zero_mod p
  · rfl

private theorem entsL_cons (c : Char) (B : List Char) :
    entsL (c :: B) = if CFSG.Blueprint.NativeSporadic.asciiWhitespace c then entsL B
      else dgv c :: entsL B := by
  cases h : CFSG.Blueprint.NativeSporadic.asciiWhitespace c <;> simp [entsL, h]

theorem decRun_cons0 (c : Lay) (M : Nat) (ch : Char) (B : List Char) (i j acc : Nat) :
    decRun c M (ch :: B) 0 i j acc = Bool.rec (motive := fun _ => Bool)
      (decRun c M B 0 i j acc) (decRun c M B 1 i j acc) (Nat.beq ch.toNat 10) := by
  have e : decRun c M (ch :: B) 0 i j acc = strictB ch.toNat (fun n =>
      Bool.rec (motive := fun _ => Bool) (decRun c M B 0 i j acc) (decRun c M B 1 i j acc)
        (Nat.beq n 10)) := rfl
  rw [e, strictB_eq]

theorem decRun_cons1 (c : Lay) (M : Nat) (ch : Char) (B : List Char) (i j acc : Nat) :
    decRun c M (ch :: B) 1 i j acc =
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (decRun c M B 1 i (j + 1)
              (acc + Nat.mod (digitV ch.toNat) c.p * 2 ^ (c.w * j)))
            (CFSG.KC.Ord.andB
              (Nat.beq (CFSG.KC.Ord.rowsOf c.S i 1 M)
                (acc + Nat.mod (digitV ch.toNat) c.p * 2 ^ (c.w * j)))
              (decRun c M B 1 (i + 1) 0 0))
            (Nat.beq (j + 1) c.d))
          (decRun c M B 1 i j acc) (Nat.ble c.d i))
        (decRun c M B 1 i j acc) (isWs ch.toNat) := by
  have e : decRun c M (ch :: B) 1 i j acc = strictB ch.toNat (fun n =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (strictB (Nat.add acc (Nat.shiftLeft (Nat.mod (digitV n) c.p) (Nat.mul c.w j)))
            fun a => strictB (Nat.succ j) fun j1 =>
              Bool.rec (motive := fun _ => Bool) (decRun c M B 1 i j1 a)
                (CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.Ord.rowsOf c.S i (nat_lit 1) M) a)
                  (strictB (Nat.succ i) fun i1 => decRun c M B 1 i1 0 0))
                (Nat.beq j1 c.d))
          (decRun c M B 1 i j acc) (Nat.ble c.d i))
        (decRun c M B 1 i j acc) (isWs n)) := rfl
  rw [e]
  simp only [strictB_eq]
  have e2 : Nat.add acc (Nat.shiftLeft (Nat.mod (digitV ch.toNat) c.p) (Nat.mul c.w j)) =
      acc + Nat.mod (digitV ch.toNat) c.p * 2 ^ (c.w * j) := by
    change acc + (Nat.mod (digitV ch.toNat) c.p) <<< (c.w * j) = _
    rw [Nat.shiftLeft_eq]
  rw [e2]

theorem decRun_ws {c : Lay} {M : Nat} {ch : Char} {B : List Char} {i j acc : Nat}
    (hws : isWs ch.toNat = true) : decRun c M (ch :: B) 1 i j acc = decRun c M B 1 i j acc := by
  rw [decRun_cons1, hws]

theorem decRun_past {c : Lay} {M : Nat} {ch : Char} {B : List Char} {i j acc : Nat}
    (hws : isWs ch.toNat = false) (hdi : Nat.ble c.d i = true) :
    decRun c M (ch :: B) 1 i j acc = decRun c M B 1 i j acc := by
  rw [decRun_cons1, hws, hdi]

theorem decRun_ent {c : Lay} {M : Nat} {ch : Char} {B : List Char} {i j acc : Nat}
    (hws : isWs ch.toNat = false) (hdi : Nat.ble c.d i = false) (hjd : Nat.beq (j + 1) c.d = false) :
    decRun c M (ch :: B) 1 i j acc =
      decRun c M B 1 i (j + 1) (acc + Nat.mod (digitV ch.toNat) c.p * 2 ^ (c.w * j)) := by
  rw [decRun_cons1, hws, hdi, hjd]

theorem decRun_row {c : Lay} {M : Nat} {ch : Char} {B : List Char} {i j acc : Nat}
    (hws : isWs ch.toNat = false) (hdi : Nat.ble c.d i = false) (hjd : Nat.beq (j + 1) c.d = true) :
    decRun c M (ch :: B) 1 i j acc =
      CFSG.KC.Ord.andB
        (Nat.beq (CFSG.KC.Ord.rowsOf c.S i 1 M)
          (acc + Nat.mod (digitV ch.toNat) c.p * 2 ^ (c.w * j)))
        (decRun c M B 1 (i + 1) 0 0) := by
  rw [decRun_cons1, hws, hdi, hjd]

theorem char_nl {ch : Char} (h : ch.toNat = 10) : ch = '\n' :=
  Char.ext (UInt32.toNat_inj.mp h)

theorem phase0 (c : Lay) (M i j acc : Nat) : ∀ l : List Char,
    decRun c M l 0 i j acc = decRun c M ((l.dropWhile (· != '\n')).drop 1) 1 i j acc
  | [] => rfl
  | ch :: l => by
    rw [decRun_cons0]
    cases h10 : Nat.beq ch.toNat 10
    · have e : Bool.rec (motive := fun _ => Bool) (decRun c M l 0 i j acc)
          (decRun c M l 1 i j acc) false = decRun c M l 0 i j acc := rfl
      rw [e, phase0 c M i j acc l]
      have hne : ch ≠ '\n' := by
        intro he
        rw [he] at h10
        exact absurd h10 (by decide)
      simp [hne]
    · have e : Bool.rec (motive := fun _ => Bool) (decRun c M l 0 i j acc)
          (decRun c M l 1 i j acc) true = decRun c M l 1 i j acc := rfl
      rw [e]
      have he := char_nl (Nat.eq_of_beq_eq_true h10)
      subst he
      simp

private theorem pk_getD (w p : Nat) (l : List Nat) {n : Nat} (hn : l.length ≤ n) :
    pk w n (fun t => (l[t]?.getD 0) % p) = pk w l.length (fun t => (l[t]?.getD 0) % p) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold pk
  rw [Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range k, (l[l.length + x]?.getD 0) % p * 2 ^ (w * (l.length + x)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [List.getElem?_eq_none (by omega)]
    simp
  rw [h0, Nat.add_zero]

private theorem pk_split (w m n : Nat) (f : Nat → Nat) :
    pk w (m + n) f = pk w m f + 2 ^ (w * m) * pk w n (fun t => f (m + t)) := by
  unfold pk
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.mul_add, Nat.pow_add]
  ring

private theorem pk_zero (w : Nat) (f : Nat → Nat) : pk w 0 f = 0 := by
  simp [pk]

private theorem bodyRun {c : Lay} {M : Nat} (hS : c.S = c.d * c.w) :
    ∀ (B : List Char) (i j acc : Nat) (pre : List Nat),
      ((i < c.d ∧ pre.length = j ∧ j < c.d) ∨ (i = c.d ∧ pre = [])) →
      acc = pk c.w pre.length (fun q => (pre[q]?.getD 0) % c.p) →
      decRun c M B 1 i j acc = true →
      M >>> (c.S * i) = pk c.w (c.d * (c.d - i)) (fun t => ((pre ++ entsL B)[t]?.getD 0) % c.p)
  | [], i, j, acc, pre, hinv, hacc, h => by
    have h' : Nat.beq (M >>> (c.S * i)) acc = true := h
    have hE0 : entsL ([] : List Char) = [] := rfl
    rw [Nat.eq_of_beq_eq_true h', hacc, hE0, List.append_nil]
    refine (pk_getD c.w c.p pre ?_).symm
    rcases hinv with ⟨hi, hl, hj⟩ | ⟨rfl, rfl⟩
    · have : 1 ≤ c.d - i := by omega
      have := Nat.mul_le_mul_left c.d this
      omega
    · simp
  | ch :: B, i, j, acc, pre, hinv, hacc, h => by
    cases hws : isWs ch.toNat
    · have hE : entsL (ch :: B) = dgv ch :: entsL B := by
        rw [entsL_cons, ← isWs_eq, hws]
        rfl
      rw [hE]
      cases hdi : Nat.ble c.d i
      · have hid : i < c.d := Nat.lt_of_not_le
          (Nat.not_le_of_not_ble_eq_true (by rw [hdi]; exact Bool.false_ne_true))
        rcases hinv with ⟨-, hl, hj⟩ | ⟨rfl, -⟩
        swap
        · omega
        subst hl
        have hacc' : acc + dgv ch % c.p * 2 ^ (c.w * pre.length) =
            pk c.w (pre ++ [dgv ch]).length
              (fun q => ((pre ++ [dgv ch])[q]?.getD 0) % c.p) := by
          rw [List.length_append, List.length_singleton, pk_succ, hacc]
          congr 1
          · refine pk_congr fun q hq => ?_
            rw [List.getElem?_append_left hq]
          · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
        have hL : pre ++ dgv ch :: entsL B = (pre ++ [dgv ch]) ++ entsL B := by simp
        rw [hL]
        cases hjd : Nat.beq (pre.length + 1) c.d
        · rw [decRun_ent hws hdi hjd, digit_eq] at h
          have hj1 : pre.length + 1 < c.d := by
            have := Nat.ne_of_beq_eq_false hjd
            omega
          exact bodyRun hS B i (pre.length + 1) _ (pre ++ [dgv ch])
            (Or.inl ⟨hid, by simp, hj1⟩) hacc' h
        · rw [decRun_row hws hdi hjd, digit_eq] at h
          obtain ⟨hrow, hrest⟩ := andT h
          have hj1 : pre.length + 1 = c.d := Nat.eq_of_beq_eq_true hjd
          have ih := bodyRun hS B (i + 1) 0 0 []
            (by
              rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hid) with h2 | h2
              · exact Or.inl ⟨h2, rfl, by omega⟩
              · exact Or.inr ⟨h2, rfl⟩) (pk_zero _ _).symm hrest
          rw [List.nil_append] at ih
          have hrow' : (M >>> (c.S * i)) % 2 ^ c.S =
              acc + dgv ch % c.p * 2 ^ (c.w * pre.length) := by
            have := Nat.eq_of_beq_eq_true hrow
            rw [← this]
            unfold CFSG.KC.Ord.rowsOf
            change _ = (M >>> (c.S * i)) &&& ((1 <<< (c.S * 1)) - 1)
            rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mul_one, Nat.and_two_pow_sub_one_eq_mod]
          have hshift : M >>> (c.S * (i + 1)) = (M >>> (c.S * i)) / 2 ^ c.S := by
            rw [Nat.mul_succ, Nat.shiftRight_add]
            exact Nat.shiftRight_eq_div_pow _ _
          have hdd : c.d * (c.d - i) = c.d + c.d * (c.d - (i + 1)) := by
            have : c.d - i = (c.d - (i + 1)) + 1 := by omega
            rw [this, Nat.mul_succ, Nat.add_comm]
          have hlen : (pre ++ [dgv ch]).length = c.d := by
            rw [List.length_append, List.length_singleton]
            exact hj1
          rw [← Nat.mod_add_div (M >>> (c.S * i)) (2 ^ c.S), hrow', ← hshift, ih, hdd, pk_split,
            hacc', hlen, hS, Nat.mul_comm c.d c.w]
          congr 1
          · refine pk_congr fun q hq => ?_
            have hq' : q < (pre ++ [dgv ch]).length := by
              rw [hlen]
              exact hq
            rw [List.getElem?_append_left hq']
          · congr 1
            refine pk_congr fun q _ => ?_
            have hq' : (pre ++ [dgv ch]).length ≤ c.d + q := by
              rw [hlen]
              omega
            rw [List.getElem?_append_right hq', hlen, Nat.add_sub_cancel_left]
      · rw [decRun_past hws hdi] at h
        have hid : c.d ≤ i := Nat.le_of_ble_eq_true hdi
        rcases hinv with ⟨hi, -⟩ | ⟨rfl, rfl⟩
        · omega
        have := bodyRun hS B c.d j acc [] (Or.inr ⟨rfl, rfl⟩) hacc h
        rw [Nat.sub_self, Nat.mul_zero, pk_zero] at this
        rw [Nat.sub_self, Nat.mul_zero, pk_zero]
        exact this
    · rw [decRun_ws hws] at h
      have hE : entsL (ch :: B) = entsL B := by
        rw [entsL_cons, ← isWs_eq, hws]
        rfl
      rw [hE]
      exact bodyRun hS B i j acc pre hinv hacc h

theorem decOK_sound (c : Lay) (hc : c.ok = true) {M : Nat} {l : List Char}
    (h : decOK c M l = true) :
    Canon c.p c.d c.w M ∧
      ordMat c.p c.d c.w c.S M = CFSG.Blueprint.NativeSporadic.decode c.p c.d 1 (String.ofList l) := by
  obtain ⟨hp, hS, hw, -, hT, -⟩ := consts_facts hc
  have hp2 : c.p ≤ 2 ^ (c.w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right c.p (Nat.two_pow_pos c.T)) hT
  have e2 := two_pow_pred hw
  have hpw : c.p ≤ 2 ^ c.w := by omega
  have h0 : decRun c M ((l.dropWhile (· != '\n')).drop 1) 1 0 0 0 = true := by
    rw [← phase0]
    exact h
  have hM := bodyRun hS _ 0 0 0 []
    (by
      rcases Nat.eq_zero_or_pos c.d with hd | hd
      · exact Or.inr ⟨hd.symm, rfl⟩
      · exact Or.inl ⟨hd, rfl, hd⟩) (pk_zero _ _).symm h0
  rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.sub_zero, List.nil_append] at hM
  have hg : ∀ t < c.d * c.d,
      ((entsL ((l.dropWhile (· != '\n')).drop 1))[t]?.getD 0) % c.p < c.p :=
    fun t _ => Nat.mod_lt _ (by omega)
  rw [hM]
  refine ⟨canon_pk hg hpw, ?_⟩
  rw [hS]
  funext i j
  rw [ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) hpw), ZMod.natCast_mod]
  unfold CFSG.Blueprint.NativeSporadic.decode
  simp only [↓reduceIte, String.toList_ofList]
  change _ = ((entsL ((l.dropWhile (· != '\n')).drop 1))[i.val * c.d + j.val]?.getD 0 : ZMod c.p)
  rw [Nat.mul_comm c.d i.val]

theorem vals_sound (c : Lay) (hc : c.ok = true) {LA LB : List Char} {V P : Nat → Nat} {N : Nat}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) : ∀ n < N, Canon c.p c.d c.w (V n) ∧
      ordMat c.p c.d c.w c.S (V n) ∈
        CFSG.Blueprint.NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB) := by
  unfold StepsTo at hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | rfl | h3
    · obtain ⟨h1, h2⟩ := decOK_sound c hc hA
      refine ⟨h1, ?_⟩
      rw [h2]
      exact Submonoid.subset_closure (Set.mem_insert _ _)
    · obtain ⟨h1, h2⟩ := decOK_sound c hc hB
      refine ⟨h1, ?_⟩
      rw [h2]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [h1]
      obtain ⟨h1', h2'⟩ := one_sound hc
      refine ⟨h1', ?_⟩
      rw [h2']
      exact Submonoid.one_mem _
    · have hst := hs n h3 hn
      unfold stepOK at hst
      simp only [strictB_eq] at hst
      obtain ⟨ha, hst⟩ := andT hst
      obtain ⟨hb, hst⟩ := andT hst
      have ha' := Nat.blt_eq.mp ha
      have hb' := Nat.blt_eq.mp hb
      have hV := Nat.eq_of_beq_eq_true hst
      obtain ⟨cA, mA⟩ := ih _ ha' (by omega)
      obtain ⟨cB, mB⟩ := ih _ hb' (by omega)
      obtain ⟨cAB, eAB⟩ := mul_sound c hc cA cB
      rw [hV]
      refine ⟨cAB, ?_⟩
      rw [eAB]
      exact Submonoid.mul_mem _ mA mB

theorem pow_sound (c : Lay) (hc : c.ok = true) {X : Nat} (hX : Canon c.p c.d c.w X) :
    ∀ e : Nat, Canon c.p c.d c.w (c.pow X e) ∧
      ordMat c.p c.d c.w c.S (c.pow X e) = ordMat c.p c.d c.w c.S X ^ e
  | 0 => by
    obtain ⟨h1, h2⟩ := one_sound hc
    exact ⟨h1, by rw [pow_zero]; exact h2⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := pow_sound c hc hX e
    obtain ⟨h3, h4⟩ := mul_sound c hc h1 hX
    change Canon c.p c.d c.w (c.mul (c.pow X e) X) ∧
      ordMat c.p c.d c.w c.S (c.mul (c.pow X e) X) = _
    exact ⟨h3, by rw [h4, h2, pow_succ]⟩

theorem mat_of_beq (c : Lay) {A B : Nat} (h : Nat.beq A B = true) :
    ordMat c.p c.d c.w c.S A = ordMat c.p c.d c.w c.S B := by
  rw [Nat.eq_of_beq_eq_true h]

theorem pow_one_of (c : Lay) (hc : c.ok = true) {X e : Nat} (hX : Canon c.p c.d c.w X)
    (h : Nat.beq (c.pow X e) c.ONE = true) : ordMat c.p c.d c.w c.S X ^ e = 1 := by
  have h2 := mat_of_beq c h
  rwa [(pow_sound c hc hX e).2, (one_sound hc).2] at h2

theorem mul_eq_of (c : Lay) (hc : c.ok = true) {A B C D : Nat} (hA : Canon c.p c.d c.w A)
    (hB : Canon c.p c.d c.w B) (hC : Canon c.p c.d c.w C) (hD : Canon c.p c.d c.w D)
    (h : Nat.beq (c.mul A B) (c.mul C D) = true) :
    ordMat c.p c.d c.w c.S A * ordMat c.p c.d c.w c.S B =
      ordMat c.p c.d c.w c.S C * ordMat c.p c.d c.w c.S D := by
  have h2 := mat_of_beq c h
  rwa [(mul_sound c hc hA hB).2, (mul_sound c hc hC hD).2] at h2

theorem conj_mat (c : Lay) (hc : c.ok = true) {H X W : Nat} (hH : Canon c.p c.d c.w H)
    (hX : Canon c.p c.d c.w X) (hW : Canon c.p c.d c.w W) (h : conjOK c H X W = true) :
    ordMat c.p c.d c.w c.S H * ordMat c.p c.d c.w c.S X =
      ordMat c.p c.d c.w c.S W * ordMat c.p c.d c.w c.S H :=
  mul_eq_of c hc hH hX hW hH h

theorem vec_unit_eq (c : Lay) (hc : c.ok = true) {t X Y : Nat} (ht : t < c.d)
    (hX : Canon c.p c.d c.w X) (hY : Canon c.p c.d c.w Y)
    (h : ordMat c.p c.d c.w c.S X = ordMat c.p c.d c.w c.S Y) :
    c.vec (c.unit t) X = c.vec (c.unit t) Y := by
  have hu := unit_canon c hc ht
  obtain ⟨w1, f1⟩ := vec_sound c hc hu hX
  obtain ⟨w2, f2⟩ := vec_sound c hc hu hY
  exact vec_inj (lay_w_pos c hc) w1 w2 (by rw [f1, f2, h])

theorem mat_ne_one (c : Lay) (hc : c.ok = true) {t Z : Nat} (ht : t < c.d)
    (hZ : Canon c.p c.d c.w Z) (h : CFSG.KC.Ord.notB (Nat.beq (c.vec (c.unit t) Z) (c.unit t)) = true) :
    ordMat c.p c.d c.w c.S Z ≠ 1 := by
  intro h1
  have hu := unit_canon c hc ht
  obtain ⟨w1, f1⟩ := vec_sound c hc hu hZ
  exact ne_of_notB h (vec_inj (lay_w_pos c hc) w1 hu (by rw [f1, h1, Matrix.vecMul_one]))

theorem notMem_spec (c : Lay) {V E : Nat → Nat} {n t X : Nat} (h : notMemOK c V E n t X = true) :
    ∀ i < n, c.vec (c.unit t) X ≠ c.vec (c.unit t) (V (E i)) := by
  unfold notMemOK at h
  rw [strictB_eq] at h
  exact fun i hi => ne_of_notB (allLt_spec h i hi)

theorem sortRun_cons (N : Nat) (f : Nat → Nat) (k : Nat) (σ : List Nat) (lo mask : Nat) :
    sortRun N f (k :: σ) lo mask = CFSG.KC.Ord.andB (Nat.blt k N)
      (CFSG.KC.Ord.andB (Nat.beq (mask &&& 1 <<< k) 0)
        (CFSG.KC.Ord.andB (Nat.ble lo (f k)) (sortRun N f σ (f k + 1) (mask ||| 1 <<< k)))) := by
  have e : sortRun N f (k :: σ) lo mask = strictB (f k) fun v =>
      CFSG.KC.Ord.andB (Nat.blt k N) (CFSG.KC.Ord.andB (Nat.beq (mask &&& 1 <<< k) 0)
        (CFSG.KC.Ord.andB (Nat.ble lo v) (strictB (mask ||| 1 <<< k) fun m1 =>
          sortRun N f σ (v + 1) m1))) := rfl
  rw [e, strictB_eq, strictB_eq]

theorem sortRun_spec (N : Nat) (f : Nat → Nat) : ∀ (σ : List Nat) (lo mask : Nat),
    sortRun N f σ lo mask = true →
      (∀ n < N, mask.testBit n = true ∨ n ∈ σ) ∧ (∀ k ∈ σ, lo ≤ f k) ∧
        σ.Pairwise (fun a b => f a < f b)
  | [], lo, mask, h => by
    have e : mask = 2 ^ N - 1 := by
      have h' : Nat.beq mask (1 <<< N - 1) = true := h
      rw [Nat.eq_of_beq_eq_true h', Nat.shiftLeft_eq, Nat.one_mul]
    refine ⟨fun n hn => Or.inl ?_, fun k hk => by simp at hk, List.Pairwise.nil⟩
    rw [e, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hn
  | k :: σ, lo, mask, h => by
    rw [sortRun_cons] at h
    obtain ⟨-, h⟩ := andT h
    obtain ⟨-, h⟩ := andT h
    obtain ⟨hlo, h⟩ := andT h
    obtain ⟨h1, h2, h3⟩ := sortRun_spec N f σ _ _ h
    have hlo' := Nat.le_of_ble_eq_true hlo
    refine ⟨fun n hn => ?_, fun m hm => ?_, List.Pairwise.cons (fun m hm => ?_) h3⟩
    · rcases h1 n hn with h4 | h4
      · rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
          decide_eq_true_eq] at h4
        rcases h4 with h4 | rfl
        · exact Or.inl h4
        · exact Or.inr (by simp)
      · exact Or.inr (List.mem_cons_of_mem _ h4)
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hlo'
      · have := h2 m hm
        omega
    · have := h2 m hm
      omega

theorem pairwise_inj {f : Nat → Nat} {σ : List Nat} (h : σ.Pairwise (fun a b => f a < f b))
    {a b : Nat} (ha : a ∈ σ) (hb : b ∈ σ) (hab : f a = f b) : a = b := by
  induction σ with
  | nil => simp at ha
  | cons k σ ih =>
    obtain ⟨h0, h1⟩ := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd hab (Nat.ne_of_lt (h0 b hb'))
    · exact absurd hab (Nat.ne_of_lt (h0 a ha')).symm
    · exact ih h1 ha' hb'

theorem sortRun_inj {N : Nat} {f : Nat → Nat} {σ : List Nat} (h : sortRun N f σ 0 0 = true)
    {i j : Nat} (hi : i < N) (hj : j < N) (hij : f i = f j) : i = j := by
  obtain ⟨h1, -, h3⟩ := sortRun_spec N f σ 0 0 h
  have mi := (h1 i hi).resolve_left (by simp)
  have mj := (h1 j hj).resolve_left (by simp)
  exact pairwise_inj h3 mi mj hij

theorem addMul_lt {r i m n : Nat} (hi : i < r) (hm : m < n) : i + r * m < r * n :=
  calc i + r * m < r + r * m := by omega
    _ = r * (m + 1) := by ring
    _ ≤ r * n := Nat.mul_le_mul_left _ hm

theorem digApp_two (c : Lay) (b X Y Z n v : Nat) :
    digApp c b (sel3 X Y Z) 2 0 n v = c.vpow Y (c.vpow X v (n % b)) (n / b % b) := rfl

theorem digApp_three (c : Lay) (b X Y Z n v : Nat) :
    digApp c b (sel3 X Y Z) 3 0 n v =
      c.vpow Z (c.vpow Y (c.vpow X v (n % b)) (n / b % b)) (n / b / b % b) := rfl

theorem vpow_two (c : Lay) (hc : c.ok = true) {X Y v : Nat} (hX : Canon c.p c.d c.w X)
    (hY : Canon c.p c.d c.w Y) (hv : VCanon c.p c.d c.w v) (e1 e2 : Nat) :
    VCanon c.p c.d c.w (c.vpow Y (c.vpow X v e1) e2) ∧
      toVec c.p c.d c.w (c.vpow Y (c.vpow X v e1) e2) = toVec c.p c.d c.w v ᵥ*
        (ordMat c.p c.d c.w c.S X ^ e1 * ordMat c.p c.d c.w c.S Y ^ e2) := by
  obtain ⟨w1, f1⟩ := vpow_spec c hc hX e1 hv
  obtain ⟨w2, f2⟩ := vpow_spec c hc hY e2 w1
  exact ⟨w2, by rw [f2, f1, Matrix.vecMul_vecMul]⟩

theorem vpow_three (c : Lay) (hc : c.ok = true) {X Y Z v : Nat} (hX : Canon c.p c.d c.w X)
    (hY : Canon c.p c.d c.w Y) (hZ : Canon c.p c.d c.w Z) (hv : VCanon c.p c.d c.w v)
    (e1 e2 e3 : Nat) :
    VCanon c.p c.d c.w (c.vpow Z (c.vpow Y (c.vpow X v e1) e2) e3) ∧
      toVec c.p c.d c.w (c.vpow Z (c.vpow Y (c.vpow X v e1) e2) e3) = toVec c.p c.d c.w v ᵥ*
        (ordMat c.p c.d c.w c.S X ^ e1 * ordMat c.p c.d c.w c.S Y ^ e2 *
          ordMat c.p c.d c.w c.S Z ^ e3) := by
  obtain ⟨w1, f1⟩ := vpow_spec c hc hX e1 hv
  obtain ⟨w2, f2⟩ := vpow_spec c hc hY e2 w1
  obtain ⟨w3, f3⟩ := vpow_spec c hc hZ e3 w2
  exact ⟨w3, by rw [f3, f2, f1, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]⟩

theorem normal2_inj (c : Lay) (hc : c.ok = true) {X Y r t : Nat} {σ : List Nat}
    (hX : Canon c.p c.d c.w X) (hY : Canon c.p c.d c.w Y) (hr : 0 < r)
    (h : normalOK c r (sel3 X Y Y) 2 t σ = true) {i j i' j' : Nat} (hi : i < r) (hj : j < r)
    (hi' : i' < r) (hj' : j' < r)
    (he : ordMat c.p c.d c.w c.S X ^ i * ordMat c.p c.d c.w c.S Y ^ j =
      ordMat c.p c.d c.w c.S X ^ i' * ordMat c.p c.d c.w c.S Y ^ j') : i = i' ∧ j = j' := by
  obtain ⟨ht, hs⟩ := andT h
  have hu := unit_canon c hc (Nat.blt_eq.mp ht)
  have e1 : ∀ {i j : Nat}, i < r → (i + r * j) % r = i := fun hi => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have e2 : ∀ {i j : Nat}, i < r → j < r → (i + r * j) / r % r = j := fun hi hj => by
    rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hi, Nat.zero_add, Nat.mod_eq_of_lt hj]
  have hlt : ∀ {i j : Nat}, i < r → j < r → i + r * j < r ^ 2 := fun hi hj => by
    rw [Nat.pow_two]
    exact addMul_lt hi hj
  have hF : ∀ {i j : Nat}, i < r → j < r →
      VCanon c.p c.d c.w (digApp c r (sel3 X Y Y) 2 0 (i + r * j) (c.unit t)) ∧
      toVec c.p c.d c.w (digApp c r (sel3 X Y Y) 2 0 (i + r * j) (c.unit t)) =
        toVec c.p c.d c.w (c.unit t) ᵥ*
          (ordMat c.p c.d c.w c.S X ^ i * ordMat c.p c.d c.w c.S Y ^ j) := by
    intro i j hi hj
    rw [digApp_two, e1 hi, e2 hi hj]
    exact vpow_two c hc hX hY hu i j
  obtain ⟨w1, f1⟩ := hF hi hj
  obtain ⟨w2, f2⟩ := hF hi' hj'
  have hN : i + r * j = i' + r * j' := sortRun_inj hs (hlt hi hj) (hlt hi' hj')
    (vec_inj (lay_w_pos c hc) w1 w2 (by rw [f1, f2, he]))
  exact ⟨by rw [← e1 (j := j) hi, ← e1 (j := j') hi', hN],
    by rw [← e2 hi hj, ← e2 hi' hj', hN]⟩

theorem normal3_inj (c : Lay) (hc : c.ok = true) {X Y Z r t : Nat} {σ : List Nat}
    (hX : Canon c.p c.d c.w X) (hY : Canon c.p c.d c.w Y) (hZ : Canon c.p c.d c.w Z) (hr : 0 < r)
    (h : normalOK c r (sel3 X Y Z) 3 t σ = true) {i j k i' j' k' : Nat} (hi : i < r) (hj : j < r)
    (hk : k < r) (hi' : i' < r) (hj' : j' < r) (hk' : k' < r)
    (he : ordMat c.p c.d c.w c.S X ^ i * ordMat c.p c.d c.w c.S Y ^ j *
        ordMat c.p c.d c.w c.S Z ^ k =
      ordMat c.p c.d c.w c.S X ^ i' * ordMat c.p c.d c.w c.S Y ^ j' *
        ordMat c.p c.d c.w c.S Z ^ k') : i = i' ∧ j = j' ∧ k = k' := by
  obtain ⟨ht, hs⟩ := andT h
  have hu := unit_canon c hc (Nat.blt_eq.mp ht)
  have e1 : ∀ {i j k : Nat}, i < r → (i + r * (j + r * k)) % r = i := fun hi => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have e2 : ∀ {i j k : Nat}, i < r → j < r → (i + r * (j + r * k)) / r % r = j := fun hi hj => by
    rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hi, Nat.zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj]
  have e3 : ∀ {i j k : Nat}, i < r → j < r → k < r → (i + r * (j + r * k)) / r / r % r = k :=
    fun hi hj hk => by
      rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hi, Nat.zero_add,
        Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hj, Nat.zero_add, Nat.mod_eq_of_lt hk]
  have hlt : ∀ {i j k : Nat}, i < r → j < r → k < r → i + r * (j + r * k) < r ^ 3 :=
    fun hi hj hk => by
      rw [pow_three]
      exact addMul_lt hi (addMul_lt hj hk)
  have hF : ∀ {i j k : Nat}, i < r → j < r → k < r →
      VCanon c.p c.d c.w (digApp c r (sel3 X Y Z) 3 0 (i + r * (j + r * k)) (c.unit t)) ∧
      toVec c.p c.d c.w (digApp c r (sel3 X Y Z) 3 0 (i + r * (j + r * k)) (c.unit t)) =
        toVec c.p c.d c.w (c.unit t) ᵥ* (ordMat c.p c.d c.w c.S X ^ i *
          ordMat c.p c.d c.w c.S Y ^ j * ordMat c.p c.d c.w c.S Z ^ k) := by
    intro i j k hi hj hk
    rw [digApp_three, e1 hi, e2 hi hj, e3 hi hj hk]
    exact vpow_three c hc hX hY hZ hu i j k
  obtain ⟨w1, f1⟩ := hF hi hj hk
  obtain ⟨w2, f2⟩ := hF hi' hj' hk'
  have hN : i + r * (j + r * k) = i' + r * (j' + r * k') :=
    sortRun_inj hs (hlt hi hj hk) (hlt hi' hj' hk')
      (vec_inj (lay_w_pos c hc) w1 w2 (by rw [f1, f2, he]))
  exact ⟨by rw [← e1 (j := j) (k := k) hi, ← e1 (j := j') (k := k') hi', hN],
    by rw [← e2 (k := k) hi hj, ← e2 (k := k') hi' hj', hN],
    by rw [← e3 hi hj hk, ← e3 hi' hj' hk', hN]⟩

end CFSG.KC.LQT.SecS

end
