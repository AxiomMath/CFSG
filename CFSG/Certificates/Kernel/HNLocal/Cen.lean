module

public import CFSG.Certificates.Kernel.HNLocal.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.HNLocal.CenPf

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord CFSG.KS.HNLocal Matrix

private theorem andT {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KC.Ord.andB]

private theorem bAndT {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

private def VCanon (p d w v : Nat) : Prop := v < 2 ^ (w * d) ∧ ∀ j < d, lane w v j < p

private noncomputable def toVec (p d w v : Nat) : Fin d → ZMod p :=
  fun j => ((lane w v j.val : Nat) : ZMod p)

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

private theorem vecU_eq (w S d RM v M : Nat) : CFSG.KC.Ord.vecU w S d RM v M =
    ∑ k ∈ Finset.range d, CFSG.KC.Ord.bitsN v (w * k) w * ((M >>> (S * k)) &&& RM) := by
  unfold CFSG.KC.Ord.vecU
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

private theorem bitsN_lane (v w k : Nat) : CFSG.KC.Ord.bitsN v (w * k) w = lane w v k := by
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

private theorem vecR_sound {p w S d T L H CM RM ONE LV HV v M : Nat}
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

private theorem vec_inj {p d w : Nat} (hw : 0 < w) {u v : Nat} (hu : VCanon p d w u)
    (hv : VCanon p d w v) (h : toVec p d w u = toVec p d w v) : u = v := by
  rw [pk_lane hw hu.1, pk_lane hw hv.1]
  refine pk_congr fun t ht => ?_
  have h3 := congrFun h ⟨t, ht⟩
  simp only [toVec] at h3
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  rwa [Nat.mod_eq_of_lt (hu.2 t ht), Nat.mod_eq_of_lt (hv.2 t ht)] at h3

private theorem row_spec {p w S d T L H CM RM ONE LV HV M a : Nat}
    (hc : CFSG.KC.Ord.constsOK p w S d T L H CM RM ONE LV HV = true) (hM : Canon p d w M)
    (ha : a < d) :
    VCanon p d w ((M >>> (S * a)) &&& RM) ∧
      toVec p d w ((M >>> (S * a)) &&& RM) = fun j => ordMat p d w S M ⟨a, ha⟩ j := by
  obtain ⟨hp, hS, hw, -, hT, -, -, -, -, hRM, -⟩ := consts_facts hc
  subst hS hRM
  obtain ⟨b, rfl, hb⟩ : ∃ b, M = pk w (d * d) b ∧ ∀ t < d * d, b t < p :=
    ⟨lane w M, pk_lane hw hM.1, hM.2⟩
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  have hb' : ∀ t < d * d, b t < 2 ^ w := fun t ht => Nat.lt_of_lt_of_le (hb t ht) hpw
  rw [row_eq hw hb' ha]
  refine ⟨vcanon_pk (fun t ht => hb _ (idx_lt ha ht)) hpw, ?_⟩
  funext j
  simp only [toVec]
  rw [lane_pk (fun t ht => hb' _ (idx_lt ha ht)) j.isLt, ordMat_pk hb']

private theorem unit_spec {p d w a : Nat} (hp : 2 ≤ p) (hpw : p ≤ 2 ^ w) (ha : a < d) :
    VCanon p d w (1 <<< (w * a)) ∧
      toVec p d w (1 <<< (w * a)) = fun j => if j.val = a then 1 else 0 := by
  have e : 1 <<< (w * a) = pk w d (fun t => if t = a then 1 else 0) := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    unfold pk
    simp [ha]
  have hg : ∀ t < d, (if t = a then 1 else 0) < p := fun t _ => by split <;> omega
  have hg' : ∀ t < d, (if t = a then 1 else 0) < 2 ^ w :=
    fun t ht => Nat.lt_of_lt_of_le (hg t ht) hpw
  rw [e]
  refine ⟨vcanon_pk hg hpw, ?_⟩
  funext j
  simp only [toVec]
  rw [lane_pk hg' j.isLt]
  split <;> simp

private theorem rec_inv {s : Nat → Nat → Nat} {x : Nat} {Q : Nat → Nat → Prop} (h0 : Q 0 x)
    (hs : ∀ i a, Q i a → Q (i + 1) (s i a)) : ∀ m, Q m (Nat.rec (motive := fun _ => Nat) x s m)
  | 0 => h0
  | m + 1 => hs m _ (rec_inv h0 hs m)

private theorem shr_split (e n : Nat) : e >>> n = 2 * (e >>> (n + 1)) + (e >>> n) % 2 := by
  have h : e >>> (n + 1) = (e >>> n) / 2 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [h]
  exact (Nat.div_add_mod _ 2).symm

private theorem bit_mod {e n : Nat} (hn : n < 16) : (e >>> n) % 2 = ((e % 2 ^ 16) >>> n) % 2 := by
  have h1 : e = e % 2 ^ 16 + 2 ^ n * (2 ^ (16 - n) * (e / 2 ^ 16)) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    exact (Nat.mod_add_div e _).symm
  have h2 : 2 ^ (16 - n) = 2 * 2 ^ (15 - n) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  conv_lhs => rw [h1]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), h2, Nat.mul_assoc, Nat.add_mul_mod_self_left]

private noncomputable def powStep (mul : Nat → Nat → Nat) (ONE M e : Nat) (i acc : Nat) : Nat :=
  CFSG.KC.Loop.strictN acc (fun a =>
      (fun sq => Bool.rec (motive := fun _ => Nat) sq
          (Bool.rec (motive := fun _ => Nat) (mul sq M) M (Nat.beq sq ONE))
          (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) (nat_lit 1)) (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (mul a a) a (Nat.beq a ONE)))

private theorem powR_eq (mul : Nat → Nat → Nat) (ONE M e : Nat) :
    powR mul ONE M e = Nat.rec (motive := fun _ => Nat) ONE (powStep mul ONE M e) 16 :=
  rfl

private theorem powR_sem {R : Type} [Monoid R] {mul : Nat → Nat → Nat} {ONE X e : Nat}
    {P : Nat → Prop} {F : Nat → R}
    (hmul : ∀ A B, P A → P B → P (mul A B) ∧ F (mul A B) = F A * F B) (h1 : P ONE)
    (h1' : F ONE = 1) (hX : P X) :
    P (powR mul ONE X e) ∧ F (powR mul ONE X e) = F X ^ (e % 2 ^ 16) := by
  have hfin : ∀ a, (16 ≤ 16 → P a ∧ F a = F X ^ ((e % 2 ^ 16) >>> (16 - 16))) →
      P a ∧ F a = F X ^ (e % 2 ^ 16) := by
    intro a h
    simpa using h le_rfl
  rw [powR_eq]
  apply hfin
  refine rec_inv (s := powStep mul ONE X e) (x := ONE)
    (Q := fun i a => i ≤ 16 → P a ∧ F a = F X ^ ((e % 2 ^ 16) >>> (16 - i))) ?_ ?_ 16
  · intro _
    have e16 : (e % 2 ^ 16) >>> (16 - 0) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num))
    rw [e16, pow_zero]
    exact ⟨h1, h1'⟩
  · intro i a ih hi
    obtain ⟨hPa, hMa⟩ := ih (by omega)
    unfold powStep
    rw [strictN_eq]
    dsimp only
    obtain ⟨sq, hsq, hPs, hMs⟩ : ∃ sq, Bool.rec (motive := fun _ => Nat) (mul a a) a
        (Nat.beq a ONE) = sq ∧ P sq ∧ F sq = F X ^ (2 * ((e % 2 ^ 16) >>> (16 - i))) := by
      cases hq : Nat.beq a ONE
      · obtain ⟨h2, h3⟩ := hmul a a hPa hPa
        exact ⟨_, rfl, h2, by rw [h3, hMa, ← pow_add, two_mul]⟩
      · have ha : a = ONE := Nat.eq_of_beq_eq_true hq
        refine ⟨_, rfl, hPa, ?_⟩
        rw [two_mul, pow_add, ← hMa, ha, h1', one_mul]
    rw [hsq]
    have hsplit := shr_split (e % 2 ^ 16) (15 - i)
    have e1 : 15 - i + 1 = 16 - i := by omega
    have e2 : 16 - (i + 1) = 15 - i := by omega
    rw [e1] at hsplit
    rw [e2]
    have hy : Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) (nat_lit 1) =
        ((e % 2 ^ 16) >>> (15 - i)) % 2 :=
      (Nat.and_one_is_mod _).trans (bit_mod (n := 15 - i) (by omega))
    rw [hy]
    rcases Nat.mod_two_eq_zero_or_one ((e % 2 ^ 16) >>> (15 - i)) with hb | hb
    · rw [hb]
      refine ⟨hPs, ?_⟩
      change F sq = F X ^ ((e % 2 ^ 16) >>> (15 - i))
      rw [hsplit, hb, Nat.add_zero, hMs]
    · rw [hb]
      change P (Bool.rec (motive := fun _ => Nat) (mul sq X) X (Nat.beq sq ONE)) ∧
        F (Bool.rec (motive := fun _ => Nat) (mul sq X) X (Nat.beq sq ONE)) =
          F X ^ ((e % 2 ^ 16) >>> (15 - i))
      rw [hsplit, hb, pow_succ, ← hMs]
      cases hq : Nat.beq sq ONE
      · exact hmul sq X hPs hX
      · have hs1 : sq = ONE := Nat.eq_of_beq_eq_true hq
        refine ⟨hX, ?_⟩
        rw [hs1, h1', one_mul]

private theorem powR_mat {p w S d T L H CM RM ONE LV HV : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {X e : Nat} (hX : Canon p d w X) :
    Canon p d w (powR (mulR p w S d T L H CM RM) ONE X e) ∧
      ordMat p d w S (powR (mulR p w S d T L H CM RM) ONE X e) = ordMat p d w S X ^ (e % 2 ^ 16) :=
  powR_sem (fun _ _ hA hB => mulR_sound hc hA hB) (one_sound hc).1 (one_sound hc).2 hX

private theorem nfE_zero (PC : Nat → Nat) (e : Nat → Nat) : nfE PC 0 e = 1 := by
  simp [nfE]

private theorem nfE_succ (PC : Nat → Nat) (n : Nat) (e : Nat → Nat) :
    nfE PC (n + 1) e = nfE PC n e * OM (PC n) ^ e n := by
  unfold nfE
  rw [List.range'_concat, List.map_append, List.prod_append]
  simp

private theorem nfE_congr (PC : Nat → Nat) {e e' : Nat → Nat} :
    ∀ n, (∀ i < n, e i = e' i) → nfE PC n e = nfE PC n e'
  | 0, _ => by rw [nfE_zero, nfE_zero]
  | n + 1, h => by
    rw [nfE_succ, nfE_succ, nfE_congr PC n (fun i hi => h i (by omega)), h n (by omega)]

variable {L H CM RM ONE LV HV : Nat} {PC RP TG : Nat → Nat} {np : Nat}

private theorem nfPre_succ (mul : Nat → Nat → Nat) (PC : Nat → Nat) (ONE e k : Nat) :
    nfPre mul PC ONE e (k + 1) = CFSG.KC.Loop.strictN (nfPre mul PC ONE e k) (fun a =>
      Bool.rec (motive := fun _ => Nat) a (mul a (PC k))
        (Nat.beq (Nat.land (Nat.shiftRight e k) 1) 1)) :=
  rfl

private theorem nfPre_ok (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (m : Nat) :
    ∀ k, (∀ i < k, Canon 5 133 13 (PC i)) →
      Canon 5 133 13 (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) ∧
        OM (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) = nfE PC k (fun i => m / 2 ^ i % 2)
  | 0, _ => ⟨(one_sound hc).1, by rw [nfE_zero]; exact (one_sound hc).2⟩
  | k + 1, hPC => by
    obtain ⟨ih1, ih2⟩ := nfPre_ok hc m k (fun i hi => hPC i (by omega))
    have e1 : nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m (k + 1) =
        Bool.rec (motive := fun _ => Nat) (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k)
          (mulR 5 13 1729 133 9 L H CM RM (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) (PC k))
          (Nat.beq (Nat.land (Nat.shiftRight m k) 1) 1) := by
      rw [nfPre_succ, strictN_eq]
    have hland : Nat.land (Nat.shiftRight m k) 1 = m / 2 ^ k % 2 := by
      show (m >>> k) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    rw [e1, hland, nfE_succ]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with hb | hb
    · rw [hb]
      refine ⟨ih1, ?_⟩
      show OM (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) = _
      simp only [hb, pow_zero, mul_one, ih2]
    · rw [hb]
      obtain ⟨h1, h2⟩ := mulR_sound hc ih1 (hPC k (by omega))
      refine ⟨h1, ?_⟩
      have h2' : OM (mulR 5 13 1729 133 9 L H CM RM
          (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) (PC k)) =
          OM (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) * OM (PC k) := h2
      have e3 : Bool.rec (motive := fun _ => Nat) (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k)
          (mulR 5 13 1729 133 9 L H CM RM (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) (PC k))
          (Nat.beq 1 1) =
          mulR 5 13 1729 133 9 L H CM RM (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) (PC k) :=
        rfl
      rw [e3, h2', ih2, pow_one]

private theorem elem_ok (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hRP : ∀ a < np, Canon 5 133 13 (RP a)) {M tg : Nat} (hM : Canon 5 133 13 M)
    (h : elemOK (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) RP np ONE RM M tg
      = true) :
    OM M = 1 ∨ OM M * OM M ≠ 1 ∨
      ∃ a < np, ∃ q, q % 2 = 1 ∧ (OM M * OM (RP a)) ^ q = 1 := by
  unfold elemOK at h
  generalize Nat.land tg 3 = k at h
  generalize Nat.land (Nat.shiftRight tg 2) 255 = a at h
  generalize Nat.shiftRight tg 10 = m at h
  beta_reduce at h
  cases hk0 : Nat.beq k 0
  · rw [hk0] at h
    dsimp only at h
    cases hk1 : Nat.beq k 1
    · rw [hk1] at h
      dsimp only at h
      cases hk2 : Nat.beq k 2
      · rw [hk2] at h
        exact absurd h (by simp)
      · rw [hk2] at h
        dsimp only at h
        obtain ⟨ha, h⟩ := andT h
        obtain ⟨hm, hp⟩ := andT h
        have ha' : a < np := Nat.le_of_ble_eq_true ha
        have hm' : m % 2 = 1 := Nat.eq_of_beq_eq_true hm
        have hp' := Nat.eq_of_beq_eq_true hp
        obtain ⟨hX, hXm⟩ := mulR_sound hc hM (hRP a ha')
        obtain ⟨-, hpow⟩ := powR_mat (e := m) hc hX
        refine Or.inr (Or.inr ⟨a, ha', m % 2 ^ 16, ?_, ?_⟩)
        · rw [Nat.mod_mod_of_dvd m (by norm_num : 2 ∣ 2 ^ 16)]
          exact hm'
        · have := hpow.symm
          rw [hp', (one_sound hc).2] at this
          change (ordMat 5 133 13 1729 M * ordMat 5 133 13 1729 (RP a)) ^ (m % 2 ^ 16) = 1
          rw [← hXm]
          exact this
    · rw [hk1] at h
      dsimp only at h
      obtain ⟨ha, hn⟩ := andT h
      have ha' : a < 133 := Nat.le_of_ble_eq_true ha
      refine Or.inr (Or.inl fun hsq => ?_)
      have hne : vecR 5 13 1729 133 9 LV HV RM (rowL RM M a) M ≠ 1 <<< (13 * a) := by
        intro heq
        have : Nat.beq (vecR 5 13 1729 133 9 LV HV RM (rowL RM M a) M)
            (Nat.shiftLeft 1 (Nat.mul 13 a)) = true := by
          have h0 := Nat.beq_refl (vecR 5 13 1729 133 9 LV HV RM (rowL RM M a) M)
          rw [heq] at h0 ⊢
          exact h0
        rw [this] at hn
        exact absurd hn (by simp [CFSG.KC.Ord.notB])
      apply hne
      obtain ⟨hp, -, hw, -, hT, -⟩ := consts_facts hc
      obtain ⟨hr1, hr2⟩ := row_spec (a := a) hc hM ha'
      have hr1' : VCanon 5 133 13 (rowL RM M a) := hr1
      have hr2' : toVec 5 133 13 (rowL RM M a) = fun j => OM M ⟨a, ha'⟩ j := hr2
      obtain ⟨hv1, hv2⟩ := vecR_sound hc hr1' hM
      obtain ⟨hu1, hu2⟩ := unit_spec (p := 5) (w := 13) (d := 133) (by norm_num) (by norm_num) ha'
      refine vec_inj hw hv1 hu1 ?_
      rw [hv2, hu2, hr2']
      funext j
      have := congrFun (congrFun hsq ⟨a, ha'⟩) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp only [Matrix.vecMul, dotProduct]
      change ∑ x, OM M ⟨a, ha'⟩ x * OM M x j = _
      rw [this]
      by_cases hj : j.val = a
      · simp [hj, Fin.ext_iff]
      · have : ¬ (⟨a, ha'⟩ : Fin 133) = j := fun h => hj (by rw [← h])
        simp [hj, this]
  · rw [hk0] at h
    dsimp only at h
    left
    rw [Nat.eq_of_beq_eq_true h]
    exact (one_sound hc).2

private theorem cen_succ {mul vm : Nat → Nat → Nat} {n k M idx : Nat}
    (h : cen mul vm PC RP TG np ONE RM (n + 1) k M idx = true) :
    cen mul vm PC RP TG np ONE RM n (k + 1) M idx = true ∧
      cen mul vm PC RP TG np ONE RM n (k + 1) (mul M (PC k)) (idx + 1 <<< k) = true := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (letB (mul M (PC k)) (fun M' => cen mul vm PC RP TG np ONE RM n (k + 1) M'
        (Nat.add idx (Nat.shiftLeft 1 k))))
      (cen mul vm PC RP TG np ONE RM n (k + 1) M idx) = true := h
  obtain ⟨h1, h2⟩ := bAndT h'
  rw [letB_eq] at h2
  exact ⟨h1, h2⟩

private theorem cen_ok (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hRP : ∀ a < np, Canon 5 133 13 (RP a)) :
    ∀ n k M idx, (∀ i < k + n, Canon 5 133 13 (PC i)) → Canon 5 133 13 M →
      cen (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC RP TG np ONE RM
        n k M idx = true →
      ∀ e : Nat → Nat, (∀ i, e i < 2) → OM M = nfE PC k e →
        nfE PC (k + n) e = 1 ∨ nfE PC (k + n) e * nfE PC (k + n) e ≠ 1 ∨
          ∃ a < np, ∃ q, q % 2 = 1 ∧ (nfE PC (k + n) e * OM (RP a)) ^ q = 1
  | 0, k, M, idx, _, hM, h, e, _, hOM => by
    rw [Nat.add_zero, ← hOM]
    exact elem_ok hc hRP hM h
  | n + 1, k, M, idx, hPC, hM, h, e, he, hOM => by
    obtain ⟨h1, h2⟩ := cen_succ h
    have hPC' : ∀ i < k + 1 + n, Canon 5 133 13 (PC i) := fun i hi => hPC i (by omega)
    rw [show k + (n + 1) = k + 1 + n by omega]
    rcases Nat.lt_or_ge (e k) 1 with hk | hk
    · replace hk : e k = 0 := by omega
      refine cen_ok hc hRP n (k + 1) M idx hPC' hM h1 e he ?_
      rw [nfE_succ, hk, pow_zero, mul_one, hOM]
    · replace hk : e k = 1 := by have := he k; omega
      obtain ⟨hM', hOM'⟩ := mulR_sound hc hM (hPC k (by omega))
      refine cen_ok hc hRP n (k + 1) _ _ hPC' hM' h2 e he ?_
      rw [nfE_succ, hk, pow_one, ← hOM]
      exact hOM'

theorem cenAt_sound' {L H CM RM ONE LV HV : Nat} {PC RP TG : Nat → Nat} {np m k n : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < k + n, Canon 5 133 13 (PC i)) (hRP : ∀ a < np, Canon 5 133 13 (RP a))
    (hm : m < 2 ^ k)
    (h : cenAt (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC RP TG np ONE RM
      m k n = true) :
    ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < k, e i = m / 2 ^ i % 2) →
      nfE PC (k + n) e = 1 ∨ nfE PC (k + n) e * nfE PC (k + n) e ≠ 1 ∨
      ∃ a < np, ∃ q, q % 2 = 1 ∧ (nfE PC (k + n) e * OM (RP a)) ^ q = 1 := by
  intro e he hek
  have h' : cen (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC RP TG np ONE RM
      n k (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) m = true := by
    unfold cenAt at h
    rw [letB_eq] at h
    exact h
  obtain ⟨hM0, hOM0⟩ := nfPre_ok hc m k (fun i hi => hPC i (by omega))
  refine cen_ok hc hRP n k _ m hPC hM0 h' e he ?_
  rw [hOM0]
  exact nfE_congr PC k fun i hi => (hek i hi).symm

end CFSG.KS.HNLocal.CenPf

end
