module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.J4Hub.BlockSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LocalQTSecLemmas
public import CFSG.Certificates.Kernel.Fam.Act

public section

namespace CFSG.KS.Cent

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.LQT.SecS CFSG.KS.J4Hub CFSG.KS.PackFld Matrix

variable {p w S d T L H CM RM ONE LV HV : Nat}

theorem canon_zero (hp : 0 < p) : Canon p d w 0 :=
  ⟨Nat.two_pow_pos _, fun t _ => by simp [lane, hp]⟩

theorem ordMat_zero : ordMat p d w S 0 = 0 := by
  funext i j
  simp [ordMat]

theorem lane_lt_p_bound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) :
    p ≤ 2 ^ w := by
  obtain ⟨-, -, hw, -, hT, -⟩ := consts_facts hc
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  omega

private theorem lane_bound {p d x y c B : Nat} (hd : 2 ≤ d) (hB : d * ((p - 1) * (p - 1)) < B)
    (hx : x < p) (hy : y < p) (hc : c < p) : x + y * c < B := by
  have h1 : y * c ≤ (p - 1) * (p - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : p - 1 ≤ (p - 1) * (p - 1) := by
    rcases Nat.eq_zero_or_pos (p - 1) with h | h
    · omega
    · exact Nat.le_mul_of_pos_left _ h
  have h3 : 2 * ((p - 1) * (p - 1)) ≤ d * ((p - 1) * (p - 1)) := Nat.mul_le_mul_right _ hd
  omega

theorem addMul_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hd : 2 ≤ d)
    {X Y c : Nat} (hX : Canon p d w X) (hY : Canon p d w Y) (hcp : c < p) :
    Canon p d w (redP w L H p T (X + Y * c)) ∧
      ordMat p d w S (redP w L H p T (X + Y * c)) =
        ordMat p d w S X + (c : ZMod p) • ordMat p d w S Y := by
  obtain ⟨hp, hS, hw, hdp, hT, hT2, hL, hH, -, -, -⟩ := consts_facts hc
  subst hS hL hH
  obtain ⟨a, rfl, ha⟩ : ∃ a, X = pk w (d * d) a ∧ ∀ t < d * d, a t < p :=
    ⟨lane w X, pk_lane hw hX.1, hX.2⟩
  obtain ⟨b, rfl, hb⟩ : ∃ b, Y = pk w (d * d) b ∧ ∀ t < d * d, b t < p :=
    ⟨lane w Y, pk_lane hw hY.1, hY.2⟩
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  have hbd : ∀ t < d * d, a t + b t * c < 2 ^ (w - 1) := fun t ht =>
    lane_bound hd hdp (ha t ht) (hb t ht) hcp
  have e : redP w (pk w (d * d) fun _ => 1) (pk w (d * d) fun _ => 2 ^ (w - 1)) p T
      (pk w (d * d) a + pk w (d * d) b * c) = pk w (d * d) (fun t => (a t + b t * c) % p) := by
    rw [pk_mul, pk_add]
    exact redP_pk hw hT hbd (fun t ht => by have := hbd t ht; omega)
  have hCp : ∀ t < d * d, (a t + b t * c) % p < p := fun t _ => Nat.mod_lt _ (by omega)
  rw [e]
  refine ⟨canon_pk hCp hpw, ?_⟩
  funext i j
  rw [ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hCp t ht) hpw)]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (ha t ht) hpw) i j,
    ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hb t ht) hpw) i j, ZMod.natCast_mod]
  push_cast
  ring

theorem lincomb_cons (RB : Nat → Nat) (p w T L H nreg x : Nat) (Ls : List Nat) :
    CFSG.KC.Fam.lincomb RB p w T L H nreg (x :: Ls) =
      Bool.rec (motive := fun _ => Nat) 0
        (redP w L H p T (Nat.add (CFSG.KC.Fam.lincomb RB p w T L H nreg Ls)
          (Nat.mul (RB (Nat.shiftRight x 8)) (Nat.land x 255))))
        (andB (Nat.blt (Nat.land x 255) p) (regBelow (Nat.shiftRight x 8) nreg)) :=
  rfl

theorem lincomb_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hd : 2 ≤ d)
    {RB : Nat → Nat} {nreg : Nat} : ∀ Ls : List Nat,
    (∀ x ∈ Ls, Nat.land x 255 < p ∧ regBelow (Nat.shiftRight x 8) nreg = true ∧
      Canon p d w (RB (Nat.shiftRight x 8))) →
    Canon p d w (CFSG.KC.Fam.lincomb RB p w T L H nreg Ls) ∧
      ordMat p d w S (CFSG.KC.Fam.lincomb RB p w T L H nreg Ls) =
        (Ls.map fun x => ((Nat.land x 255 : Nat) : ZMod p) •
          ordMat p d w S (RB (Nat.shiftRight x 8))).sum
  | [], _ => ⟨canon_zero (by have := (consts_facts hc).1; omega), ordMat_zero⟩
  | x :: Ls, h => by
    obtain ⟨ih1, ih2⟩ := lincomb_sound hc hd Ls fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨hx1, hx2, hx3⟩ := h x List.mem_cons_self
    have e : CFSG.KC.Fam.lincomb RB p w T L H nreg (x :: Ls) =
        redP w L H p T (CFSG.KC.Fam.lincomb RB p w T L H nreg Ls +
          RB (Nat.shiftRight x 8) * Nat.land x 255) := by
      rw [lincomb_cons, Nat.blt_eq.mpr hx1, hx2]
      rfl
    obtain ⟨h1, h2⟩ := addMul_sound hc hd ih1 hx3 hx1
    rw [e]
    refine ⟨h1, ?_⟩
    rw [h2, ih2, List.map_cons, List.sum_cons, add_comm]

private theorem colOf_eq {w S : Nat} (hwS : w ≤ S) (v : Nat) : ∀ m,
    CFSG.KC.Fam.colOf w S m v = ∑ i ∈ Finset.range m, lane w v i * 2 ^ (S * i) ∧
      CFSG.KC.Fam.colOf w S m v < 2 ^ (S * m)
  | 0 => ⟨rfl, by simp [CFSG.KC.Fam.colOf]⟩
  | m + 1 => by
    obtain ⟨ih1, ih2⟩ := colOf_eq hwS v m
    have hl : lane w v m < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have e : CFSG.KC.Fam.colOf w S (m + 1) v =
        Nat.lor (CFSG.KC.Fam.colOf w S m v) (Nat.shiftLeft (bitsN v (Nat.mul w m) w) (Nat.mul S m)) :=
      rfl
    have hb : bitsN v (Nat.mul w m) w = lane w v m := bitsN_lane v w m
    rw [e, hb]
    have e2 : Nat.lor (CFSG.KC.Fam.colOf w S m v) (Nat.shiftLeft (lane w v m) (Nat.mul S m)) =
        (lane w v m) <<< (S * m) + CFSG.KC.Fam.colOf w S m v := by
      rw [Nat.shiftLeft_add_eq_or_of_lt ih2]
      exact Nat.lor_comm _ _
    rw [e2, Nat.shiftLeft_eq, Finset.sum_range_succ, ih1]
    refine ⟨by ring, ?_⟩
    have h3 : (lane w v m + 1) * 2 ^ (S * m) ≤ 2 ^ (S * (m + 1)) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (S * m))]
      exact Nat.mul_le_mul_right _ (Nat.le_trans hl (Nat.pow_le_pow_right (by omega) hwS))
    rw [ih1] at ih2
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

private theorem colOf_pk {w d : Nat} (hd : 0 < d) (v : Nat) :
    CFSG.KC.Fam.colOf w (d * w) d v =
      pk w (d * d) (fun t => if t % d = 0 then lane w v (t / d) else 0) := by
  rw [(colOf_eq (Nat.le_mul_of_pos_left w hd) v d).1, pk_rows]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0]
  · obtain ⟨e1, e2⟩ := dm_eq (d := d) (i := i) (j := 0) hd
    rw [e1, e2, if_pos rfl, Nat.add_zero]
    congr 2
    ring
  · intro j hj hj0
    obtain ⟨-, e2⟩ := dm_eq (d := d) (i := i) (j := j) (Finset.mem_range.1 hj)
    rw [e2, if_neg hj0, Nat.zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

theorem colOf_apply (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (v : Nat) (i j : Fin d) :
    ordMat p d w S (CFSG.KC.Fam.colOf w S d v) i j =
      if j.val = 0 then ((lane w v i.val : Nat) : ZMod p) else 0 := by
  obtain ⟨-, hS, -⟩ := consts_facts hc
  subst hS
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [colOf_pk hd]
  have hg : ∀ t < d * d, (if t % d = 0 then lane w v (t / d) else 0) < 2 ^ w := by
    intro t _
    split
    · exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact Nat.two_pow_pos w
  rw [ordMat_pk hg]
  obtain ⟨e1, e2⟩ := dm_eq (d := d) (i := i.val) j.isLt
  rw [e1, e2]
  split <;> simp

private theorem col0_lanes (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {X : Nat}
    (hX : Nat.land X CM = X) : ∀ t < d * d, t % d ≠ 0 → lane w X t = 0 := by
  obtain ⟨-, -, hw, -, -, -, -, -, hCM, -⟩ := consts_facts hc
  subst hCM
  intro t ht htd
  have hg : ∀ s < d * d, (if s % d = 0 then 2 ^ w - 1 else 0) < 2 ^ w := by
    intro s _
    split
    · have := Nat.two_pow_pos w
      omega
    · exact Nat.two_pow_pos w
  have hF := fld_and (fld_lane w X) (fld_pk hg)
  change Fld w (Nat.land X _) _ at hF
  rw [hX] at hF
  rw [lane_of_fld hF (by simp [ht, htd, Nat.two_pow_pos w])]
  simp [ht, htd]

private theorem outer_pk {w d : Nat} (g u : Nat → Nat) (hg : ∀ t < d * d, t % d ≠ 0 → g t = 0) :
    pk w (d * d) g * pk w d u = pk w (d * d) (fun t => g (d * (t / d)) * u (t % d)) := by
  rw [pk_rows, pk_rows, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) hi'
  rw [Finset.sum_eq_single 0]
  · unfold pk
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨e1, e2⟩ := dm_eq (d := d) (i := i) (Finset.mem_range.1 hj)
    rw [e1, e2, Nat.add_zero, Nat.mul_add, Nat.pow_add]
    ring
  · intro j hj hj0
    obtain ⟨-, e2⟩ := dm_eq (d := d) (i := i) (j := j) (Finset.mem_range.1 hj)
    rw [hg _ (idx_lt hi' (Finset.mem_range.1 hj)) (by rw [e2]; exact hj0), Nat.zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

theorem rker_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hd : 2 ≤ d)
    {nb C Y C0v ur : Nat} (hnb : nb = d * S) (hC : Canon p d w C)
    (h : CFSG.KC.Fam.rkerOK p w T L H CM ONE (mulR p w S d T L H CM RM) (validM p nb L H)
      (validM p S LV HV) C Y C0v ur = true) :
    Canon p d w C0v ∧ (∀ i j : Fin d, j.val ≠ 0 → ordMat p d w S C0v i j = 0) ∧
      ordMat p d w S Y * ordMat p d w S C +
        Matrix.vecMulVec (fun i => ordMat p d w S C0v i ⟨0, by omega⟩) (toVec p d w ur) = 1 := by
  subst hnb
  obtain ⟨hY, h⟩ := andT' h
  obtain ⟨hC0, h⟩ := andT' h
  obtain ⟨hcol, h⟩ := andT' h
  obtain ⟨hur, h⟩ := andT' h
  have cY := validM_canon hc hY
  have cC0 := validM_canon hc hC0
  have vur := validV_canon hc hur
  have hcol' : Nat.land C0v CM = C0v := Nat.eq_of_beq_eq_true hcol
  have hz := col0_lanes hc hcol'
  obtain ⟨cYC, eYC⟩ := mulR_sound hc cY hC
  obtain ⟨hp, hS, hw, hdp, hT, hT2, hL, hH, -, -, hONE⟩ := consts_facts hc
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  have hdS : d * S = d * (d * w) := by rw [hS]
  refine ⟨cC0, ?_, ?_⟩
  · intro i j hj
    subst hS
    rw [pk_lane hw cC0.1]
    rw [ordMat_pk (g := lane w C0v) (fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w))]
    rw [hz _ (idx_lt i.isLt j.isLt) (by rw [(dm_eq (i := i.val) j.isLt).2]; exact hj)]
    simp
  · subst hS hL hH hONE
    generalize hM : mulR p w (d * w) d T (pk w (d * d) fun _ => 1)
      (pk w (d * d) fun _ => 2 ^ (w - 1)) CM RM Y C = M at h cYC eYC
    obtain ⟨a, rfl, ha⟩ : ∃ a, M = pk w (d * d) a ∧ ∀ t < d * d, a t < p :=
      ⟨lane w M, pk_lane hw cYC.1, cYC.2⟩
    obtain ⟨g, rfl, hg⟩ : ∃ g, C0v = pk w (d * d) g ∧ ∀ t < d * d, g t < p :=
      ⟨lane w C0v, pk_lane hw cC0.1, cC0.2⟩
    obtain ⟨u, rfl, hu⟩ : ∃ u, ur = pk w d u ∧ ∀ t < d, u t < p :=
      ⟨lane w ur, pk_lane hw vur.1, vur.2⟩
    have hg' : ∀ t < d * d, (fun s => lane w (pk w (d * d) g) s) t = g t := fun t ht =>
      lane_pk (fun s hs => Nat.lt_of_lt_of_le (hg s hs) hpw) ht
    have hgz : ∀ t < d * d, t % d ≠ 0 → g t = 0 := fun t ht htd => by
      rw [← hg' t ht]
      exact hz t ht htd
    have hbd : ∀ t < d * d, a t + g (d * (t / d)) * u (t % d) < 2 ^ (w - 1) := by
      intro t ht
      have hd0 : 0 < d := by omega
      refine lane_bound hd hdp (ha t ht) (hg _ ?_) (hu _ (Nat.mod_lt _ hd0))
      have h1 : t / d < d := (Nat.div_lt_iff_lt_mul hd0).2 ht
      exact idx_lt h1 hd0
    have e : redP w (pk w (d * d) fun _ => 1) (pk w (d * d) fun _ => 2 ^ (w - 1)) p T
        (Nat.add (pk w (d * d) a) (Nat.mul (pk w (d * d) g) (pk w d u))) =
        pk w (d * d) (fun t => (a t + g (d * (t / d)) * u (t % d)) % p) := by
      change redP _ _ _ p T (pk w (d * d) a + pk w (d * d) g * pk w d u) = _
      rw [outer_pk g u hgz, pk_add]
      exact redP_pk hw hT hbd (fun t ht => by have := hbd t ht; omega)
    have hone := Nat.eq_of_beq_eq_true h
    rw [e] at hone
    have hO := (CFSG.KS.Ord.one_sound hc).2
    funext i j
    have hCp : ∀ t < d * d, (a t + g (d * (t / d)) * u (t % d)) % p < 2 ^ w := fun t _ =>
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hpw
    have key := congrFun (congrFun (congrArg (ordMat p d w (d * w)) hone) i) j
    rw [ordMat_pk hCp] at key
    rw [← hO]
    rw [← key, Matrix.add_apply, Matrix.vecMulVec_apply, ← eYC]
    obtain ⟨e1, e3⟩ := dm_eq (i := i.val) j.isLt
    rw [e1, e3, ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (ha t ht) hpw),
      ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) hpw)]
    simp only [toVec]
    rw [lane_pk (fun t ht => Nat.lt_of_lt_of_le (hu t ht) hpw) j.isLt, ZMod.natCast_mod]
    obtain ⟨e4, -⟩ := dm_eq (d := d) (i := i.val) (j := 0) (by omega)
    rw [Nat.add_zero] at e4 ⊢
    push_cast
    ring_nf

private theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private theorem recB_spec {g : Nat → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n = true →
      ∀ k < n, g k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact recB_spec n h2 k hk
    · exact h1

theorem allBelow_spec' {m hi : Nat} {f : Nat → Bool} (h : CFSG.KC.Loop.allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  intro i him hih
  have hq : i / 64 < hi := by omega
  have h1 := recB_spec hi h (i / 64) hq
  have h2 := recB_spec (g := fun l => Bool.rec (motive := fun _ => Bool) true
    (f (Nat.add (Nat.shiftLeft (i / 64) 6) l)) (Nat.blt (Nat.add (Nat.shiftLeft (i / 64) 6) l) m))
    64 h1 (i % 64) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  simp only [e, Nat.blt_eq.mpr him] at h2
  exact h2

theorem lt_hi {k m : Nat} (hk : k < m) : k < 64 * Nat.add (Nat.shiftRight m 6) 1 := by
  change k < 64 * (m >>> 6 + 1)
  rw [Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem bitsN_div (x o m : Nat) : bitsN x o m = x / 2 ^ o % 2 ^ m := by
  unfold bitsN
  change (x >>> o) &&& ((1 <<< m) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem tpose_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {nb A AT : Nat}
    (hnb : nb = d * S) (h : CFSG.KC.Fam.tposeOK (validM p nb L H) w S d A AT = true) :
    Canon p d w A ∧ Canon p d w AT ∧ ordMat p d w S AT = (ordMat p d w S A)ᵀ := by
  subst hnb
  obtain ⟨hA, h⟩ := andT' h
  obtain ⟨hAT, h⟩ := andT' h
  refine ⟨validM_canon hc hA, validM_canon hc hAT, ?_⟩
  have hall := allBelow_spec' h
  funext i j
  have hk : d * j.val + i.val < d * d := idx_lt j.isLt i.isLt
  have e := Nat.eq_of_beq_eq_true (hall (d * j.val + i.val) hk (lt_hi hk))
  obtain ⟨e1, e2⟩ := dm_eq (d := d) (i := j.val) i.isLt
  have e1' : Nat.div (d * j.val + i.val) d = j.val := e1
  have e2' : Nat.mod (d * j.val + i.val) d = i.val := e2
  beta_reduce at e
  rw [e1', e2', bitsN_div, bitsN_div] at e
  rw [Matrix.transpose_apply]
  unfold ordMat
  exact congrArg (fun n : Nat => (n : ZMod p)) e.symm

private theorem tree_step {V : Nat → Nat} {vm : Nat → Nat → Nat} {G0 G1 PT i : Nat}
    (h : (fun i => (fun pi li => andB (Nat.blt pi i) (andB (Nat.ble li (nat_lit 1))
        (Nat.beq (V i) (vm (V pi) (Bool.rec (motive := fun _ => Nat) G1 G0
          (Nat.beq li (nat_lit 0)))))))
      (bitsN PT (Nat.mul (nat_lit 24) i) (nat_lit 16))
      (bitsN PT (Nat.add (Nat.mul (nat_lit 24) i) (nat_lit 16)) (nat_lit 8))) i = true) :
    ∃ pi < i, ∃ b : Bool, V i = vm (V pi) (Bool.rec (motive := fun _ => Nat) G1 G0 b) := by
  simp only [] at h
  generalize bitsN PT (Nat.mul (nat_lit 24) i) (nat_lit 16) = pi at h
  generalize bitsN PT (Nat.add (Nat.mul (nat_lit 24) i) (nat_lit 16)) (nat_lit 8) = li at h
  obtain ⟨hpi, h⟩ := andT' h
  obtain ⟨-, h⟩ := andT' h
  exact ⟨pi, Nat.blt_eq.mp hpi, _, Nat.eq_of_beq_eq_true h⟩

theorem treeVec_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {V : Nat → Nat}
    {G0 G1 v0 PT : Nat} (hv0 : VCanon p d w v0) (hG0 : Canon p d w G0) (hG1 : Canon p d w G1)
    (h : CFSG.KC.Fam.treeVecOK V (vecR p w S d T LV HV RM) G0 G1 v0 PT d = true)
    (Q : (Fin d → ZMod p) → Prop) (hQ0 : Q (toVec p d w v0))
    (hQ : ∀ x, Q x → Q (x ᵥ* ordMat p d w S G0) ∧ Q (x ᵥ* ordMat p d w S G1)) :
    ∀ i < d, VCanon p d w (V i) ∧ Q (toVec p d w (V i)) := by
  obtain ⟨h0, hrec⟩ := andT' h
  have hV0 : V 0 = v0 := Nat.eq_of_beq_eq_true h0
  have hstep := rec_and' (d - 1) hrec
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | s
    · rw [hV0]
      exact ⟨hv0, hQ0⟩
    · obtain ⟨pi, hpi', b, e⟩ := tree_step (hstep s (by omega))
      obtain ⟨cpi, qpi⟩ := ih pi hpi' (by omega)
      rw [e]
      cases b
      · obtain ⟨c1, e1⟩ := vecR_sound hc cpi hG1
        have e1' : toVec p d w (vecR p w S d T LV HV RM (V pi)
            (Bool.rec (motive := fun _ => Nat) G1 G0 false)) =
            toVec p d w (V pi) ᵥ* ordMat p d w S G1 := e1
        exact ⟨c1, by rw [e1']; exact (hQ _ qpi).2⟩
      · obtain ⟨c1, e1⟩ := vecR_sound hc cpi hG0
        have e1' : toVec p d w (vecR p w S d T LV HV RM (V pi)
            (Bool.rec (motive := fun _ => Nat) G1 G0 true)) =
            toVec p d w (V pi) ᵥ* ordMat p d w S G0 := e1
        exact ⟨c1, by rw [e1']; exact (hQ _ qpi).1⟩

private theorem rowsMat_eq {p d w S : Nat} {V : Nat → Nat} {vld : Nat → Bool} (hwS : w * d = S)
    (hV : ∀ k < d, VCanon p d w (V k)) (hvld : ∀ k < d, vld (V k) = true) :
    ∀ m ≤ d, CFSG.KC.Fam.rowsMat V vld S m = ∑ k ∈ Finset.range m, V k * 2 ^ (S * k) ∧
      CFSG.KC.Fam.rowsMat V vld S m < 2 ^ (S * m)
  | 0, _ => ⟨rfl, by simp [CFSG.KC.Fam.rowsMat]⟩
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := rowsMat_eq hwS hV hvld m (by omega)
    have e : CFSG.KC.Fam.rowsMat V vld S (m + 1) =
        Bool.rec (motive := fun _ => Nat) 0
          (Nat.lor (CFSG.KC.Fam.rowsMat V vld S m) (Nat.shiftLeft (V m) (Nat.mul S m))) (vld (V m)) :=
      rfl
    rw [e, hvld m (by omega)]
    change Nat.lor (CFSG.KC.Fam.rowsMat V vld S m) (Nat.shiftLeft (V m) (S * m)) = _ ∧
      Nat.lor (CFSG.KC.Fam.rowsMat V vld S m) (Nat.shiftLeft (V m) (S * m)) < _
    have e2 : Nat.lor (CFSG.KC.Fam.rowsMat V vld S m) (Nat.shiftLeft (V m) (S * m)) =
        (V m) <<< (S * m) + CFSG.KC.Fam.rowsMat V vld S m := by
      rw [Nat.shiftLeft_add_eq_or_of_lt ih2]
      exact Nat.lor_comm _ _
    have hVm : V m < 2 ^ S := by rw [← hwS]; exact (hV m (by omega)).1
    rw [e2, Nat.shiftLeft_eq, Finset.sum_range_succ, ih1]
    refine ⟨by ring, ?_⟩
    have h3 : (V m + 1) * 2 ^ (S * m) ≤ 2 ^ (S * (m + 1)) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (S * m))]
      exact Nat.mul_le_mul_right _ hVm
    rw [ih1] at ih2
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

theorem rowsBasis_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {nb : Nat}
    (hnb : nb = d * S) {V : Nat → Nat} {Ri : Nat}
    (h : CFSG.KC.Fam.rowsBasis V (mulR p w S d T L H CM RM) (validM p nb L H) (validM p S LV HV)
      S d ONE Ri = true) :
    (∀ k < d, VCanon p d w (V k)) ∧
      Matrix.of (fun i j : Fin d => toVec p d w (V i.val) j) * ordMat p d w S Ri = 1 := by
  subst hnb
  obtain ⟨hall, h⟩ := andT' h
  obtain ⟨hRi, h⟩ := andT' h
  have hv : ∀ k < d, validM p S LV HV (V k) = true := fun k hk =>
    allBelow_spec' hall k hk (lt_hi hk)
  have hV : ∀ k < d, VCanon p d w (V k) := fun k hk => validV_canon hc (hv k hk)
  refine ⟨hV, ?_⟩
  obtain ⟨hp, hS, hw, -, hT, -⟩ := consts_facts hc
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  subst hS
  have hr := (rowsMat_eq (Nat.mul_comm w d) hV hv d le_rfl).1
  have hl : ∀ t < d * d, lane w (V (t / d)) (t % d) < p := by
    intro t ht
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h
        simp at ht
      · exact h
    exact (hV _ ((Nat.div_lt_iff_lt_mul hd0).2 ht)).2 _ (Nat.mod_lt _ hd0)
  have ep : CFSG.KC.Fam.rowsMat V (validM p (d * w) LV HV) (d * w) d =
      pk w (d * d) (fun t => lane w (V (t / d)) (t % d)) := by
    rw [hr, pk_rows]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [pk_lane hw (hV i (Finset.mem_range.1 hi)).1]
    unfold pk
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨e1, e3⟩ := dm_eq (d := d) (i := i) (Finset.mem_range.1 hj)
    rw [e1, e3, ← lane_pk (w := w) (n := d) (g := lane w (V i))
      (fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)) (Finset.mem_range.1 hj),
      ← pk_lane hw (hV i (Finset.mem_range.1 hi)).1, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    ring
  have cR : Canon p d w (pk w (d * d) (fun t => lane w (V (t / d)) (t % d))) := canon_pk hl hpw
  have e := Nat.eq_of_beq_eq_true h
  rw [ep] at e
  obtain ⟨-, eM⟩ := mulR_sound hc cR (validM_canon hc hRi)
  rw [e, (CFSG.KS.Ord.one_sound hc).2] at eM
  rw [eM]
  congr 1
  funext i j
  rw [ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hl t ht) hpw)]
  obtain ⟨e1, e3⟩ := dm_eq (d := d) (i := i.val) j.isLt
  rw [e1, e3]
  rfl

end CFSG.KS.Cent

end
