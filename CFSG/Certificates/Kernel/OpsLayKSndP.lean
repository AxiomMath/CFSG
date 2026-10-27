module

public import CFSG.Certificates.Kernel.OpsLayKSnd
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KC.OpsLayK.SndP

open CFSG.KC.LQT CFSG.KS.Ord CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.He.Native (toMat toVec toMat_apply toVec_apply getElem!_ofFn rowsOf mulM idM
  toMat_mulM toMat_idM toMat_rowsOf)
open scoped Matrix

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem p_two {c : Lay} (hc : c.ok = true) : 2 ≤ c.p := (CFSG.KS.SporSch.LyM.cfacts hc).1

@[expose] def ArrCanon (p d : ℕ) (X : Array (Array ℕ)) : Prop :=
  X.size = d ∧ ∀ i < d, (X[i]!).size = d ∧ ∀ j < d, (X[i]!)[j]! < p

theorem arr_rowsOf {p d : ℕ} (hp : 0 < p) (s : String) : ArrCanon p d (rowsOf p d s) := by
  refine ⟨by simp [rowsOf], fun i hi => ?_⟩
  unfold rowsOf
  rw [getElem!_ofFn _ hi]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_ofFn _ hj]
  exact Nat.mod_lt _ hp

theorem arr_idM {p d : ℕ} (hp : 1 < p) : ArrCanon p d (idM d) := by
  refine ⟨by simp [idM], fun i hi => ?_⟩
  unfold idM
  rw [getElem!_ofFn _ hi]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_ofFn _ hj]
  split <;> omega

theorem arr_mulM {p d : ℕ} (hp : 0 < p) (X Y : Array (Array ℕ)) :
    ArrCanon p d (mulM p d X Y) := by
  refine ⟨by simp [mulM], fun i hi => ?_⟩
  unfold mulM
  rw [getElem!_ofFn _ hi]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_ofFn _ hj]
  exact Nat.mod_lt _ hp

theorem arr_pow {p d : ℕ} (hp : 1 < p) {X : Array (Array ℕ)} (hX : ArrCanon p d X) (e : ℕ) :
    ArrCanon p d ((opsP p d).pow X e) := by
  have hp0 : 0 < p := by omega
  induction e using Nat.strong_induction_on generalizing X with
  | _ e ih =>
    unfold Ops.pow
    by_cases h0 : e = 0
    · rw [if_pos h0]
      exact arr_idM hp
    by_cases h1 : e = 1
    · rw [if_neg h0, if_pos h1]
      exact hX
    rw [if_neg h0, if_neg h1]
    have hpow := ih (e / 2) (by omega) (arr_mulM hp0 X X)
    by_cases ho : e % 2 = 1
    · rw [if_pos ho]
      exact arr_mulM hp0 _ _
    · rw [if_neg ho]
      exact hpow

theorem arr_eq_of_toMat_eq {p d : ℕ} {X Y : Array (Array ℕ)} (hX : ArrCanon p d X)
    (hY : ArrCanon p d Y) (h : toMat p d X = toMat p d Y) : X = Y := by
  apply Array.ext
  · rw [hX.1, hY.1]
  · intro i hi hi'
    have hid : i < d := by rwa [hX.1] at hi
    have hXi : i < X.size := hi
    have hYi : i < Y.size := by rwa [hY.1]
    have hXi' : (X[i]).size = d := by rw [← getElem!_pos X i hXi]; exact (hX.2 i hid).1
    have hYi' : (Y[i]).size = d := by rw [← getElem!_pos Y i hYi]; exact (hY.2 i hid).1
    apply Array.ext
    · rw [hXi', hYi']
    · intro j hj hj'
      have hjd : j < d := by rw [← hXi']; exact hj
      have hXj : j < (X[i]).size := hj
      have hYj : j < (Y[i]).size := by rwa [hYi']
      have e := congrFun (congrFun h ⟨i, hid⟩) ⟨j, hjd⟩
      rw [toMat_apply, toMat_apply] at e
      rw [getElem!_pos X i hXi, getElem!_pos Y i hYi,
        getElem!_pos (X[i]) j hXj, getElem!_pos (Y[i]) j hYj] at e
      have hbX : X[i][j] < p := by
        rw [← getElem!_pos (X[i]) j hXj, ← getElem!_pos X i hXi]
        exact (hX.2 i hid).2 j hjd
      have hbY : Y[i][j] < p := by
        rw [← getElem!_pos (Y[i]) j hYj, ← getElem!_pos Y i hYi]
        exact (hY.2 i hid).2 j hjd
      exact CFSG.KS.SporSch.LyM.eq_of_cast hbX hbY e

@[expose] def LRel (c : Lay) (X : Array (Array ℕ)) (x : ℕ) : Prop :=
  Canon c.p c.d c.w x ∧ ArrCanon c.p c.d X ∧ toMat c.p c.d X = ordMat c.p c.d c.w c.S x

@[expose] def LVRel (c : Lay) (u : Array ℕ) (v : ℕ) : Prop :=
  SecS.VCanon c.p c.d c.w v ∧ toVec c.p c.d u = SecS.toVec c.p c.d c.w v

theorem rel_mul {c : Lay} (hc : c.ok = true) {X Y : Array (Array ℕ)} {x y : ℕ}
    (hX : LRel c X x) (hY : LRel c Y y) : LRel c ((opsP c.p c.d).mul X Y) (c.mul x y) := by
  obtain ⟨cx, -, mX⟩ := hX
  obtain ⟨cy, -, mY⟩ := hY
  obtain ⟨cxy, mxy⟩ := SecS.mul_sound c hc cx cy
  refine ⟨cxy, arr_mulM (by have := p_two hc; omega) X Y, ?_⟩
  change toMat c.p c.d (mulM c.p c.d X Y) = _
  rw [toMat_mulM, mX, mY, mxy]

theorem rel_one {c : Lay} (hc : c.ok = true) : LRel c (opsP c.p c.d).one c.ONE := by
  obtain ⟨c1, m1⟩ := one_sound hc
  refine ⟨c1, arr_idM (by have := p_two hc; omega), ?_⟩
  change toMat c.p c.d (idM c.d) = _
  rw [toMat_idM, m1]

theorem rel_decode {c : Lay} (hc : c.ok = true) {M : ℕ} {l : List Char} {s : String}
    (hM : decOK c M l = true) (hs : s = String.ofList l) :
    LRel c ((opsP c.p c.d).decode s) M := by
  obtain ⟨cM, mM⟩ := SecS.decOK_sound c hc hM
  refine ⟨cM, arr_rowsOf (by have := p_two hc; omega) s, ?_⟩
  change toMat c.p c.d (rowsOf c.p c.d s) = _
  rw [toMat_rowsOf, mM, hs]

private theorem powN_succ (c : Lay) (f X e : ℕ) :
    powN c (f + 1) X e =
      Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) (powN c f (c.mul X X) (e / 2))
            (c.mul X (powN c f (c.mul X X) (e / 2))) (Nat.beq (e % 2) 1))
          X (Nat.beq e 1))
        c.ONE (Nat.beq e 0) := by
  change Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (CFSG.KC.Loop.strictN (c.mul X X) fun X2 =>
          CFSG.KC.Loop.strictN (powN c f X2 (e / 2)) fun Y =>
            Bool.rec (motive := fun _ => ℕ) Y (c.mul X Y) (Nat.beq (e % 2) 1))
        X (Nat.beq e 1))
      c.ONE (Nat.beq e 0) = _
  simp only [strictN_eq]

theorem powN_spec {c : Lay} (hc : c.ok = true) :
    ∀ (f : ℕ) {X : ℕ} (e : ℕ), Canon c.p c.d c.w X → e < 2 ^ f →
      Canon c.p c.d c.w (powN c f X e) ∧
        ordMat c.p c.d c.w c.S (powN c f X e) = ordMat c.p c.d c.w c.S X ^ e
  | 0, X, e, _, he => by
    have e0 : e = 0 := by simpa using he
    subst e0
    exact ⟨(one_sound hc).1, by rw [pow_zero]; exact (one_sound hc).2⟩
  | f + 1, X, e, hX, he => by
    rw [powN_succ]
    rcases Nat.lt_or_ge e 2 with h2 | h2
    · rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · exact ⟨(one_sound hc).1, by rw [pow_zero]; exact (one_sound hc).2⟩
      · exact ⟨hX, (pow_one _).symm⟩
    · rw [beq_false (show e ≠ 0 by omega), beq_false (show e ≠ 1 by omega)]
      obtain ⟨cX2, mX2⟩ := SecS.mul_sound c hc hX hX
      have he2 : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
      obtain ⟨cY, mY⟩ := powN_spec hc f (e / 2) cX2 he2
      have mY' : ordMat c.p c.d c.w c.S (powN c f (c.mul X X) (e / 2)) =
          ordMat c.p c.d c.w c.S X ^ (2 * (e / 2)) := by
        rw [mY, mX2, ← pow_two, ← pow_mul]
      rcases Nat.mod_two_eq_zero_or_one e with ho | ho
      · rw [beq_false (show e % 2 ≠ 1 by omega)]
        change Canon c.p c.d c.w (powN c f (c.mul X X) (e / 2)) ∧
          ordMat c.p c.d c.w c.S (powN c f (c.mul X X) (e / 2)) = ordMat c.p c.d c.w c.S X ^ e
        refine ⟨cY, ?_⟩
        rw [mY']
        congr 1
        omega
      · rw [beq_true ho]
        change Canon c.p c.d c.w (c.mul X (powN c f (c.mul X X) (e / 2))) ∧
          ordMat c.p c.d c.w c.S (c.mul X (powN c f (c.mul X X) (e / 2))) =
            ordMat c.p c.d c.w c.S X ^ e
        obtain ⟨cZ, mZ⟩ := SecS.mul_sound c hc hX cY
        refine ⟨cZ, ?_⟩
        rw [mZ, mY', ← pow_succ']
        congr 1
        omega

theorem rel_pow {c : Lay} (hc : c.ok = true) {X : Array (Array ℕ)} {x : ℕ}
    (hX : LRel c X x) {e : ℕ} (he : e < 65536) :
    LRel c ((opsP c.p c.d).pow X e) (powK c x e) := by
  obtain ⟨cx, aX, mX⟩ := hX
  obtain ⟨cy, my⟩ := powN_spec hc 17 e cx (lt_of_lt_of_le he (by norm_num))
  obtain ⟨-, mY⟩ := OpsSpec.pow_spec (specP c.p c.d) (X := X) trivial e
  refine ⟨cy, arr_pow (by have := p_two hc; omega) aX e, ?_⟩
  have h : toMat c.p c.d ((opsP c.p c.d).pow X e) = toMat c.p c.d X ^ e := mY
  rw [h, mX]
  exact my.symm

theorem eq_of_rel {c : Lay} {X Y : Array (Array ℕ)} {x y : ℕ} (hX : LRel c X x)
    (hY : LRel c Y y) (h : Nat.beq x y = true) : (opsP c.p c.d).eq X Y = true := by
  have hxy := Nat.eq_of_beq_eq_true h
  subst hxy
  have e := arr_eq_of_toMat_eq hX.2.1 hY.2.1 (hX.2.2.trans hY.2.2.symm)
  subst e
  change (X == X) = true
  exact beq_self_eq_true X

private theorem lane_pow_two (w t j : ℕ) (hw : 0 < w) :
    lane w (2 ^ (w * t)) j = if j = t then 1 else 0 := by
  have hw2 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  unfold lane
  rcases lt_trichotomy j t with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, t = j + k + 1 := ⟨t - j - 1, by omega⟩
    rw [if_neg (show j ≠ j + k + 1 by omega)]
    have e : 2 ^ (w * (j + k + 1)) = 2 ^ (w * j) * (2 ^ (w * k) * 2 ^ w) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    rw [e, Nat.mul_div_cancel_left _ (show 0 < 2 ^ (w * j) by positivity)]
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _)
  · rw [if_pos h, h, Nat.div_self (show 0 < 2 ^ (w * t) by positivity), Nat.mod_eq_of_lt hw2]
  · rw [if_neg (show j ≠ t by omega)]
    have hlt : 2 ^ (w * t) < 2 ^ (w * j) :=
      Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

theorem toVec_unit (c : Lay) (hc : c.ok = true) (t : ℕ) :
    SecS.toVec c.p c.d c.w (c.unit t) =
      fun j : Fin c.d => if (j : ℕ) = t then (1 : ZMod c.p) else 0 := by
  have hw := SecS.lay_w_pos c hc
  have hu : c.unit t = 2 ^ (c.w * t) := by
    unfold Lay.unit
    change 1 <<< (c.w * t) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  funext j
  simp only [SecS.toVec]
  rw [hu, lane_pow_two c.w t (j : ℕ) hw]
  split_ifs <;> simp

theorem toVec_unitP (p d t : ℕ) :
    toVec p d ((opsP p d).unit t) = fun j : Fin d => if (j : ℕ) = t then (1 : ZMod p) else 0 := by
  funext j
  rw [toVec_apply]
  unfold opsP
  rw [getElem!_ofFn _ j.isLt]
  split <;> simp

theorem vne_of_toVec_ne {p d : ℕ} {u w : Array ℕ} (h : toVec p d u ≠ toVec p d w) :
    (opsP p d).vne u w = true := by
  by_contra hc
  apply h
  funext j
  rw [toVec_apply, toVec_apply]
  by_contra hne
  have hb : (u[j.val]! % p != w[j.val]! % p) = true := by
    rw [bne_iff_ne]
    intro he
    exact hne (by rw [ZMod.natCast_eq_natCast_iff'] at *; omega)
  have hany : (List.range d).any (fun k => u[k]! % p != w[k]! % p) = true :=
    List.any_eq_true.2 ⟨j.val, List.mem_range.2 j.isLt, hb⟩
  exact hc (by simpa [opsP] using hany)

theorem vrel_unit {c : Lay} (hc : c.ok = true) {t : ℕ} (ht : t < c.d) :
    LVRel c ((opsP c.p c.d).unit t) (c.unit t) :=
  ⟨SecS.unit_canon c hc ht, by rw [toVec_unitP, toVec_unit c hc]⟩

theorem vrel_vmul {c : Lay} (hc : c.ok = true) {u : Array ℕ} {v : ℕ}
    {X : Array (Array ℕ)} {x : ℕ} (hu : LVRel c u v) (hX : LRel c X x) :
    LVRel c ((opsP c.p c.d).vmul u X) (c.vec v x) := by
  obtain ⟨cv, mu⟩ := hu
  obtain ⟨cx, -, mX⟩ := hX
  obtain ⟨cv', mv'⟩ := SecS.vec_sound c hc cv cx
  refine ⟨cv', ?_⟩
  change toVec c.p c.d (vecMulRow c.p c.d u X) = _
  rw [toVec_vecMulRow, mu, mX, mv']

theorem vrel_vpow {c : Lay} (hc : c.ok = true) {u : Array ℕ} {v : ℕ}
    {X : Array (Array ℕ)} {x : ℕ} (hu : LVRel c u v) (hX : LRel c X x) (n : ℕ) :
    LVRel c ((opsP c.p c.d).app X n u) (c.vpow x v n) := by
  obtain ⟨cv, mu⟩ := hu
  obtain ⟨cx, -, mX⟩ := hX
  obtain ⟨-, m1⟩ := OpsSpec.app_spec (specP c.p c.d) (X := X) trivial n (v := u) trivial
  obtain ⟨cv', mv'⟩ := SecS.vpow_spec c hc cx n cv
  refine ⟨cv', ?_⟩
  have m1' : toVec c.p c.d ((opsP c.p c.d).app X n u) =
      toVec c.p c.d u ᵥ* toMat c.p c.d X ^ n := m1
  rw [m1', mu, mX, mv']

theorem vne_of_vrel {c : Lay} (hc : c.ok = true) {u u' : Array ℕ} {v v' : ℕ}
    (hu : LVRel c u v) (hu' : LVRel c u' v') (h : v ≠ v') : (opsP c.p c.d).vne u u' = true := by
  apply vne_of_toVec_ne
  rw [hu.2, hu'.2]
  intro heq
  exact h (SecS.vec_inj (SecS.lay_w_pos c hc) hu.1 hu'.1 heq)

theorem vrel_appBase {c : Lay} (hc : c.ok = true) (b : ℕ)
    {Xs : List (Array (Array ℕ))} {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) :
    ∀ (n : ℕ) {u : Array ℕ} {v : ℕ}, LVRel c u v →
      LVRel c ((opsP c.p c.d).appBase b Xs n u) (appBaseK c b xs n v) := by
  induction h with
  | nil => intro n u v hu; exact hu
  | cons hX _ ih => intro n u v hu; exact ih (n / b) (vrel_vpow hc hu hX (n % b))

@[expose] def LCorr (c : Lay) (R : List ℕ) (Rn : Array (Array (Array ℕ))) : Prop :=
  R.length = Rn.size ∧ ∀ r < R.length, LRel c Rn[r]! (getR c R r)

theorem lcorr_set {c : Lay} {R : List ℕ} {Rn : Array (Array (Array ℕ))} (hR : LCorr c R Rn)
    {k : ℕ} (hk : k < R.length) {X : Array (Array ℕ)} {x : ℕ} (hX : LRel c X x) :
    LCorr c (R.set k x) (Rn.set! k X) := by
  obtain ⟨hlen, hR'⟩ := hR
  have hkR : k < Rn.size := by rw [← hlen]; exact hk
  refine ⟨by rw [List.length_set, Array.size_set!]; exact hlen, fun r hr => ?_⟩
  rw [List.length_set] at hr
  by_cases hrk : k = r
  · subst hrk
    have e1 : getR c (R.set k x) k = x := by
      simp [getR, List.getD_eq_getElem?_getD, hk]
    rw [e1, Array.getElem!_set!_self Rn k X hkR]
    exact hX
  · have e1 : getR c (R.set k x) r = getR c R r := by
      simp [getR, List.getD_eq_getElem?_getD, List.getElem?_set_ne hrk]
    rw [e1, Array.getElem!_set!_ne Rn k r X hrk]
    exact hR' r hr

theorem lcorr_step {c : Lay} (hc : c.ok = true) {R : List ℕ}
    {Rn : Array (Array (Array ℕ))} (hR : LCorr c R Rn) {o : Op} (hlt : Op.lt R.length o = true)
    (hexp : expOK o = true) :
    LCorr c (R.set (Op.tgt o) (stepV c R o)) ((opsP c.p c.d).step Rn o) := by
  cases o with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨⟨hi, hj⟩, hk⟩ := hlt
    exact lcorr_set hR hk (rel_mul hc (hR.2 i hi) (hR.2 j hj))
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨hi, hk⟩ := hlt
    have he : e < 65536 := by simpa [expOK] using hexp
    exact lcorr_set hR hk (rel_pow hc (hR.2 i hi) he)

theorem lcorr_run {c : Lay} (hc : c.ok = true) :
    ∀ (prog : List Op) (R : List ℕ) (Rn : Array (Array (Array ℕ))),
      prog.all (Op.lt R.length) = true → prog.all expOK = true → LCorr c R Rn →
        LCorr c (Snd.runL c prog R) (prog.foldl (opsP c.p c.d).step Rn)
  | [], _, _, _, _, hR => hR
  | o :: prog, R, Rn, hlt, hexp, hR => by
    rw [List.all_cons, Bool.and_eq_true] at hlt hexp
    have h1 := lcorr_step hc hR hlt.1 hexp.1
    have hlt' : prog.all (Op.lt (R.set (Op.tgt o) (stepV c R o)).length) = true := by
      rw [List.length_set]
      exact hlt.2
    exact lcorr_run hc prog _ _ hlt' hexp.2 h1

theorem lcorr_init {c : Lay} (hc : c.ok = true) {A B n : ℕ} {LA LB : List Char}
    {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) :
    LCorr c (initR c A B n)
      ((opsP c.p c.d).initRegs ((opsP c.p c.d).decode sA) ((opsP c.p c.d).decode sB) n) := by
  have hlen : (initR c A B n).length = n := by simp [initR]
  refine ⟨by rw [hlen]; simp [Ops.initRegs], fun r hr => ?_⟩
  rw [hlen] at hr
  have e1 : getR c (initR c A B n) r = if r = 0 then A else if r = 1 then B else c.ONE := by
    unfold getR initR
    rw [Snd.getD_eq_of_lt _ (by simpa using hr), List.getElem_map, List.getElem_range]
  have e2 : ((opsP c.p c.d).initRegs ((opsP c.p c.d).decode sA)
      ((opsP c.p c.d).decode sB) n)[r]! =
      if r = 0 then (opsP c.p c.d).decode sA else if r = 1 then (opsP c.p c.d).decode sB
        else (opsP c.p c.d).one := by
    unfold Ops.initRegs
    rw [Snd.ofFn_getElem! _ hr]
  rw [e1, e2]
  by_cases h0 : r = 0
  · rw [if_pos h0, if_pos h0]
    exact rel_decode hc hA hsA
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : r = 1
    · rw [if_pos h1, if_pos h1]
      exact rel_decode hc hB hsB
    · rw [if_neg h1, if_neg h1]
      exact rel_one hc

theorem lcorr_regs {c : Lay} (hc : c.ok = true) {A B : ℕ} {LA LB : List Char}
    {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : ℕ} {prog : List Op}
    (hprog : progOK n prog = true) :
    LCorr c (Snd.runL c prog (initR c A B n))
      ((opsP c.p c.d).run prog
        ((opsP c.p c.d).initRegs ((opsP c.p c.d).decode sA) ((opsP c.p c.d).decode sB) n)) := by
  simp only [progOK, Bool.and_eq_true] at hprog
  obtain ⟨⟨hexp, _⟩, hlt⟩ := hprog
  have hlen : (initR c A B n).length = n := by simp [initR]
  exact lcorr_run hc prog _ _ (by rw [hlen]; exact hlt) hexp (lcorr_init hc hA hB hsA hsB)

theorem forall₂_map {c : Lay} {R : List ℕ} {Rn : Array (Array (Array ℕ))} (h : LCorr c R Rn) :
    ∀ (outs : List ℕ), (∀ r ∈ outs, r < R.length) →
      List.Forall₂ (LRel c) (outs.map fun r => Rn[r]!) (outs.map (getR c R))
  | [], _ => List.Forall₂.nil
  | r :: outs, hr => List.Forall₂.cons (h.2 r (hr r List.mem_cons_self))
      (forall₂_map h outs fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))

theorem commsModOK_of {c : Lay} (hc : c.ok = true) {T : Array (Array ℕ)} {t : ℕ}
    (hT : LRel c T t) {Xs : List (Array (Array ℕ))} {xs : List ℕ}
    (h : List.Forall₂ (LRel c) Xs xs) :
    commsModK c t xs = true → (opsP c.p c.d).commsModOK T Xs = true := by
  induction h with
  | nil => intro _; rfl
  | cons hX h' ih =>
    intro hk
    simp only [commsModK, Ops.commsModOK, Bool.and_eq_true] at hk ⊢
    refine ⟨Snd.all_of_forall₂ (fun Y y hY hy => ?_) h' hk.1, ih hk.2⟩
    simp only [Ops.commModOK, Bool.or_eq_true] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (eq_of_rel (rel_mul hc hX hY) (rel_mul hc hY hX) hy)
    · exact Or.inr (eq_of_rel (rel_mul hc hX hY) (rel_mul hc hT (rel_mul hc hY hX)) hy)

theorem kerModOK_of {c : Lay} (hc : c.ok = true) {T : Array (Array ℕ)} {t : ℕ}
    (hT : LRel c T t) {Xs : List (Array (Array ℕ))} {xs : List ℕ}
    (h : List.Forall₂ (LRel c) Xs xs) {tests : List ℕ} (htests : ∀ k ∈ tests, k < c.d)
    (hk : ((List.range (2 ^ xs.length - 1)).all fun n =>
      tests.any (fun k => !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.unit k)) &&
        tests.any (fun k =>
          !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.vec (c.unit k) t))) = true) :
    (opsP c.p c.d).kerModOK T Xs tests = true := by
  unfold Ops.kerModOK
  rw [Snd.forall₂_length h]
  rw [List.all_eq_true] at hk ⊢
  intro n hn
  have hkn := hk n hn
  rw [Bool.and_eq_true] at hkn
  simp only [Ops.outsideN, Bool.and_eq_true]
  constructor
  · refine Snd.any_mono (fun k hk' hb => ?_) hkn.1
    have hu := vrel_unit hc (htests k hk')
    exact vne_of_vrel hc (vrel_appBase hc 2 h (n + 1) hu) hu (Snd.ne_of_not_beq hb)
  · refine Snd.any_mono (fun k hk' hb => ?_) hkn.2
    have hu := vrel_unit hc (htests k hk')
    exact vne_of_vrel hc (vrel_appBase hc 2 h (n + 1) hu) (vrel_vmul hc hu hT)
      (Snd.ne_of_not_beq hb)

theorem secOK_of {c : Lay} (hc : c.ok = true) {T : Array (Array ℕ)} {t : ℕ}
    (hT : LRel c T t) {Xs : List (Array (Array ℕ))} {xs : List ℕ}
    (h : List.Forall₂ (LRel c) Xs xs) {tests : List ℕ} (htests : ∀ k ∈ tests, k < c.d)
    (hk : (Nat.beq (c.mul t t) c.ONE &&
      xs.all (fun X => Nat.beq (c.mul X t) (c.mul t X) &&
        (Nat.beq (c.mul X X) c.ONE || Nat.beq (c.mul X X) t)) &&
      commsModK c t xs &&
      (List.range (2 ^ xs.length - 1)).all fun n =>
        tests.any (fun k => !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.unit k)) &&
          tests.any (fun k =>
            !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.vec (c.unit k) t))) = true) :
    (opsP c.p c.d).secOK T Xs tests = true := by
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨hTT, hall⟩, hcomm⟩, hker⟩ := hk
  unfold Ops.secOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨eq_of_rel (rel_mul hc hT hT) (rel_one hc) hTT, ?_⟩,
    commsModOK_of hc hT h hcomm⟩, kerModOK_of hc hT h htests hker⟩
  refine Snd.all_of_forall₂ (fun X x hX hx => ?_) h hall
  rw [Bool.and_eq_true, Bool.or_eq_true] at hx
  simp only [Ops.inN, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨eq_of_rel (rel_mul hc hX hT) (rel_mul hc hT hX) hx.1, ?_⟩
  rcases hx.2 with h1 | h1
  · exact Or.inl (eq_of_rel (rel_mul hc hX hX) (rel_one hc) h1)
  · exact Or.inr (eq_of_rel (rel_mul hc hX hX) hT h1)

end CFSG.KC.OpsLayK.SndP

end
