module

public import Certificates.Data.Kernel.OpsLayKNorm
public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Bridge
public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Native

public section

namespace CFSG.KC.OpsLayK.Snd

open CFSG.KC.LQT CFSG.KS.Ord CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.KC.LocalComp.Ops3Snd
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

theorem ne_of_not_beq {a b : ℕ} (h : (!Nat.beq a b) = true) : a ≠ b := by
  cases hb : Nat.beq a b
  · exact Nat.ne_of_beq_eq_false hb
  · rw [hb] at h
    exact absurd h (by decide)

theorem getD_eq_of_lt {α : Type} {l : List α} {n : ℕ} (d : α) (hn : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]

theorem ofFn_getElem! {α : Type} [Inhabited α] {N : ℕ} (f : Fin N → α) {i : ℕ} (hi : i < N) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem lt_of_all {l : List ℕ} {m : ℕ} (h : l.all (decide <| · < m) = true) {x : ℕ}
    (hx : x ∈ l) : x < m :=
  of_decide_eq_true (List.all_eq_true.1 h x hx)

theorem any_mono {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ k ∈ l, p k = true → q k = true) (hp : l.any p = true) : l.any q = true := by
  obtain ⟨k, hk, hpk⟩ := List.any_eq_true.1 hp
  exact List.any_eq_true.2 ⟨k, hk, h k hk hpk⟩

@[expose] def LRel (c : Lay) (X : Array FV) (x : ℕ) : Prop :=
  Canon c.p c.d c.w x ∧ WFb c.d X ∧ CFSG.F3.Native.toMat c.d X = mat3 c x

@[expose] def LVRel (c : Lay) (u : FV) (v : ℕ) : Prop :=
  SecS.VCanon c.p c.d c.w v ∧ u.wf = true ∧ (spec3b c.d).toVec u = vec3 c v

theorem rel_mul {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {X Y : Array FV} {x y : ℕ}
    (hX : LRel c X x) (hY : LRel c Y y) : LRel c ((ops3 c.d).mul X Y) (c.mul x y) := by
  obtain ⟨cx, wX, mX⟩ := hX
  obtain ⟨cy, wY, mY⟩ := hY
  obtain ⟨cxy, mxy⟩ := mat3_mul c hc hp cx cy
  refine ⟨cxy, wfb_mul wX wY, ?_⟩
  have h : CFSG.F3.Native.toMat c.d ((ops3 c.d).mul X Y) =
      CFSG.F3.Native.toMat c.d X * CFSG.F3.Native.toMat c.d Y := (spec3b c.d).toMat_mul wX wY
  rw [h, mX, mY, mxy]

theorem rel_one {c : Lay} (hc : c.ok = true) (hp : c.p = 3) : LRel c (ops3 c.d).one c.ONE := by
  obtain ⟨c1, m1⟩ := mat3_one c hc hp
  refine ⟨c1, wfb_idM c.d, ?_⟩
  show CFSG.F3.Native.toMat c.d (CFSG.F3.Native.idM c.d) = _
  rw [CFSG.F3.Native.toMat_idM, m1]

theorem rel_decode {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {M : ℕ} {l : List Char}
    {s : String} (hM : decOK c M l = true) (hs : s = String.ofList l) :
    LRel c ((ops3 c.d).decode s) M := by
  obtain ⟨cM, mM⟩ := mat3_decode c hc hp hM
  refine ⟨cM, wfb_rowsOf c.d s, ?_⟩
  rw [mM, ← hs]
  exact (spec3b c.d).toMat_decode s

private theorem powN_succ (c : Lay) (f X e : ℕ) :
    powN c (f + 1) X e =
      Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) (powN c f (c.mul X X) (e / 2))
            (c.mul X (powN c f (c.mul X X) (e / 2))) (Nat.beq (e % 2) 1))
          X (Nat.beq e 1))
        c.ONE (Nat.beq e 0) := by
  show Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (CFSG.KC.Loop.strictN (c.mul X X) fun X2 =>
          CFSG.KC.Loop.strictN (powN c f X2 (e / 2)) fun Y =>
            Bool.rec (motive := fun _ => ℕ) Y (c.mul X Y) (Nat.beq (e % 2) 1))
        X (Nat.beq e 1))
      c.ONE (Nat.beq e 0) = _
  simp only [strictN_eq]

theorem powN_spec {c : Lay} (hc : c.ok = true) (hp : c.p = 3) :
    ∀ (f : ℕ) {X : ℕ} (e : ℕ), Canon c.p c.d c.w X → e < 2 ^ f →
      Canon c.p c.d c.w (powN c f X e) ∧ mat3 c (powN c f X e) = mat3 c X ^ e
  | 0, X, e, _, he => by
    have e0 : e = 0 := by simpa using he
    subst e0
    exact ⟨(mat3_one c hc hp).1, by rw [pow_zero]; exact (mat3_one c hc hp).2⟩
  | f + 1, X, e, hX, he => by
    rw [powN_succ]
    rcases Nat.lt_or_ge e 2 with h2 | h2
    · rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · exact ⟨(mat3_one c hc hp).1, by rw [pow_zero]; exact (mat3_one c hc hp).2⟩
      · exact ⟨hX, (pow_one _).symm⟩
    · rw [beq_false (show e ≠ 0 by omega), beq_false (show e ≠ 1 by omega)]
      obtain ⟨cX2, mX2⟩ := mat3_mul c hc hp hX hX
      have he2 : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
      obtain ⟨cY, mY⟩ := powN_spec hc hp f (e / 2) cX2 he2
      have mY' : mat3 c (powN c f (c.mul X X) (e / 2)) = mat3 c X ^ (2 * (e / 2)) := by
        rw [mY, mX2, ← pow_two, ← pow_mul]
      rcases Nat.mod_two_eq_zero_or_one e with ho | ho
      · rw [beq_false (show e % 2 ≠ 1 by omega)]
        show Canon c.p c.d c.w (powN c f (c.mul X X) (e / 2)) ∧
          mat3 c (powN c f (c.mul X X) (e / 2)) = mat3 c X ^ e
        refine ⟨cY, ?_⟩
        rw [mY']
        congr 1
        omega
      · rw [beq_true ho]
        show Canon c.p c.d c.w (c.mul X (powN c f (c.mul X X) (e / 2))) ∧
          mat3 c (c.mul X (powN c f (c.mul X X) (e / 2))) = mat3 c X ^ e
        obtain ⟨cZ, mZ⟩ := mat3_mul c hc hp hX cY
        refine ⟨cZ, ?_⟩
        rw [mZ, mY', ← pow_succ']
        congr 1
        omega

theorem rel_pow {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {X : Array FV} {x : ℕ}
    (hX : LRel c X x) {e : ℕ} (he : e < 65536) : LRel c ((ops3 c.d).pow X e) (powK c x e) := by
  obtain ⟨cx, wX, mX⟩ := hX
  have wX' : (spec3b c.d).WF X := wX
  obtain ⟨cy, my⟩ := powN_spec hc hp 17 e cx (lt_of_lt_of_le he (by norm_num))
  obtain ⟨wY, mY⟩ := OpsSpec.pow_spec (spec3b c.d) wX' e
  refine ⟨cy, wY, ?_⟩
  have h : CFSG.F3.Native.toMat c.d ((ops3 c.d).pow X e) = CFSG.F3.Native.toMat c.d X ^ e := mY
  rw [h, mX]
  exact my.symm

theorem rel_commM {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {X Y : Array FV} {x y : ℕ}
    (hX : LRel c X x) (hY : LRel c Y y) {r : ℕ} (hr : r < 65536) :
    LRel c ((ops3 c.d).commM r X Y) (commMK c r x y) :=
  rel_mul hc hp (rel_mul hc hp (rel_mul hc hp hX hY) (rel_pow hc hp hX (by omega)))
    (rel_pow hc hp hY (by omega))

theorem eq_of_rel {c : Lay} {X Y : Array FV} {x y : ℕ} (hX : LRel c X x) (hY : LRel c Y y)
    (h : Nat.beq x y = true) : (ops3 c.d).eq X Y = true := by
  have hxy := Nat.eq_of_beq_eq_true h
  subst hxy
  exact eqM_of_toMat_eq hX.2.1 hY.2.1 (hX.2.2.trans hY.2.2.symm)

theorem eq_pow_one {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {X : Array FV} {x e : ℕ}
    (hX : LRel c X x) (he : e < 65536) (h : Nat.beq (powK c x e) c.ONE = true) :
    (ops3 c.d).eq ((ops3 c.d).pow X e) (ops3 c.d).one = true :=
  eq_of_rel (rel_pow hc hp hX he) (rel_one hc hp) h

theorem conjOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {H X W : Array FV} {a x w : ℕ}
    (hH : LRel c H a) (hX : LRel c X x) (hW : LRel c W w) (hk : conjK c a x w = true) :
    (ops3 c.d).conjOK H X W = true :=
  eq_of_rel (rel_mul hc hp hH hX) (rel_mul hc hp hW hH) hk

theorem vrel_unit {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {t : ℕ} (ht : t < c.d) :
    LVRel c ((ops3 c.d).unit t) (c.unit t) :=
  ⟨SecS.unit_canon c hc ht, by simp [ops3, CFSG.F3.Native.V.wf],
    by rw [toVec_unit, vec3_unit c hc hp ht]⟩

private theorem vec3_vec {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {v x : ℕ}
    (hv : SecS.VCanon c.p c.d c.w v) (hx : Canon c.p c.d c.w x) :
    SecS.VCanon c.p c.d c.w (c.vec v x) ∧ vec3 c (c.vec v x) = vec3 c v ᵥ* mat3 c x := by
  have h := vec3_vpow c hc hp hx hv 1
  rw [pow_one] at h
  exact h

theorem vrel_vmul {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {u : FV} {v : ℕ}
    {X : Array FV} {x : ℕ} (hu : LVRel c u v) (hX : LRel c X x) :
    LVRel c ((ops3 c.d).vmul u X) (c.vec v x) := by
  obtain ⟨cv, wu, mu⟩ := hu
  obtain ⟨cx, wX, mX⟩ := hX
  have hwX : (spec3b c.d).WF X := wX
  have hwu : (spec3b c.d).VWF u := wu
  obtain ⟨cv', mv'⟩ := vec3_vec hc hp cv cx
  refine ⟨cv', (spec3b c.d).vmul_wf hwu hwX, ?_⟩
  have e : (spec3b c.d).toMat X = mat3 c x := mX
  rw [(spec3b c.d).toVec_vmul hwu hwX, mu, mv', e]

theorem vrel_vpow {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {u : FV} {v : ℕ}
    {X : Array FV} {x : ℕ} (hu : LVRel c u v) (hX : LRel c X x) (n : ℕ) :
    LVRel c ((ops3 c.d).app X n u) (c.vpow x v n) := by
  obtain ⟨cv, wu, mu⟩ := hu
  obtain ⟨cx, wX, mX⟩ := hX
  have hwX : (spec3b c.d).WF X := wX
  have hwu : (spec3b c.d).VWF u := wu
  obtain ⟨w1, m1⟩ := OpsSpec.app_spec (spec3b c.d) hwX n hwu
  obtain ⟨cv', mv'⟩ := vec3_vpow c hc hp cx cv n
  have e : (spec3b c.d).toMat X = mat3 c x := mX
  exact ⟨cv', w1, by rw [m1, mu, e, mv']⟩

theorem vne_of_vrel {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {u u' : FV} {v v' : ℕ}
    (hu : LVRel c u v) (hu' : LVRel c u' v') (h : v ≠ v') : (ops3 c.d).vne u u' = true := by
  apply vne_of_toVec_ne
  rw [hu.2.2, hu'.2.2]
  intro heq
  exact h (vec3_inj c hc hu.1 hu'.1 hp heq)

theorem forall₂_length {α β : Type} {R : α → β → Prop} {Xs : List α} {xs : List β}
    (h : List.Forall₂ R Xs xs) : Xs.length = xs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem all_of_forall₂ {α β : Type} {R : α → β → Prop} {P : α → Bool} {p : β → Bool}
    (hPp : ∀ X x, R X x → p x = true → P X = true) {Xs : List α} {xs : List β}
    (h : List.Forall₂ R Xs xs) : xs.all p = true → Xs.all P = true := by
  induction h with
  | nil => intro _; rfl
  | cons hX _ ih =>
    intro hp
    rw [List.all_cons, Bool.and_eq_true] at hp ⊢
    exact ⟨hPp _ _ hX hp.1, ih hp.2⟩

theorem forall₂_get {c : Lay} {Xs : List (Array FV)} {xs : List ℕ}
    (h : List.Forall₂ (LRel c) Xs xs) {i : ℕ} (hi : i < xs.length) :
    LRel c Xs[i]! (xs.getD i c.ONE) := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hX _ ih =>
    cases i with
    | zero =>
      rw [List.getElem!_cons_zero, List.getD_cons_zero]
      exact hX
    | succ i =>
      rw [List.getElem!_cons_succ, List.getD_cons_succ]
      exact ih (by simpa using hi)

theorem vrel_appBase {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (b : ℕ)
    {Xs : List (Array FV)} {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) :
    ∀ (n : ℕ) {u : FV} {v : ℕ}, LVRel c u v →
      LVRel c ((ops3 c.d).appBase b Xs n u) (appBaseK c b xs n v) := by
  induction h with
  | nil => intro n u v hu; exact hu
  | cons hX _ ih => intro n u v hu; exact ih (n / b) (vrel_vpow hc hp hu hX (n % b))

theorem vrel_appDigits {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {Xs : List (Array FV)}
    {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) :
    ∀ (n : ℕ) {u : FV} {v : ℕ}, LVRel c u v →
      LVRel c ((ops3 c.d).appDigits Xs n u) (appBaseK c 3 xs n v) := by
  induction h with
  | nil => intro n u v hu; exact hu
  | cons hX _ ih => intro n u v hu; exact ih (n / 3) (vrel_vpow hc hp hu hX (n % 3))

theorem rel_powProd {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {Xs : List (Array FV)}
    {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) :
    ∀ (f : ℕ → ℕ), (∀ k < xs.length, f k < 65536) →
      LRel c ((ops3 c.d).powProdIdx Xs f) (powProdK c xs f) := by
  induction h with
  | nil => intro f _; exact rel_one hc hp
  | cons hX _ ih =>
    intro f hf
    exact rel_mul hc hp (rel_pow hc hp hX (hf 0 (by simp)))
      (ih (fun k => f (k + 1)) (fun k hk => hf (k + 1) (by simp; omega)))

@[expose] noncomputable def runL (c : Lay) (prog : List Op) (R : List ℕ) : List ℕ :=
  prog.foldl (fun R o => R.set (Op.tgt o) (stepV c R o)) R

theorem runC_eq (c : Lay) : ∀ (prog : List Op) (R : List ℕ) (k : List ℕ → Bool),
    runC c prog R k = k (runL c prog R)
  | [], _, _ => rfl
  | o :: prog, R, k => by
    show strictB (stepV c R o) (fun v => runC c prog (R.set (Op.tgt o) v) k) = _
    rw [SecS.strictB_eq]
    exact runC_eq c prog _ k

theorem runL_length (c : Lay) : ∀ (prog : List Op) (R : List ℕ),
    (runL c prog R).length = R.length
  | [], _ => rfl
  | o :: prog, R => by
    show (runL c prog (R.set (Op.tgt o) (stepV c R o))).length = R.length
    rw [runL_length c prog, List.length_set]

theorem runL_initR_length (c : Lay) (prog : List Op) (A B n : ℕ) :
    (runL c prog (initR c A B n)).length = n := by
  rw [runL_length]
  simp [initR]

theorem progOK_spec {n : ℕ} {prog : List Op} (h : progOK n prog = true) :
    2 ≤ n ∧ prog.all (Op.lt n) = true := by
  simp only [progOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

@[expose] def LCorr (c : Lay) (R : List ℕ) (Rn : Array (Array FV)) : Prop :=
  R.length = Rn.size ∧ ∀ r < R.length, LRel c Rn[r]! (getR c R r)

theorem lcorr_set {c : Lay} {R : List ℕ} {Rn : Array (Array FV)} (hR : LCorr c R Rn) {k : ℕ}
    (hk : k < R.length) {X : Array FV} {x : ℕ} (hX : LRel c X x) :
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

theorem lcorr_step {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {R : List ℕ}
    {Rn : Array (Array FV)} (hR : LCorr c R Rn) {o : Op} (hlt : Op.lt R.length o = true)
    (hexp : expOK o = true) :
    LCorr c (R.set (Op.tgt o) (stepV c R o)) ((ops3 c.d).step Rn o) := by
  cases o with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨⟨hi, hj⟩, hk⟩ := hlt
    exact lcorr_set hR hk (rel_mul hc hp (hR.2 i hi) (hR.2 j hj))
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨hi, hk⟩ := hlt
    have he : e < 65536 := by simpa [expOK] using hexp
    exact lcorr_set hR hk (rel_pow hc hp (hR.2 i hi) he)

theorem lcorr_run {c : Lay} (hc : c.ok = true) (hp : c.p = 3) :
    ∀ (prog : List Op) (R : List ℕ) (Rn : Array (Array FV)),
      prog.all (Op.lt R.length) = true → prog.all expOK = true → LCorr c R Rn →
        LCorr c (runL c prog R) (prog.foldl (ops3 c.d).step Rn)
  | [], _, _, _, _, hR => hR
  | o :: prog, R, Rn, hlt, hexp, hR => by
    rw [List.all_cons, Bool.and_eq_true] at hlt hexp
    have h1 := lcorr_step hc hp hR hlt.1 hexp.1
    have hlt' : prog.all (Op.lt (R.set (Op.tgt o) (stepV c R o)).length) = true := by
      rw [List.length_set]
      exact hlt.2
    exact lcorr_run hc hp prog _ _ hlt' hexp.2 h1

theorem lcorr_init {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {A B n : ℕ} {LA LB : List Char}
    {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) :
    LCorr c (initR c A B n)
      ((ops3 c.d).initRegs ((ops3 c.d).decode sA) ((ops3 c.d).decode sB) n) := by
  have hlen : (initR c A B n).length = n := by simp [initR]
  refine ⟨by rw [hlen]; simp [Ops.initRegs], fun r hr => ?_⟩
  rw [hlen] at hr
  have e1 : getR c (initR c A B n) r = if r = 0 then A else if r = 1 then B else c.ONE := by
    unfold getR initR
    rw [getD_eq_of_lt _ (by simpa using hr), List.getElem_map, List.getElem_range]
  have e2 : ((ops3 c.d).initRegs ((ops3 c.d).decode sA) ((ops3 c.d).decode sB) n)[r]! =
      if r = 0 then (ops3 c.d).decode sA else if r = 1 then (ops3 c.d).decode sB
        else (ops3 c.d).one := by
    unfold Ops.initRegs
    rw [ofFn_getElem! _ hr]
  rw [e1, e2]
  by_cases h0 : r = 0
  · rw [if_pos h0, if_pos h0]
    exact rel_decode hc hp hA hsA
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : r = 1
    · rw [if_pos h1, if_pos h1]
      exact rel_decode hc hp hB hsB
    · rw [if_neg h1, if_neg h1]
      exact rel_one hc hp

theorem lcorr_regs {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {A B : ℕ} {LA LB : List Char}
    {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : ℕ} {prog : List Op}
    (hprog : progOK n prog = true) :
    LCorr c (runL c prog (initR c A B n))
      ((ops3 c.d).run prog
        ((ops3 c.d).initRegs ((ops3 c.d).decode sA) ((ops3 c.d).decode sB) n)) := by
  simp only [progOK, Bool.and_eq_true] at hprog
  obtain ⟨⟨hexp, _⟩, hlt⟩ := hprog
  have hlen : (initR c A B n).length = n := by simp [initR]
  exact lcorr_run hc hp prog _ _ (by rw [hlen]; exact hlt) hexp (lcorr_init hc hp hA hB hsA hsB)

theorem forall₂_map {c : Lay} {R : List ℕ} {Rn : Array (Array FV)} (h : LCorr c R Rn) :
    ∀ (outs : List ℕ), (∀ r ∈ outs, r < R.length) →
      List.Forall₂ (LRel c) (outs.map fun r => Rn[r]!) (outs.map (getR c R))
  | [], _ => List.Forall₂.nil
  | r :: outs, hr => List.Forall₂.cons (h.2 r (hr r List.mem_cons_self))
      (forall₂_map h outs fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))

theorem commsModOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {T : Array FV} {t : ℕ}
    (hT : LRel c T t) {Xs : List (Array FV)} {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) :
    commsModK c t xs = true → (ops3 c.d).commsModOK T Xs = true := by
  induction h with
  | nil => intro _; rfl
  | cons hX h' ih =>
    intro hk
    simp only [commsModK, Ops.commsModOK, Bool.and_eq_true] at hk ⊢
    refine ⟨all_of_forall₂ (fun Y y hY hy => ?_) h' hk.1, ih hk.2⟩
    simp only [Ops.commModOK, Bool.or_eq_true] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (eq_of_rel (rel_mul hc hp hX hY) (rel_mul hc hp hY hX) hy)
    · exact Or.inr (eq_of_rel (rel_mul hc hp hX hY) (rel_mul hc hp hT (rel_mul hc hp hY hX)) hy)

theorem commsOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {Xs : List (Array FV)}
    {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) :
    commsK c xs = true → (ops3 c.d).commsOK Xs = true := by
  induction h with
  | nil => intro _; rfl
  | cons hX h' ih =>
    intro hk
    simp only [commsK, Ops.commsOK, Bool.and_eq_true] at hk ⊢
    refine ⟨all_of_forall₂ ?_ h' hk.1, ih hk.2⟩
    intro Y y hY hy
    exact eq_of_rel (rel_mul hc hp hX hY) (rel_mul hc hp hY hX) hy

theorem kerModOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {T : Array FV} {t : ℕ}
    (hT : LRel c T t) {Xs : List (Array FV)} {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs)
    {tests : List ℕ} (htests : ∀ k ∈ tests, k < c.d)
    (hk : ((List.range (2 ^ xs.length - 1)).all fun n =>
      tests.any (fun k => !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.unit k)) &&
        tests.any (fun k =>
          !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.vec (c.unit k) t))) = true) :
    (ops3 c.d).kerModOK T Xs tests = true := by
  unfold Ops.kerModOK
  rw [forall₂_length h]
  rw [List.all_eq_true] at hk ⊢
  intro n hn
  have hkn := hk n hn
  rw [Bool.and_eq_true] at hkn
  simp only [Ops.outsideN, Bool.and_eq_true]
  constructor
  · refine any_mono (fun k hk' hb => ?_) hkn.1
    have hu := vrel_unit hc hp (htests k hk')
    exact vne_of_vrel hc hp (vrel_appBase hc hp 2 h (n + 1) hu) hu (ne_of_not_beq hb)
  · refine any_mono (fun k hk' hb => ?_) hkn.2
    have hu := vrel_unit hc hp (htests k hk')
    exact vne_of_vrel hc hp (vrel_appBase hc hp 2 h (n + 1) hu) (vrel_vmul hc hp hu hT)
      (ne_of_not_beq hb)

theorem secOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {T : Array FV} {t : ℕ}
    (hT : LRel c T t) {Xs : List (Array FV)} {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs)
    {tests : List ℕ} (htests : ∀ k ∈ tests, k < c.d)
    (hk : (Nat.beq (c.mul t t) c.ONE &&
      xs.all (fun X => Nat.beq (c.mul X t) (c.mul t X) &&
        (Nat.beq (c.mul X X) c.ONE || Nat.beq (c.mul X X) t)) &&
      commsModK c t xs &&
      (List.range (2 ^ xs.length - 1)).all fun n =>
        tests.any (fun k => !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.unit k)) &&
          tests.any (fun k =>
            !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.vec (c.unit k) t))) = true) :
    (ops3 c.d).secOK T Xs tests = true := by
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨hTT, hall⟩, hcomm⟩, hker⟩ := hk
  unfold Ops.secOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨eq_of_rel (rel_mul hc hp hT hT) (rel_one hc hp) hTT, ?_⟩,
    commsModOK_of hc hp hT h hcomm⟩, kerModOK_of hc hp hT h htests hker⟩
  refine all_of_forall₂ (fun X x hX hx => ?_) h hall
  rw [Bool.and_eq_true, Bool.or_eq_true] at hx
  simp only [Ops.inN, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨eq_of_rel (rel_mul hc hp hX hT) (rel_mul hc hp hT hX) hx.1, ?_⟩
  rcases hx.2 with h1 | h1
  · exact Or.inl (eq_of_rel (rel_mul hc hp hX hX) (rel_one hc hp) h1)
  · exact Or.inr (eq_of_rel (rel_mul hc hp hX hX) hT h1)

theorem kerOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {Xs : List (Array FV)}
    {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) {tests : List ℕ}
    (htests : ∀ k ∈ tests, k < c.d)
    (hk : ((List.range (3 ^ xs.length - 1)).all fun n =>
      tests.any fun k => !Nat.beq (appBaseK c 3 xs (n + 1) (c.unit k)) (c.unit k)) = true) :
    (ops3 c.d).kerOK Xs tests = true := by
  unfold Ops.kerOK
  rw [forall₂_length h]
  rw [List.all_eq_true] at hk ⊢
  intro n hn
  refine any_mono (fun k hk' hb => ?_) (hk n hn)
  have hu := vrel_unit hc hp (htests k hk')
  exact vne_of_vrel hc hp (vrel_appDigits hc hp h (n + 1) hu) hu (ne_of_not_beq hb)

theorem elemOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {Xs : List (Array FV)}
    {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) {tests : List ℕ}
    (htests : ∀ k ∈ tests, k < c.d) (hk : elemK c xs tests = true) :
    (ops3 c.d).elemOK Xs tests = true := by
  unfold elemK at hk
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk
  obtain ⟨⟨hcube, hcomm⟩, hker⟩ := hk
  unfold Ops.elemOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨all_of_forall₂ (fun X x hX hx => ?_) h hcube, commsOK_of hc hp h hcomm⟩,
    kerOK_of hc hp h htests hker⟩
  exact eq_of_rel (rel_mul hc hp (rel_mul hc hp hX hX) hX) (rel_one hc hp) hx

theorem allDistinct_pairwise {L : List ℕ} (h : allDistinct L = true) : L.Pairwise (· ≠ ·) := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    simp only [allDistinct, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons (fun y hy => ne_of_not_beq (h.1 y hy)) (ih h.2)

theorem normalFormOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (b : ℕ)
    {Xs : List (Array FV)} {xs : List ℕ} (h : List.Forall₂ (LRel c) Xs xs) {t : ℕ}
    (ht : t < c.d) (hk : normalK c b xs t = true) : (ops3 c.d).normalFormOK b Xs t = true := by
  have hpw := List.pairwise_iff_getElem.1 (allDistinct_pairwise hk)
  have hlen := forall₂_length h
  have hu := vrel_unit hc hp ht
  unfold Ops.normalFormOK Ops.distinctOK
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range, Array.size_ofFn] at hi
  rw [List.mem_range] at hj
  have hi' : i < b ^ xs.length := hlen ▸ hi
  rw [ofFn_getElem! _ hi, ofFn_getElem! _ (lt_trans hj hi)]
  have hne := hpw j i (by simp only [List.length_map, List.length_range]; omega)
    (by simp only [List.length_map, List.length_range]; omega) hj
  simp only [List.getElem_map, List.getElem_range] at hne
  exact vne_of_vrel hc hp (vrel_appBase hc hp b h i hu) (vrel_appBase hc hp b h j hu)
    (Ne.symm hne)

theorem normOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {Rf : List ℕ}
    {Rn : Array (Array FV)} (hL : LCorr c Rf Rn) {nregs : ℕ} (hlen : Rf.length = nregs)
    {X Y Z : Array FV} {x y z : ℕ} (hX : LRel c X x) (hY : LRel c Y y) (hZ : LRel c Z z)
    {N : Cub2NormData} (hk : normK c N nregs Rf x y z = true) :
    (ops3 c.d).normOK N nregs Rn X Y Z = true := by
  unfold normK at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hk
  obtain ⟨hrh, hoh, hexp, hH1, hcx, hcy⟩ := hk
  have hH := hL.2 N.rh (by rw [hlen]; exact hrh)
  have e : ∀ v ∈ [N.oh, N.a, N.b, N.c, N.d, N.k, N.l], v < 65536 :=
    fun v hv => lt_of_all hexp hv
  unfold Ops.normOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hrh, hoh, eq_pow_one hc hp hH (e N.oh (by simp)) hH1,
    conjOK_of hc hp hH hX ?_ hcx, conjOK_of hc hp hH hY ?_ hcy⟩
  · exact rel_mul hc hp (rel_mul hc hp (rel_pow hc hp hX (e N.a (by simp)))
      (rel_pow hc hp hY (e N.b (by simp)))) (rel_pow hc hp hZ (e N.k (by simp)))
  · exact rel_mul hc hp (rel_mul hc hp (rel_pow hc hp hX (e N.c (by simp)))
      (rel_pow hc hp hY (e N.d (by simp)))) (rel_pow hc hp hZ (e N.l (by simp)))

theorem normGens_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {Rf : List ℕ}
    {Rn : Array (Array FV)} (hL : LCorr c Rf Rn) {nregs : ℕ} (hlen : Rf.length = nregs)
    {outs gens : List ℕ} (houts : ∀ r ∈ outs, r < nregs) (hgens : ∀ g ∈ gens, g < nregs)
    {og : ℕ} (hog : og < 65536) {expo : ℕ → ℕ → ℕ → ℕ}
    (hexpo : ∀ j < gens.length, ∀ i < outs.length, ∀ k < outs.length, expo j k i < 65536)
    (hk : ((List.range gens.length).all fun j =>
      Nat.beq (powK c (getR c Rf (gens.getD j 0)) og) c.ONE &&
        (List.range outs.length).all fun i =>
          conjK c (getR c Rf (gens.getD j 0)) ((outs.map (getR c Rf)).getD i c.ONE)
            (powProdK c (outs.map (getR c Rf)) fun k => expo j k i)) = true) :
    ((List.range gens.length).all fun j =>
      decide (gens[j]! < nregs) &&
        (ops3 c.d).eq ((ops3 c.d).pow Rn[gens[j]!]! og) (ops3 c.d).one &&
        (List.range (outs.map fun r => Rn[r]!).length).all fun i =>
          (ops3 c.d).conjOK Rn[gens[j]!]! (outs.map fun r => Rn[r]!)[i]!
            ((ops3 c.d).powProdIdx (outs.map fun r => Rn[r]!) fun k => expo j k i)) = true := by
  have hxs := forall₂_map hL outs (fun r hr => by rw [hlen]; exact houts r hr)
  rw [List.all_eq_true] at hk ⊢
  intro j hj
  have hkj := hk j hj
  rw [List.mem_range] at hj
  rw [Bool.and_eq_true] at hkj
  have hgj : gens[j]! = gens.getD j 0 := by
    rw [getElem!_pos gens j hj, getD_eq_of_lt _ hj]
  have hg : gens.getD j 0 < nregs := by
    rw [getD_eq_of_lt _ hj]
    exact hgens _ (List.getElem_mem hj)
  have hG := hL.2 (gens.getD j 0) (by rw [hlen]; exact hg)
  rw [hgj, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨decide_eq_true hg, eq_pow_one hc hp hG hog hkj.1⟩, ?_⟩
  have hkj2 := hkj.2
  rw [List.all_eq_true] at hkj2 ⊢
  intro i hi
  rw [List.mem_range, List.length_map] at hi
  have hki := hkj2 i (List.mem_range.2 hi)
  have hXi := forall₂_get hxs (i := i) (by simpa using hi)
  have hW := rel_powProd hc hp hxs (fun k => expo j k i)
    (fun k hk' => hexpo j hj i hi k (by simpa using hk'))
  exact conjOK_of hc hp hG hXi hW hki

end CFSG.KC.OpsLayK.Snd

end
