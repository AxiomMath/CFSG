module

public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Native
public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Steps
import all CFSG.Certificates.Kernel.LocalQT.Steps

public section

namespace CFSG.KC.LocalComp.Ops3Snd

open CFSG.KC.LQT CFSG.KS.Ord CFSG.SectionRank CFSG.SectionRank.Native CFSG.KC.LocalComp.Replay
open scoped Matrix

theorem digApp_corr (c : Lay) (hc : c.ok = true) (hp : c.p = 3) (X : ℕ → ℕ) :
    ∀ (xs : List (Array FV)) (i : ℕ), (∀ x ∈ xs, WFb c.d x) →
      (∀ q < xs.length, Canon c.p c.d c.w (X (i + q))) →
      (∀ (q : ℕ) (hq : q < xs.length),
        CFSG.F3.Native.toMat c.d xs[q] = mat3 c (X (i + q))) →
      ∀ (n v : ℕ) (u : FV), SecS.VCanon c.p c.d c.w v → u.wf = true →
        (spec3b c.d).toVec u = vec3 c v →
        ((ops3 c.d).appDigits xs n u).wf = true ∧
          SecS.VCanon c.p c.d c.w (digApp c 3 X xs.length i n v) ∧
          (spec3b c.d).toVec ((ops3 c.d).appDigits xs n u) =
            vec3 c (digApp c 3 X xs.length i n v) := by
  intro xs
  induction xs with
  | nil =>
    intro i _ _ _ n v u hv hu huv
    exact ⟨hu, hv, huv⟩
  | cons x xs ih =>
    intro i hWF hcan hmat n v u hv hu huv
    have hx : WFb c.d x := hWF x List.mem_cons_self
    have hX0 : Canon c.p c.d c.w (X i) := by
      simpa using hcan 0 (by simp)
    have hx0 : CFSG.F3.Native.toMat c.d x = mat3 c (X i) := hmat 0 (by simp)
    have hx0' : (spec3b c.d).toMat x = mat3 c (X i) := hx0
    obtain ⟨hu', hm⟩ := OpsSpec.app_spec (spec3b c.d) (X := x) hx (n % 3) (v := u) hu
    have hv' := vec3_vpow c hc hp hX0 hv (n % 3)
    have huv' : (spec3b c.d).toVec ((ops3 c.d).app x (n % 3) u) =
        vec3 c (c.vpow (X i) v (n % 3)) := by
      rw [hm, hv'.2, huv, hx0']
    have hcan' : ∀ q < xs.length, Canon c.p c.d c.w (X (i + 1 + q)) := by
      intro q hq
      have h := hcan (q + 1) (by rw [List.length_cons]; omega)
      rwa [show i + (q + 1) = i + 1 + q by omega] at h
    have hmat' : ∀ (q : ℕ) (hq : q < xs.length),
        CFSG.F3.Native.toMat c.d xs[q] = mat3 c (X (i + 1 + q)) := by
      intro q hq
      have h := hmat (q + 1) (by rw [List.length_cons]; omega)
      rw [show i + (q + 1) = i + 1 + q by omega, List.getElem_cons_succ] at h
      exact h
    exact ih (i + 1) (fun y hy => hWF y (List.mem_cons_of_mem _ hy)) hcan' hmat'
      (n / 3) (c.vpow (X i) v (n % 3)) ((ops3 c.d).app x (n % 3) u) hv'.1 hu' huv'


@[expose] def Corr (c : Lay) (Vk : ℕ → ℕ) (N : ℕ) (Rk : List ℕ) (Rn : Array (Array FV)) :
    Prop :=
  Rk.length = Rn.size ∧ ∀ r < Rk.length,
    (Rk.getD r 0 < N ∨ Rk.getD r 0 < 3) ∧ WFb c.d Rn[r]! ∧
      CFSG.F3.Native.toMat c.d Rn[r]! = mat3 c (Vk (Rk.getD r 0))

private theorem corr_set {c : Lay} {Vk : ℕ → ℕ} {N : ℕ} {Rk : List ℕ}
    {Rn : Array (Array FV)} (hR : Corr c Vk N Rk Rn) {k t : ℕ} (hk : k < Rk.length)
    {X : Array FV} (ht : t < N ∨ t < 3) (hX : WFb c.d X)
    (hXm : CFSG.F3.Native.toMat c.d X = mat3 c (Vk t)) :
    Corr c Vk N (Rk.set k t) (Rn.set! k X) := by
  obtain ⟨hlen, hR'⟩ := hR
  have hkR : k < Rn.size := by rw [← hlen]; exact hk
  refine ⟨by rw [List.length_set, Array.size_set!]; exact hlen, fun r hr => ?_⟩
  rw [List.length_set] at hr
  by_cases hrk : k = r
  · have e1 : (Rk.set k t).getD r 0 = t := by
      rw [← hrk]; simp [List.getD_eq_getElem?_getD, hk]
    have e2 : (Rn.set! k X)[r]! = X := by
      rw [← hrk]; exact Array.getElem!_set!_self Rn k X hkR
    rw [e1, e2]
    exact ⟨ht, hX, hXm⟩
  · have e1 : (Rk.set k t).getD r 0 = Rk.getD r 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hrk]
    have e2 : (Rn.set! k X)[r]! = Rn[r]! := Array.getElem!_set!_ne Rn k r X hrk
    rw [e1, e2]
    exact hR' r hr

theorem corr_mul {c : Lay} {Vk P : ℕ → ℕ} {N : ℕ} (hV : Vals c Vk P N) {Rk : List ℕ}
    {Rn : Array (Array FV)} (hR : Corr c Vk N Rk Rn) {i j k t : ℕ} (hi : i < Rk.length)
    (hj : j < Rk.length) (hk : k < Rk.length) (h3 : 3 ≤ t) (hlt : t < N)
    (hP : P t = Rk.getD i 0 + 1048576 * Rk.getD j 0) :
    Corr c Vk N (Rk.set k t) (Rn.set! k ((ops3 c.d).mul Rn[i]! Rn[j]!)) := by
  have hR2 := hR
  obtain ⟨_, hR'⟩ := hR2
  have hRi := hR' i hi
  have hRj := hR' j hj
  have hN : N ≤ 1048576 := hV.hN
  have ha : Rk.getD i 0 < 1048576 := by rcases hRi.1 with h | h <;> omega
  have hstep : stepOK c Vk P t = true := hV.step t h3 hlt
  obtain ⟨_, _, hVt⟩ := stepOK_of_pair hstep hP ha
  have hmul := (mat3_mul c hV.hc hV.hp (hV.canon _ hRi.1) (hV.canon _ hRj.1)).2
  have hWi : (spec3b c.d).WF Rn[i]! := hRi.2.1
  have hWj : (spec3b c.d).WF Rn[j]! := hRj.2.1
  have hX : WFb c.d ((ops3 c.d).mul Rn[i]! Rn[j]!) := (spec3b c.d).mul_wf hWi hWj
  have hXm : CFSG.F3.Native.toMat c.d ((ops3 c.d).mul Rn[i]! Rn[j]!) = mat3 c (Vk t) := by
    have h : CFSG.F3.Native.toMat c.d ((ops3 c.d).mul Rn[i]! Rn[j]!)
        = CFSG.F3.Native.toMat c.d Rn[i]! * CFSG.F3.Native.toMat c.d Rn[j]! :=
      (spec3b c.d).toMat_mul hWi hWj
    rw [h, hRi.2.2, hRj.2.2, hVt, hmul]
  exact corr_set hR hk (Or.inl hlt) hX hXm

theorem corr_pow {c : Lay} {Vk P : ℕ → ℕ} {N : ℕ} (hV : Vals c Vk P N) {Rk : List ℕ}
    {Rn : Array (Array FV)} (hR : Corr c Vk N Rk Rn) {e i k t : ℕ} (hi : i < Rk.length)
    (hk : k < Rk.length)
    (ht : (e = 0 ∧ t = 2) ∨ (t < N ∧ e < expoFail ∧ expoK P (Rk.getD i 0) 64 t = e)) :
    Corr c Vk N (Rk.set k t) (Rn.set! k ((ops3 c.d).pow Rn[i]! e)) := by
  have hR2 := hR
  obtain ⟨_, hR'⟩ := hR2
  have hRi := hR' i hi
  have hWi : (spec3b c.d).WF Rn[i]! := hRi.2.1
  have hX : WFb c.d ((ops3 c.d).pow Rn[i]! e) := (OpsSpec.pow_spec (spec3b c.d) hWi e).1
  have h : CFSG.F3.Native.toMat c.d ((ops3 c.d).pow Rn[i]! e)
      = CFSG.F3.Native.toMat c.d Rn[i]! ^ e := (OpsSpec.pow_spec (spec3b c.d) hWi e).2
  have hmain : CFSG.F3.Native.toMat c.d ((ops3 c.d).pow Rn[i]! e) = mat3 c (Vk t)
      ∧ (t < N ∨ t < 3) := by
    rcases ht with ⟨he0, ht2⟩ | ⟨htN, hef, hek⟩
    · refine ⟨?_, Or.inr (by omega)⟩
      rw [h, hRi.2.2, he0, pow_zero, ht2, hV.two]
    · have hspec := expoK_spec hV (Rk.getD i 0) 64 t (Or.inl htN) (by rw [hek]; exact hef)
      rw [hek] at hspec
      refine ⟨?_, Or.inl htN⟩
      rw [h, hRi.2.2, hspec]
  exact corr_set hR hk hmain.2 hX hmain.1

theorem replay_corr {c : Lay} {Vk P T : ℕ → ℕ} {N : ℕ} (hV : Vals c Vk P N) :
    ∀ (ops : List Op) (s : ℕ) (Rk : List ℕ) (Rn : Array (Array FV)),
      ops.all (Op.lt Rk.length) = true → Corr c Vk N Rk Rn →
      (replayK c Vk P T N ops s Rk).1 = true →
      Corr c Vk N (replayK c Vk P T N ops s Rk).2 (ops.foldl (ops3 c.d).step Rn) := by
  intro ops
  induction ops with
  | nil =>
    intro s Rk Rn _ hR _
    simpa [replayK] using hR
  | cons op ops ih =>
    intro s Rk Rn hall hR hok
    rw [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hop, hall'⟩ := hall
    cases op with
    | mul i j k =>
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
      obtain ⟨⟨hi, hj⟩, hk⟩ := hop
      simp only [replayK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨h3, hlt⟩, hP⟩, hrest⟩ := hok
      have hcorr := corr_mul hV hR hi hj hk h3 hlt (Nat.eq_of_beq_eq_true hP)
      have hall2 : ops.all (Op.lt (Rk.set k (T s)).length) = true := by
        rw [List.length_set]; exact hall'
      have key := ih (s + 1) (Rk.set k (T s))
        (Rn.set! k ((ops3 c.d).mul Rn[i]! Rn[j]!)) hall2 hcorr hrest
      show Corr c Vk N (replayK c Vk P T N ops (s + 1) (Rk.set k (T s))).2
        (ops.foldl (ops3 c.d).step (Rn.set! k ((ops3 c.d).mul Rn[i]! Rn[j]!)))
      exact key
    | pow e i k =>
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
      obtain ⟨hi, hk⟩ := hop
      simp only [replayK, Bool.and_eq_true] at hok
      obtain ⟨hcond, hrest⟩ := hok
      have ht : (e = 0 ∧ T s = 2) ∨
          (T s < N ∧ e < expoFail ∧ expoK P (Rk.getD i 0) 64 (T s) = e) := by
        by_cases he : e = 0
        · subst he
          exact Or.inl ⟨rfl, Nat.eq_of_beq_eq_true (by simpa using hcond)⟩
        · right
          simp only [he, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact ⟨hcond.1.1, hcond.1.2, Nat.eq_of_beq_eq_true hcond.2⟩
      have hcorr := corr_pow hV hR hi hk ht
      have hall2 : ops.all (Op.lt (Rk.set k (T s)).length) = true := by
        rw [List.length_set]; exact hall'
      have key := ih (s + 1) (Rk.set k (T s))
        (Rn.set! k ((ops3 c.d).pow Rn[i]! e)) hall2 hcorr hrest
      show Corr c Vk N (replayK c Vk P T N ops (s + 1) (Rk.set k (T s))).2
        (ops.foldl (ops3 c.d).step (Rn.set! k ((ops3 c.d).pow Rn[i]! e)))
      exact key


theorem replayK_length (c : Lay) (Vk P T : ℕ → ℕ) (N : ℕ) :
    ∀ (ops : List Op) (s : ℕ) (R : List ℕ), (replayK c Vk P T N ops s R).2.length = R.length
  | [], _, _ => rfl
  | .mul i j k :: ops, s, R => by
    change (replayK c Vk P T N ops (s + 1) (R.set k (T s))).2.length = R.length
    rw [replayK_length c Vk P T N ops (s + 1), List.length_set]
  | .pow e i k :: ops, s, R => by
    change (replayK c Vk P T N ops (s + 1) (R.set k (T s))).2.length = R.length
    rw [replayK_length c Vk P T N ops (s + 1), List.length_set]

theorem foldl_step_size (O : Ops (Array FV) FV) :
    ∀ (ops : List Op) (R : Array (Array FV)), (ops.foldl O.step R).size = R.size
  | [], _ => rfl
  | .mul i j k :: ops, R => by
    rw [List.foldl_cons, foldl_step_size O ops]
    change (R.set! k _).size = R.size
    exact Array.size_set! ..
  | .pow e i k :: ops, R => by
    rw [List.foldl_cons, foldl_step_size O ops]
    change (R.set! k _).size = R.size
    exact Array.size_set! ..

theorem commsOK_of_pairs {d : ℕ} :
    ∀ (xs : List (Array FV)), (∀ x ∈ xs, WFb d x) →
      (∀ (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length),
        CFSG.F3.Native.toMat d xs[i] * CFSG.F3.Native.toMat d xs[j] =
          CFSG.F3.Native.toMat d xs[j] * CFSG.F3.Native.toMat d xs[i]) →
      (ops3 d).commsOK xs = true
  | [], _, _ => rfl
  | X :: xs, hwf, hpair => by
    have hX : WFb d X := hwf X List.mem_cons_self
    have hxs : ∀ x ∈ xs, WFb d x := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
    have ih := commsOK_of_pairs xs hxs (fun i j hi hj => by
      have := hpair (i + 1) (j + 1) (by simpa using hi) (by simpa using hj)
      simpa using this)
    change (xs.all ((ops3 d).commOK X) && (ops3 d).commsOK xs) = true
    rw [ih, Bool.and_true, List.all_eq_true]
    intro Y hY
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hY
    have hYw := hxs _ hY
    have h := hpair 0 (j + 1) (by simp) (by simpa using hj)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
    change CFSG.F3.Native.eqM d (CFSG.F3.Native.mul d X xs[j]) (CFSG.F3.Native.mul d xs[j] X) = true
    refine eqM_of_toMat_eq (wfb_mul hX hYw) (wfb_mul hYw hX) ?_
    have e1 : CFSG.F3.Native.toMat d (CFSG.F3.Native.mul d X xs[j]) =
        CFSG.F3.Native.toMat d X * CFSG.F3.Native.toMat d xs[j] := (spec3b d).toMat_mul hX hYw
    have e2 : CFSG.F3.Native.toMat d (CFSG.F3.Native.mul d xs[j] X) =
        CFSG.F3.Native.toMat d xs[j] * CFSG.F3.Native.toMat d X := (spec3b d).toMat_mul hYw hX
    rw [e1, e2]
    exact h

theorem ops3_check_main {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {Vk P T O W : Nat → Nat} {N : Nat} {D : Data}
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (hA : decOK c (Vk 0) LA = true) (hB : decOK c (Vk 1) LB = true) (h1 : Vk 2 = c.ONE)
    (hs : StepsTo (stepOK c Vk P) N) (hr : replayOK c Vk P T N D O W = true)
    (he : elemOK c Vk N O W D.outs.length = true) :
    (ops3 d).check D = true := by
  subst hd
  unfold replayOK at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨hN, h2⟩, hprog⟩, houts⟩, hrep⟩, hOut⟩, hTests⟩ := hr
  have hN' : N ≤ 1048576 := of_decide_eq_true hN
  have hV := vals_of hc hp hN' hA hB h1 hs
  set Rk0 : List ℕ := (List.range D.nregs).map
    (fun x => if x = 0 then 0 else if x = 1 then 1 else 2) with hRk0
  set Rn0 : Array (Array FV) := (ops3 c.d).initRegs ((ops3 c.d).decode D.seedA)
    ((ops3 c.d).decode D.seedB) D.nregs with hRn0
  have hRk0len : Rk0.length = D.nregs := by simp [hRk0]
  have hRn0size : Rn0.size = D.nregs := by simp [hRn0, Ops.initRegs]
  have hcorr0 : Corr c Vk N Rk0 Rn0 := by
    refine ⟨by rw [hRk0len, hRn0size], fun r hr => ?_⟩
    rw [hRk0len] at hr
    have hRk : Rk0.getD r 0 = if r = 0 then 0 else if r = 1 then 1 else 2 := by
      rw [List.getD_eq_getElem _ _ (by simpa [hRk0] using hr)]
      simp [hRk0]
    have hRn : Rn0[r]! = if r = 0 then (ops3 c.d).decode D.seedA
        else if r = 1 then (ops3 c.d).decode D.seedB else (ops3 c.d).one := by
      rw [getElem!_pos Rn0 r (by omega)]
      simp [hRn0, Ops.initRegs]
    rw [hRk, hRn]
    by_cases h0 : r = 0
    · subst h0
      simp only [if_true]
      refine ⟨Or.inr (by norm_num), wfb_rowsOf c.d D.seedA, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.rowsOf c.d D.seedA) = mat3 c (Vk 0)
      exact ((spec3 c.d).toMat_decode D.seedA).trans
        (by rw [hsA]; exact (mat3_decode c hc hp hA).2.symm)
    by_cases h01 : r = 1
    · subst h01
      simp only [if_false, if_true, one_ne_zero]
      refine ⟨Or.inr (by norm_num), wfb_rowsOf c.d D.seedB, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.rowsOf c.d D.seedB) = mat3 c (Vk 1)
      exact ((spec3 c.d).toMat_decode D.seedB).trans
        (by rw [hsB]; exact (mat3_decode c hc hp hB).2.symm)
    · simp only [h0, h01, if_false]
      refine ⟨Or.inr (by norm_num), wfb_idM c.d, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.idM c.d) = mat3 c (Vk 2)
      rw [CFSG.F3.Native.toMat_idM, hV.two]
  have hprog' : D.prog.all (Op.lt Rk0.length) = true := by
    rw [hRk0len]
    exact hprog
  have hcorr := replay_corr hV D.prog 0 Rk0 Rn0 hprog' hcorr0 hrep
  set Rk' := (replayK c Vk P T N D.prog 0 Rk0).2 with hRk'
  set Rn' := D.prog.foldl (ops3 c.d).step Rn0 with hRn'
  have hRk'len : Rk'.length = D.nregs := by rw [hRk', replayK_length, hRk0len]
  have houts' : ∀ i (hi : i < D.outs.length), D.outs[i] < D.nregs := by
    intro i hi
    exact of_decide_eq_true ((List.all_eq_true.1 houts) _ (List.getElem_mem hi))
  have hOut' : ∀ i < D.outs.length, O i = Rk'.getD (D.outs.getD i 0) 0 := by
    intro i hi
    exact Nat.eq_of_beq_eq_true ((List.all_eq_true.1 hOut) i (List.mem_range.2 hi))
  unfold elemOK at he
  obtain ⟨hO, he2⟩ := SecS.andT he
  obtain ⟨hcube, he3⟩ := SecS.andT he2
  obtain ⟨hcomm, hker⟩ := SecS.andT he3
  have hO' := SecS.allLt_spec hO
  have hOlt : ∀ i < D.outs.length, O i < N := fun i hi => Nat.blt_eq.mp (hO' i hi)
  have hcanO : ∀ i < D.outs.length, Canon c.p c.d c.w (Vk (O i)) :=
    fun i hi => hV.canon _ (Or.inl (hOlt i hi))
  set xs : List (Array FV) := D.outs.map (fun r => Rn'[r]!) with hxs
  have hxs_len : xs.length = D.outs.length := by simp [hxs]
  have hxs_get : ∀ (i : ℕ) (hi : i < xs.length), xs[i] = Rn'[D.outs[i]'(hxs_len ▸ hi)]! := by
    intro i hi
    simp [hxs]
  have hxs_info : ∀ (i : ℕ) (hi : i < xs.length),
      WFb c.d xs[i] ∧ CFSG.F3.Native.toMat c.d xs[i] = mat3 c (Vk (O i)) := by
    intro i hi
    have hi' : i < D.outs.length := hxs_len ▸ hi
    have hr := houts' i hi'
    have h := hcorr.2 D.outs[i] (by rw [hRk'len]; exact hr)
    rw [hxs_get i hi]
    have e : Rk'.getD D.outs[i] 0 = O i := by
      rw [hOut' i hi', List.getD_eq_getElem _ _ hi']
    rw [e] at h
    exact ⟨h.2.1, h.2.2⟩
  have hxs_wf : ∀ x ∈ xs, WFb c.d x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact (hxs_info i hi).1
  have hcubeOK : xs.all (ops3 c.d).cubeOK = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    obtain ⟨hxw, hxm⟩ := hxs_info i hi
    have hi' : i < D.outs.length := hxs_len ▸ hi
    obtain ⟨cc, ec⟩ := mat3_mul c hc hp (hcanO i hi') (hcanO i hi')
    obtain ⟨cc2, ec2⟩ := mat3_mul c hc hp cc (hcanO i hi')
    have h3 := Nat.eq_of_beq_eq_true (SecS.allLt_spec hcube i hi')
    have hone : mat3 c (c.mul (c.mul (Vk (O i)) (Vk (O i))) (Vk (O i))) = 1 := by
      rw [h3]
      exact (mat3_one c hc hp).2
    rw [ec2, ec] at hone
    change CFSG.F3.Native.eqM c.d (CFSG.F3.Native.mul c.d (CFSG.F3.Native.mul c.d xs[i] xs[i])
      xs[i]) (CFSG.F3.Native.idM c.d) = true
    refine eqM_of_toMat_eq (wfb_mul (wfb_mul hxw hxw) hxw) (wfb_idM c.d) ?_
    have e1 : CFSG.F3.Native.toMat c.d (CFSG.F3.Native.mul c.d xs[i] xs[i]) =
        CFSG.F3.Native.toMat c.d xs[i] * CFSG.F3.Native.toMat c.d xs[i] :=
      (spec3b c.d).toMat_mul hxw hxw
    have e2 : CFSG.F3.Native.toMat c.d
        (CFSG.F3.Native.mul c.d (CFSG.F3.Native.mul c.d xs[i] xs[i]) xs[i]) =
        CFSG.F3.Native.toMat c.d (CFSG.F3.Native.mul c.d xs[i] xs[i]) *
          CFSG.F3.Native.toMat c.d xs[i] :=
      (spec3b c.d).toMat_mul (wfb_mul hxw hxw) hxw
    rw [e2, e1, hxm, CFSG.F3.Native.toMat_idM]
    exact hone
  have key : ∀ i j : ℕ, j < i → i < D.outs.length →
      mat3 c (Vk (O i)) * mat3 c (Vk (O j)) = mat3 c (Vk (O j)) * mat3 c (Vk (O i)) := by
    intro i j hji hi
    have h := Nat.eq_of_beq_eq_true (SecS.allLt_spec (SecS.allLt_spec hcomm i hi) j hji)
    have h2 := congrArg (mat3 c) h
    rwa [(mat3_mul c hc hp (hcanO i hi) (hcanO j (by omega))).2,
      (mat3_mul c hc hp (hcanO j (by omega)) (hcanO i hi)).2] at h2
  have hcommsOK : (ops3 c.d).commsOK xs = true := by
    refine commsOK_of_pairs xs hxs_wf (fun i j hi hj => ?_)
    rw [(hxs_info i hi).2, (hxs_info j hj).2]
    have hi' : i < D.outs.length := hxs_len ▸ hi
    have hj' : j < D.outs.length := hxs_len ▸ hj
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · exact (key j i hij hj').symm
    · rfl
    · exact key i j hij hi'
  have hkerOK : (ops3 c.d).kerOK xs D.tests = true := by
    unfold Ops.kerOK
    rw [List.all_eq_true]
    intro n hn
    rw [List.mem_range, hxs_len] at hn
    have hk := SecS.allLt_spec hker n hn
    simp only [SecS.strictB_eq] at hk
    obtain ⟨ht, hne⟩ := SecS.andT hk
    have htd : W (Nat.succ n) < c.d := Nat.blt_eq.mp ht
    have hmem := (List.all_eq_true.1 hTests) n (List.mem_range.2 hn)
    refine List.any_eq_true.2 ⟨W (n + 1), by simpa using hmem, ?_⟩
    unfold Ops.moved
    apply vne_of_toVec_ne
    obtain ⟨hw, hcan, hvec⟩ := digApp_corr c hc hp (fun i => Vk (O i)) xs 0 hxs_wf
      (fun q hq => by simpa using hcanO q (hxs_len ▸ hq))
      (fun q hq => by simpa using (hxs_info q hq).2) (n + 1) (c.unit (W (n + 1)))
      ((ops3 c.d).unit (W (n + 1))) (SecS.unit_canon c hc htd) (by simp [ops3, CFSG.F3.Native.V.wf])
      (by rw [toVec_unit, vec3_unit c hc hp htd])
    rw [hvec, toVec_unit, ← vec3_unit c hc hp htd]
    intro heq
    have hunit := SecS.unit_canon c hc htd
    rw [hxs_len] at hcan heq
    exact SecS.ne_of_notB hne (vec3_inj c hc hcan hunit hp heq)
  have hcheck : (ops3 c.d).check D = (decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
      D.outs.all (decide <| · < D.nregs) && (ops3 c.d).elemOK xs D.tests) := rfl
  rw [hcheck, h2, hprog, houts]
  change (true && true && true && ((xs.all (ops3 c.d).cubeOK && (ops3 c.d).commsOK xs) &&
    (ops3 c.d).kerOK xs D.tests)) = true
  rw [hcubeOK, hcommsOK, hkerOK]
  rfl

end CFSG.KC.LocalComp.Ops3Snd

end
