module

public import Certificates.Data.Kernel.LocalComp.ReplayWit
public import CFSG.Certificates.Kernel.OpsLayKSnd
public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Replay

public section

namespace CFSG.KC.LocalComp.SqReplaySnd

open CFSG.KC.LQT CFSG.KS.Ord CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.KC.LocalComp.Ops3Snd CFSG.KC.LocalComp.Replay CFSG.KC.OpsLayK
open scoped Matrix

theorem mat3_pow {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {X : ℕ}
    (hX : Canon c.p c.d c.w X) (e : ℕ) :
    Canon c.p c.d c.w (c.pow X e) ∧ mat3 c (c.pow X e) = mat3 c X ^ e := by
  obtain ⟨h1, h2⟩ := SecS.pow_sound c hc hX e
  unfold mat3
  rw [hp] at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem rel_lpow {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {X : Array FV} {x : ℕ}
    (hX : Snd.LRel c X x) (e : ℕ) : Snd.LRel c ((ops3 c.d).pow X e) (c.pow x e) := by
  obtain ⟨cx, wX, mX⟩ := hX
  have wX' : (spec3b c.d).WF X := wX
  obtain ⟨cy, my⟩ := mat3_pow hc hp cx e
  obtain ⟨wY, mY⟩ := OpsSpec.pow_spec (spec3b c.d) wX' e
  refine ⟨cy, wY, ?_⟩
  have h : CFSG.F3.Native.toMat c.d ((ops3 c.d).pow X e) =
      CFSG.F3.Native.toMat c.d X ^ e := mY
  rw [h, mX]
  exact my.symm

theorem normalFormOK_of_inj {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (b : ℕ)
    {Xs : List (Array FV)} {xs : List ℕ} (h : List.Forall₂ (Snd.LRel c) Xs xs) {t : ℕ}
    (ht : t < c.d)
    (hinj : ∀ i < b ^ xs.length, ∀ j < i,
      appBaseK c b xs i (c.unit t) ≠ appBaseK c b xs j (c.unit t)) :
    (ops3 c.d).normalFormOK b Xs t = true := by
  have hlen := Snd.forall₂_length h
  have hu := Snd.vrel_unit hc hp ht
  unfold Ops.normalFormOK Ops.distinctOK
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range, Array.size_ofFn] at hi
  rw [List.mem_range] at hj
  have hi' : i < b ^ xs.length := hlen ▸ hi
  rw [Snd.ofFn_getElem! _ hi, Snd.ofFn_getElem! _ (lt_trans hj hi)]
  exact Snd.vne_of_vrel hc hp (Snd.vrel_appBase hc hp b h i hu) (Snd.vrel_appBase hc hp b h j hu)
    (hinj i hi' j hj)

theorem replay_rel {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {LA LB : List Char}
    {V P T : ℕ → ℕ} {N : ℕ} {sA sB : String} {nregs : ℕ} {prog : List Op}
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB)
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hN : N ≤ 1048576) (hprog : prog.all (Op.lt nregs) = true)
    (hrep : (replayK c V P T N prog 0
      ((List.range nregs).map fun x => if x = 0 then 0 else if x = 1 then 1 else 2)).1 = true)
    {r : ℕ} (hr : r < nregs) :
    Snd.LRel c ((ops3 c.d).regsOf sA sB nregs prog)[r]!
      (V ((replayK c V P T N prog 0
        ((List.range nregs).map fun x => if x = 0 then 0 else if x = 1 then 1 else 2)).2.getD
          r 0)) := by
  have hV := vals_of hc hp hN hA hB h1 hs
  set Rk0 : List ℕ := (List.range nregs).map
    (fun x => if x = 0 then 0 else if x = 1 then 1 else 2) with hRk0
  set Rn0 : Array (Array FV) := (ops3 c.d).initRegs ((ops3 c.d).decode sA)
    ((ops3 c.d).decode sB) nregs with hRn0
  have hRk0len : Rk0.length = nregs := by simp [hRk0]
  have hRn0size : Rn0.size = nregs := by simp [hRn0, Ops.initRegs]
  have hcorr0 : Corr c V N Rk0 Rn0 := by
    refine ⟨by rw [hRk0len, hRn0size], fun r hr => ?_⟩
    rw [hRk0len] at hr
    have hRk : Rk0.getD r 0 = if r = 0 then 0 else if r = 1 then 1 else 2 := by
      rw [List.getD_eq_getElem _ _ (by simpa [hRk0] using hr)]
      simp [hRk0]
    have hRn : Rn0[r]! = if r = 0 then (ops3 c.d).decode sA
        else if r = 1 then (ops3 c.d).decode sB else (ops3 c.d).one := by
      rw [getElem!_pos Rn0 r (by omega)]
      simp [hRn0, Ops.initRegs]
    rw [hRk, hRn]
    by_cases h0 : r = 0
    · subst h0
      simp only [if_true]
      refine ⟨Or.inr (by norm_num), wfb_rowsOf c.d sA, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.rowsOf c.d sA) = mat3 c (V 0)
      exact ((spec3 c.d).toMat_decode sA).trans
        (by rw [hsA]; exact (mat3_decode c hc hp hA).2.symm)
    by_cases h01 : r = 1
    · subst h01
      simp only [if_false, if_true, one_ne_zero]
      refine ⟨Or.inr (by norm_num), wfb_rowsOf c.d sB, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.rowsOf c.d sB) = mat3 c (V 1)
      exact ((spec3 c.d).toMat_decode sB).trans
        (by rw [hsB]; exact (mat3_decode c hc hp hB).2.symm)
    · simp only [h0, h01, if_false]
      refine ⟨Or.inr (by norm_num), wfb_idM c.d, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.idM c.d) = mat3 c (V 2)
      rw [CFSG.F3.Native.toMat_idM, hV.two]
  have hprog' : prog.all (Op.lt Rk0.length) = true := by
    rw [hRk0len]
    exact hprog
  have hcorr := replay_corr hV prog 0 Rk0 Rn0 hprog' hcorr0 hrep
  have hlen : (replayK c V P T N prog 0 Rk0).2.length = nregs := by
    rw [replayK_length, hRk0len]
  obtain ⟨hidx, hwf, hmat⟩ := hcorr.2 r (by rw [hlen]; exact hr)
  exact ⟨hV.canon _ hidx, hwf, hmat⟩

theorem squareCheck_main {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {V P T O : Nat → Nat} {N : Nat} {D : SqData} {σ : List Nat}
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : replayOK c V P T N D.asData O (fun _ => D.t) = true)
    (hq : sqOK c V N (O 0) (O 1) (O 2) D.r D.oh D.a D.b D.c D.d D.t σ = true) :
    (ops3 d).squareCheck D = true := by
  subst hd
  unfold replayOK at hr
  simp only [SqData.asData, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨hN, h2⟩, hprog⟩, houts⟩, hrep⟩, hOut⟩, -⟩ := hr
  have hN' : N ≤ 1048576 := of_decide_eq_true hN
  have hlt : ∀ x ∈ [D.rx, D.ry, D.rh], x < D.nregs := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 houts x hx)
  have hO := List.all_eq_true.1 hOut
  have hO0 := Nat.eq_of_beq_eq_true (hO 0 (by simp))
  have hO1 := Nat.eq_of_beq_eq_true (hO 1 (by simp))
  have hO2 := Nat.eq_of_beq_eq_true (hO 2 (by simp))
  have hX := replay_rel hc hp hsA hsB hA hB h1 hs hN' hprog hrep (hlt D.rx (by simp))
  have hY := replay_rel hc hp hsA hsB hA hB h1 hs hN' hprog hrep (hlt D.ry (by simp))
  have hH := replay_rel hc hp hsA hsB hA hB h1 hs hN' hprog hrep (hlt D.rh (by simp))
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hO0 hO1 hO2
  rw [← hO0] at hX
  rw [← hO1] at hY
  rw [← hO2] at hH
  unfold sqOK at hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hr0, hq⟩ := SecS.andT hq
  obtain ⟨hoh0, hq⟩ := SecS.andT hq
  obtain ⟨hXr, hq⟩ := SecS.andT hq
  obtain ⟨hYr, hq⟩ := SecS.andT hq
  obtain ⟨hHo, hq⟩ := SecS.andT hq
  obtain ⟨hXY, hq⟩ := SecS.andT hq
  obtain ⟨hHX, hq⟩ := SecS.andT hq
  obtain ⟨hHY, hnf⟩ := SecS.andT hq
  obtain ⟨ht, hsr⟩ := SecS.andT hnf
  unfold Ops.squareCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨of_decide_eq_true h2, hprog, hlt _ (by simp), hlt _ (by simp), hlt _ (by simp),
    Nat.blt_eq.mp hr0, Nat.blt_eq.mp hoh0,
    Snd.eq_of_rel (rel_lpow hc hp hX D.r) (Snd.rel_one hc hp) hXr,
    Snd.eq_of_rel (rel_lpow hc hp hY D.r) (Snd.rel_one hc hp) hYr,
    Snd.eq_of_rel (rel_lpow hc hp hH D.oh) (Snd.rel_one hc hp) hHo,
    Snd.eq_of_rel (Snd.rel_mul hc hp hX hY) (Snd.rel_mul hc hp hY hX) hXY,
    Snd.conjOK_of hc hp hH hX
      (Snd.rel_mul hc hp (rel_lpow hc hp hX D.a) (rel_lpow hc hp hY D.c)) hHX,
    Snd.conjOK_of hc hp hH hY
      (Snd.rel_mul hc hp (rel_lpow hc hp hX D.b) (rel_lpow hc hp hY D.d)) hHY,
    normalFormOK_of_inj hc hp D.r (.cons hX (.cons hY .nil)) (Nat.blt_eq.mp ht) ?_⟩
  intro i hi j hj heq
  have hi2 : i < Nat.pow D.r 2 := by simpa using hi
  have hij := SecS.sortRun_inj hsr hi2 (lt_trans hj hi2)
    (by simpa only [SecS.digApp_two, appBaseK] using heq)
  omega

end CFSG.KC.LocalComp.SqReplaySnd

end
