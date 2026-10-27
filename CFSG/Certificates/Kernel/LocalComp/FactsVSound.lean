module

public import Certificates.Data.Kernel.LocalComp.FactsV
public import CFSG.Certificates.Kernel.LocalQT.Steps
import all CFSG.Certificates.Kernel.LocalQT.Steps
public import Certificates.Data.CFSGNative.SectionRank.F3
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
import CFSG.Certificates.Kernel.LocalCompOps3Snd.Replay
import CFSG.Certificates.Kernel.OpsKSound
import CFSG.Certificates.Kernel.Spor.OrdCanon
import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3

public section

namespace CFSG.KC.LocalComp.FactsV

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native

open CFSG.KC.LocalComp.Ops3Snd CFSG.KC.LocalComp.Replay CFSG.SectionRank CFSG.KS.Ord CFSG.KC.OpsK

private theorem ksFV_listIs {Rf : Nat → Nat} :
    ∀ (l : List Nat) (i : Nat), listIs Rf l i = true → ∀ q < l.length, l[q]! = Rf (i + q)
  | [], _, _, q, hq => absurd hq (by simp)
  | a :: l, i, h, 0, _ => by
    rw [List.getElem!_cons_zero]
    simp only [listIs, Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1
  | a :: l, i, h, q + 1, hq => by
    simp only [listIs, Bool.and_eq_true] at h
    have := ksFV_listIs l (i + 1) h.2 q (by simpa using hq)
    rw [List.getElem!_cons_succ, this]
    congr 1
    omega

private def ksFV_CorrN (c : Lay) (V : Nat → Nat) (N n : Nat) (R : Nat → Nat)
    (Rn : Array (Array FV)) : Prop :=
  Rn.size = n ∧ ∀ r < n, (R r < N ∨ R r < 3) ∧ WFb c.d Rn[r]! ∧
    CFSG.F3.Native.toMat c.d Rn[r]! = mat3 c (V (R r))

private theorem ksFV_replay_init {c : Lay} (hc : c.ok = true) (hp : c.p = 3)
    {LA LB : List Char} {sA sB : String} (hsA : sA = String.ofList LA)
    (hsB : sB = String.ofList LB) {V P : Nat → Nat} {N n : Nat}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true)
    (hV : Vals c V P N) :
    Corr c V N (initK n) ((ops3 c.d).initRegs ((ops3 c.d).decode sA)
      ((ops3 c.d).decode sB) n) := by
  set Rk0 : List ℕ := initK n with hRk0
  set Rn0 : Array (Array FV) := (ops3 c.d).initRegs ((ops3 c.d).decode sA)
    ((ops3 c.d).decode sB) n with hRn0
  have hRk0len : Rk0.length = n := by simp [hRk0, initK]
  have hRn0size : Rn0.size = n := by simp [hRn0, Ops.initRegs]
  have hcorr0 : Corr c V N Rk0 Rn0 := by
    refine ⟨by rw [hRk0len, hRn0size], fun r hr => ?_⟩
    rw [hRk0len] at hr
    have hRk : Rk0.getD r 0 = if r = 0 then 0 else if r = 1 then 1 else 2 := by
      rw [List.getD_eq_getElem _ _ (by simpa [hRk0, initK] using hr)]
      simp [hRk0, initK]
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
      exact ((spec3b c.d).toMat_decode sA).trans
        (by rw [hsA]; exact (mat3_decode c hc hp hA).2.symm)
    by_cases h01 : r = 1
    · subst h01
      simp only [if_false, if_true, one_ne_zero]
      refine ⟨Or.inr (by norm_num), wfb_rowsOf c.d sB, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.rowsOf c.d sB) = mat3 c (V 1)
      exact ((spec3b c.d).toMat_decode sB).trans
        (by rw [hsB]; exact (mat3_decode c hc hp hB).2.symm)
    · simp only [h0, h01, if_false]
      refine ⟨Or.inr (by norm_num), wfb_idM c.d, ?_⟩
      change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.idM c.d) = mat3 c (V 2)
      rw [CFSG.F3.Native.toMat_idM, hV.two]
  simpa [hRk0, hRn0] using hcorr0

private theorem ksFV_replay {c : Lay} (hc : c.ok = true) (hp : c.p = 3)
    {LA LB : List Char} {sA sB : String} (hsA : sA = String.ofList LA)
    (hsB : sB = String.ofList LB) {V P T Rf : Nat → Nat} {N n : Nat} {prog : List Op}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : regsV c V P T N n prog Rf = true) :
    (∀ r < n, Rf r = (replayK c V P T N prog 0 (initK n)).2.getD r 0) ∧
      ksFV_CorrN c V N n Rf ((ops3 c.d).regsOf sA sB n prog) := by
  unfold regsV at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨hN, h2⟩, hprog⟩, hrep⟩, hlist⟩ := hr
  have hV := vals_of hc hp hN hA hB h1 hs
  set Rk0 : List ℕ := initK n with hRk0
  set Rn0 : Array (Array FV) := (ops3 c.d).initRegs ((ops3 c.d).decode sA)
    ((ops3 c.d).decode sB) n with hRn0
  have hRk0len : Rk0.length = n := by simp [hRk0, initK]
  have hRn0size : Rn0.size = n := by simp [hRn0, Ops.initRegs]
  have hcorr0 : Corr c V N Rk0 Rn0 := by
    simpa [hRk0, hRn0] using ksFV_replay_init hc hp hsA hsB hA hB hV
  have hprog' : prog.all (Op.lt Rk0.length) = true := by rw [hRk0len]; exact hprog
  have hcorr := replay_corr hV prog 0 Rk0 Rn0 hprog' hcorr0 hrep
  have hlen : (replayK c V P T N prog 0 Rk0).2.length = n := by
    rw [replayK_length, hRk0len]
  have hregs : (ops3 c.d).regsOf sA sB n prog =
      prog.foldl (ops3 c.d).step Rn0 := rfl
  rw [hregs]
  have hget : ∀ r < (replayK c V P T N prog 0 Rk0).2.length,
      (replayK c V P T N prog 0 Rk0).2.getD r 0 =
        (replayK c V P T N prog 0 Rk0).2[r]! := by
    intro r hr
    rw [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    rfl
  refine ⟨fun r hr => ?_, ?_⟩
  · have hq : r < (replayK c V P T N prog 0 Rk0).2.length := by rw [hlen]; exact hr
    rw [hget r hq, ksFV_listIs _ 0 hlist r hq]
    simp only [Nat.zero_add]
  · refine ⟨?_, fun r hr => ?_⟩
    · exact (foldl_step_size (ops3 c.d) prog Rn0).trans hRn0size
    have hr' : r < (replayK c V P T N prog 0 Rk0).2.length := by rw [hlen]; exact hr
    obtain ⟨hidx, hwf, hmat⟩ := hcorr.2 r hr'
    have e : (replayK c V P T N prog 0 Rk0).2.getD r 0 = Rf r := by
      rw [hget r hr', ksFV_listIs _ 0 hlist r hr', Nat.zero_add]
    rw [e] at hidx hmat
    exact ⟨hidx, hwf, hmat⟩


private theorem ksFV_evalW_spec {c : Lay} {V P : Nat → Nat} {N : Nat} (_hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    (w : Word) (hw : wordLt n w = true) :
    WFb c.d (evalW (ops3 c.d) Rn w) ∧
      CFSG.F3.Native.toMat c.d (evalW (ops3 c.d) Rn w) =
        (w.map fun p => mat3 c (V (R p.1)) ^ p.2).prod := by
  induction w with
  | nil =>
    refine ⟨wfb_idM c.d, ?_⟩
    rw [List.map_nil, List.prod_nil]
    have hone : CFSG.F3.Native.toMat c.d (ops3 c.d).one = 1 := (spec3b c.d).toMat_one
    simpa [evalW] using hone
  | cons p w ih =>
    obtain ⟨r, e⟩ := p
    simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hr, hw'⟩ := hw
    obtain ⟨hwf, hmat⟩ := ih hw'
    obtain ⟨wp, hp⟩ := OpsSpec.pow_spec (spec3b c.d) (hR.2 r hr).2.1 e
    have hp' : CFSG.F3.Native.toMat c.d ((ops3 c.d).pow Rn[r]! e) =
        CFSG.F3.Native.toMat c.d Rn[r]! ^ e := hp
    refine ⟨(spec3b c.d).mul_wf wp hwf, ?_⟩
    have hmul : CFSG.F3.Native.toMat c.d ((ops3 c.d).mul ((ops3 c.d).pow Rn[r]! e)
        (evalW (ops3 c.d) Rn w)) =
        CFSG.F3.Native.toMat c.d ((ops3 c.d).pow Rn[r]! e) *
          CFSG.F3.Native.toMat c.d (evalW (ops3 c.d) Rn w) :=
      (spec3b c.d).toMat_mul wp hwf
    rw [evalW, hmul, hp', (hR.2 r hr).2.2, hmat, List.map_cons, List.prod_cons]

private theorem ksFV_wordRV_cons {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (_hR : ksFV_CorrN c V N n R Rn)
    {r e r' e' : Nat} {ws : Word} {t : Nat}
    (hw' : wordLt n ((r', e') :: ws) = true)
    (h : wordRV P N R ((r, e) :: (r', e') :: ws) t = true)
    (ih : ∀ (t : Nat), wordLt n ((r', e') :: ws) = true →
      wordRV P N R ((r', e') :: ws) t = true →
        mat3 c (V t) = (((r', e') :: ws).reverse.map fun p =>
          mat3 c (V (R p.1)) ^ p.2).prod) :
    mat3 c (V t) = (((r, e) :: (r', e') :: ws).reverse.map fun p =>
      mat3 c (V (R p.1)) ^ p.2).prod := by
  rw [show wordRV P N R ((r, e) :: (r', e') :: ws) t =
    (decide (3 ≤ t) && decide (t < N) && decide (e < expoFail) &&
      Nat.beq (expoK P (R r) 64 (Nat.shiftRight (P t) 20)) e &&
      wordRV P N R ((r', e') :: ws) (Nat.land (P t) 1048575)) from rfl] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h3, htN⟩, hef⟩, hE⟩, htail⟩ := h
  have hstep : stepOK c V P t = true := by
    have hs : ∀ m, 3 ≤ m → m < N → stepOK c V P m = true := hV.step
    exact hs t h3 htN
  obtain ⟨ha, hb, hVt⟩ := stepOK_spec hstep
  have hcanA : Canon c.p c.d c.w (V (Nat.land (P t) 1048575)) :=
    hV.canon _ (Or.inl (by omega))
  have hcanB : Canon c.p c.d c.w (V (Nat.shiftRight (P t) 20)) :=
    hV.canon _ (Or.inl (by omega))
  have hmul := (mat3_mul c hV.hc hV.hp hcanA hcanB).2
  have hA := ih (Nat.land (P t) 1048575) (by simpa [wordLt] using hw') htail
  have hE' : expoK P (R r) 64 (Nat.shiftRight (P t) 20) = e :=
    Nat.eq_of_beq_eq_true hE
  have hB := expoK_spec hV (R r) 64 (Nat.shiftRight (P t) 20) (Or.inl (by omega))
    (by rw [hE']; exact hef)
  rw [hVt]
  change mat3 c (c.mul (V (Nat.land (P t) 1048575))
    (V (Nat.shiftRight (P t) 20))) = _
  rw [hmul, hA, hB, hE']
  simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]



private theorem ksFV_wordRV_mat {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    (w : Word) (t : Nat) (hw : wordLt n w = true) (h : wordRV P N R w t = true) :
    mat3 c (V t) = (w.reverse.map fun p => mat3 c (V (R p.1)) ^ p.2).prod := by
  revert t hR hw h
  induction w with
  | nil =>
    intro hR t hw h
    rw [show wordRV P N R [] t = Nat.beq t 2 from rfl, Nat.beq_eq] at h
    subst h
    rw [List.reverse_nil, List.map_nil, List.prod_nil]
    exact hV.two
  | cons p w ih =>
    intro hR t hw h
    obtain ⟨r, e⟩ := p
    have hr : r < n := by
      have h := hw
      simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    have hw' : wordLt n w = true := by
      have h := hw
      simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    clear hw
    revert hw'
    rcases w with _ | ⟨q, ws⟩
    · intro hw'
      rw [show wordRV P N R [(r, e)] t =
        (decide (t < N) && decide (e < expoFail) &&
          Nat.beq (expoK P (R r) 64 t) e) from rfl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨htN, hef⟩, hE⟩ := h
      have hE' : expoK P (R r) 64 t = e := Nat.eq_of_beq_eq_true hE
      have hspec := expoK_spec hV (R r) 64 t (Or.inl htN) (by rw [hE']; exact hef)
      rw [List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil]
      simpa [hE'] using hspec
    · intro hw'
      exact ksFV_wordRV_cons hV hR hw' h (ih hR)
private theorem ksFV_wordV_mat {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {w : Word} {t : Nat} (hwl : wordLt n w = true) (hw : wordV P N R w t = true) :
    mat3 c (V t) = (w.map fun p => mat3 c (V (R p.1)) ^ p.2).prod := by
  change wordRV P N R w.reverse t = true at hw
  have h := ksFV_wordRV_mat hV hR w.reverse t (by simpa [wordLt, List.all_reverse] using hwl) hw
  rwa [List.reverse_reverse] at h

private theorem ksFV_word_evalW {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {w : Word} {t : Nat} (hwl : wordLt n w = true) (hw : wordV P N R w t = true) :
    CFSG.F3.Native.toMat c.d (evalW (ops3 c.d) Rn w) = mat3 c (V t) := by
  rw [(ksFV_evalW_spec hV hR w hwl).2, ksFV_wordV_mat hV hR hwl hw]

private theorem ksFV_wordRV_bound {P : Nat → Nat} {N : Nat} {R : Nat → Nat} (w : Word) (t : Nat)
    (h : wordRV P N R w t = true) : t < N ∨ t < 3 := by
  rcases w with _ | ⟨x, w⟩
  · rw [show wordRV P N R [] t = Nat.beq t 2 from rfl, Nat.beq_eq] at h
    subst h
    exact Or.inr (by norm_num)
  · rcases w with _ | ⟨y, ws⟩
    · obtain ⟨r, e⟩ := x
      rw [show wordRV P N R [(r, e)] t =
        (decide (t < N) && decide (e < expoFail) &&
          Nat.beq (expoK P (R r) 64 t) e) from rfl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inl h.1.1
    · obtain ⟨r, e⟩ := x
      obtain ⟨r', e'⟩ := y
      rw [show wordRV P N R ((r, e) :: (r', e') :: ws) t =
        (decide (3 ≤ t) && decide (t < N) && decide (e < expoFail) &&
          Nat.beq (expoK P (R r) 64 (Nat.shiftRight (P t) 20)) e &&
          wordRV P N R ((r', e') :: ws) (Nat.land (P t) 1048575)) from rfl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inl h.1.1.1.2

private theorem ksFV_wordV_bound {P : Nat → Nat} {N : Nat} {R : Nat → Nat} {w : Word} {t : Nat}
    (h : wordV P N R w t = true) : t < N ∨ t < 3 := by
  change wordRV P N R w.reverse t = true at h
  exact ksFV_wordRV_bound w.reverse t h



private theorem ksFV_andB {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KC.Ord.andB]

private theorem ksFV_consts {c : Lay} (hc : c.ok = true) :
    c.S = c.d * c.w ∧ c.RM = 2 ^ c.S - 1 := by
  unfold Lay.ok CFSG.KC.Ord.constsOK at hc
  obtain ⟨-, hc⟩ := ksFV_andB hc
  obtain ⟨hS, hc⟩ := ksFV_andB hc
  obtain ⟨-, hc⟩ := ksFV_andB hc
  obtain ⟨-, hc⟩ := ksFV_andB hc
  obtain ⟨-, hc⟩ := ksFV_andB hc
  obtain ⟨-, hc⟩ := ksFV_andB hc
  obtain ⟨-, hc⟩ := ksFV_andB hc
  obtain ⟨-, hc⟩ := ksFV_andB hc
  obtain ⟨hRM, -⟩ := ksFV_andB hc
  have hRM' : c.RM = 2 ^ c.S - 1 := by
    have h := hRM
    have hpow : Nat.shiftLeft 1 c.S = 2 ^ c.S := Nat.one_shiftLeft c.S
    rw [hpow] at h
    exact Nat.eq_of_beq_eq_true h
  exact ⟨Nat.eq_of_beq_eq_true hS, hRM'⟩


private theorem ksFV_mod_div {a B k w : Nat} (h : k + w ≤ B) :
    (a % 2 ^ B) / 2 ^ k % 2 ^ w = a / 2 ^ k % 2 ^ w := by
  have hk : k ≤ B := by omega
  conv_rhs =>
    rw [show a = a % 2 ^ B + 2 ^ B * (a / 2 ^ B) from
      (Nat.mod_add_div a (2 ^ B)).symm]
  rw [show 2 ^ B * (a / 2 ^ B) = 2 ^ k * (2 ^ (B - k) * (a / 2 ^ B)) by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hk]]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
  rw [show 2 ^ (B - k) = 2 ^ w * 2 ^ (B - k - w) by
    rw [← Nat.pow_add]
    congr 1
    omega]
  rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]

private theorem ksFV_rowV_lane {c : Lay} (hc : c.ok = true) {X t j : Nat} (hj : j < c.d) :
    rowV c X t / 2 ^ (c.w * j) % 2 ^ c.w =
      X / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w := by
  obtain ⟨hS, hRM⟩ := ksFV_consts hc
  have hmod : Nat.land (Nat.shiftRight X (Nat.mul c.S t)) c.RM =
      Nat.shiftRight X (Nat.mul c.S t) % 2 ^ c.S := by
    rw [hRM]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  unfold rowV
  rw [hmod, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  change X / 2 ^ (c.S * t) % 2 ^ c.S / 2 ^ (c.w * j) % 2 ^ c.w =
    X / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w
  rw [ksFV_mod_div (a := X / 2 ^ (c.S * t)) (B := c.S) (k := c.w * j) (w := c.w) ?_]
  · rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  · rw [hS]
    nlinarith [hj]

private theorem ksFV_rowV_lt {c : Lay} (hc : c.ok = true) (X t : Nat) :
    rowV c X t < 2 ^ (c.w * c.d) := by
  obtain ⟨hS, hRM⟩ := ksFV_consts hc
  have hlt := Nat.and_lt_two_pow (Nat.shiftRight X (Nat.mul c.S t))
    (Nat.sub_one_lt (Nat.two_pow_pos c.S).ne')
  unfold rowV
  rw [hRM]
  rw [hS] at hlt ⊢
  simpa [Nat.mul_comm c.d c.w] using hlt

private theorem ksFV_rowV_eq_of_lane {c : Lay} (hc : c.ok = true) {X Y t : Nat}
    (h : ∀ j < c.d, rowV c X t / 2 ^ (c.w * j) % 2 ^ c.w =
      rowV c Y t / 2 ^ (c.w * j) % 2 ^ c.w) :
    rowV c X t = rowV c Y t := by
  have hw : 0 < c.w := (cfacts hc).2.2.1
  have h' := (fields_eq_iff hw c.d (rowV c X t) (rowV c Y t)).1 h
  rwa [Nat.mod_eq_of_lt (ksFV_rowV_lt hc X t),
    Nat.mod_eq_of_lt (ksFV_rowV_lt hc Y t)] at h'

private theorem ksFV_rowV_eq_of_toVec {c : Lay} (hc : c.ok = true) (hp : c.p = 3)
    {X Y : Nat} (hX : Canon c.p c.d c.w X) (hY : Canon c.p c.d c.w Y) {t : Nat}
    (ht : t < c.d)
    (h : (fun j : Fin c.d => mat3 c X ⟨t, ht⟩ j) =
      fun j : Fin c.d => mat3 c Y ⟨t, ht⟩ j) :
    rowV c X t = rowV c Y t := by
  obtain ⟨hS, -⟩ := ksFV_consts hc
  refine ksFV_rowV_eq_of_lane hc fun j hj => ?_
  have he := congrFun h ⟨j, hj⟩
  unfold mat3 at he
  rw [ordMat_apply, ordMat_apply] at he
  have hidx : c.d * t + j < c.d * c.d := by nlinarith
  have hxl : X / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w < c.p := by
    have hl := hX.2 (c.d * t + j) hidx
    unfold lane at hl
    rwa [show c.w * (c.d * t + j) = c.S * t + c.w * j by rw [hS]; ring] at hl
  have hyl : Y / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w < c.p := by
    have hl := hY.2 (c.d * t + j) hidx
    unfold lane at hl
    rwa [show c.w * (c.d * t + j) = c.S * t + c.w * j by rw [hS]; ring] at hl
  have hxl' : X / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w < 3 := by
    simpa [hp] using hxl
  have hyl' : Y / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w < 3 := by
    simpa [hp] using hyl
  have he' : ((X / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w : Nat) : ZMod 3) =
      ((Y / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w : Nat) : ZMod 3) := by simpa using he
  have e := eq_of_cast hxl' hyl' he'
  rw [ksFV_rowV_lane hc (X := X) (t := t) (j := j) hj,
    ksFV_rowV_lane hc (X := Y) (t := t) (j := j) hj]
  exact e

private theorem ksFV_toVec_vmul_unit {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {w : Word} {u t : Nat} (ht : t < c.d) (hwl : wordLt n w = true)
    (hword : wordV P N R w u = true) :
    (spec3b c.d).toVec ((ops3 c.d).vmul ((ops3 c.d).unit t) (evalW (ops3 c.d) Rn w)) =
      fun j : Fin c.d => mat3 c (V u) ⟨t, ht⟩ j := by
  obtain ⟨hwf, -⟩ := ksFV_evalW_spec hV hR w hwl
  have hmat' := ksFV_word_evalW hV hR hwl hword
  funext j
  rw [(spec3b c.d).toVec_vmul (by simp [spec3b, ops3, CFSG.F3.Native.V.wf]) hwf,
    toVec_unit c.d t, ← hmat']
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [if_pos rfl, one_mul]
    rfl
  · intro b _ hb
    have hb' : (b : Nat) ≠ t := fun h => hb (Fin.ext h)
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem ksFV_factOK_V3_ord {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {h r e : Nat} (hf : factV c V P N R n h (MFact.ord r e) = true) :
    factOK (ops3 c.d) Rn n (MFact.ord r e) = true := by
  simp only [factV, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hrest, hVone⟩ := hf
  obtain ⟨⟨hr, he⟩, hword⟩ := hrest
  have hwl : wordLt n [(r, e)] = true := by
    simpa [wordLt] using decide_eq_true hr
  have hword' : mat3 c (V (fld h 0)) = mat3 c (V (R r)) ^ e := by
    simpa [List.map_cons, List.prod_cons] using ksFV_wordV_mat hV hR hwl hword
  have hVone' : V (fld h 0) = c.ONE := Nat.eq_of_beq_eq_true hVone
  obtain ⟨wp, hp⟩ := OpsSpec.pow_spec (spec3b c.d) (hR.2 r hr).2.1 e
  have hp' : CFSG.F3.Native.toMat c.d ((ops3 c.d).pow Rn[r]! e) =
      CFSG.F3.Native.toMat c.d Rn[r]! ^ e := hp
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hr, he⟩, ?_⟩
  refine eqM_of_toMat_eq wp (wfb_idM c.d) ?_
  rw [hp', (hR.2 r hr).2.2, ← hword', hVone', (mat3_one c hV.hc hV.hp).2]
  have hone : CFSG.F3.Native.toMat c.d (ops3 c.d).one = 1 := (spec3b c.d).toMat_one
  rw [hone]

private theorem ksFV_factOK_V3_conj {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {h : Nat} {g : Nat} {u w : Word} (hf : factV c V P N R n h (MFact.conj g u w) = true) :
    factOK (ops3 c.d) Rn n (MFact.conj g u w) = true := by
  simp only [factV, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hrest, hVeq⟩ := hf
  obtain ⟨⟨⟨⟨hg, hwu⟩, hww⟩, hvu⟩, hvw⟩ := hrest
  have hgu : wordLt n ((g, 1) :: u) = true := by
    simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hg, hwu⟩
  have hgw : wordLt n (w ++ [(g, 1)]) = true := by
    simp only [wordLt, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hww, hg⟩
  have hvu' : mat3 c (V (fld h 0)) = mat3 c (V (R g)) * (u.map fun p =>
      mat3 c (V (R p.1)) ^ p.2).prod := by
    simpa [List.map_cons, List.prod_cons] using ksFV_wordV_mat hV hR hgu hvu
  have hvw' : mat3 c (V (fld h 1)) = (w.map fun p =>
      mat3 c (V (R p.1)) ^ p.2).prod * mat3 c (V (R g)) := by
    simpa [List.map_append, List.map_cons, List.prod_append, List.prod_cons] using
      ksFV_wordV_mat hV hR hgw hvw
  have hVeq' : V (fld h 0) = V (fld h 1) := Nat.eq_of_beq_eq_true hVeq
  obtain ⟨huwf, humat⟩ := ksFV_evalW_spec hV hR u hwu
  obtain ⟨hwwf, hwmat⟩ := ksFV_evalW_spec hV hR w hww
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]; refine ⟨⟨⟨hg, hwu⟩, hww⟩, ?_⟩
  have hmul1 : CFSG.F3.Native.toMat c.d ((ops3 c.d).mul Rn[g]! (evalW (ops3 c.d) Rn u)) =
      CFSG.F3.Native.toMat c.d Rn[g]! * CFSG.F3.Native.toMat c.d (evalW (ops3 c.d) Rn u) :=
    (spec3b c.d).toMat_mul (hR.2 g hg).2.1 huwf
  have hmul2 : CFSG.F3.Native.toMat c.d ((ops3 c.d).mul (evalW (ops3 c.d) Rn w) Rn[g]!) =
      CFSG.F3.Native.toMat c.d (evalW (ops3 c.d) Rn w) * CFSG.F3.Native.toMat c.d Rn[g]! :=
    (spec3b c.d).toMat_mul hwwf (hR.2 g hg).2.1
  refine eqM_of_toMat_eq ((spec3b c.d).mul_wf (hR.2 g hg).2.1 huwf)
    ((spec3b c.d).mul_wf hwwf (hR.2 g hg).2.1) ?_
  rw [hmul1, hmul2, (hR.2 g hg).2.2, humat, hwmat, ← hvu', ← hvw', hVeq']

private theorem ksFV_factOK_V3_ne {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {h : Nat} {w1 w2 : Word} {t : Nat} (hf : factV c V P N R n h (MFact.ne w1 w2 t) = true) :
    factOK (ops3 c.d) Rn n (MFact.ne w1 w2 t) = true := by
  simp only [factV, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hrest, hne⟩ := hf
  obtain ⟨⟨⟨⟨hw1, hw2⟩, ht⟩, hword1⟩, hword2⟩ := hrest
  have ht' : t < c.d := ht
  have hrowne : rowV c (V (fld h 0)) t ≠ rowV c (V (fld h 1)) t := by
    have hb : Nat.beq (rowV c (V (fld h 0)) t) (rowV c (V (fld h 1)) t) = false := by
      have := hne
      rwa [Bool.not_eq_true'] at this
    exact Nat.ne_of_beq_eq_false hb
  have hb0 := ksFV_wordV_bound (P := P) (N := N) (R := R) hword1
  have hb1 := ksFV_wordV_bound (P := P) (N := N) (R := R) hword2
  have hcan0 := hV.canon _ hb0
  have hcan1 := hV.canon _ hb1
  simp only [factOK, Bool.and_eq_true]
  refine ⟨⟨hw1, hw2⟩, ?_⟩
  apply vne_of_toVec_ne
  intro heq
  have hv1 := ksFV_toVec_vmul_unit hV hR ht' hw1 hword1
  have hv2 := ksFV_toVec_vmul_unit hV hR ht' hw2 hword2
  rw [hv1, hv2] at heq
  exact hrowne (ksFV_rowV_eq_of_toVec hV.hc hV.hp hcan0 hcan1 ht' heq)

private theorem ksFV_factOK_V3_eq {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {h : Nat} {w1 w2 : Word} (hf : factV c V P N R n h (MFact.eq w1 w2) = true) :
    factOK (ops3 c.d) Rn n (MFact.eq w1 w2) = true := by
  simp only [factV, Bool.and_eq_true] at hf
  obtain ⟨hrest, hVeq⟩ := hf
  obtain ⟨⟨⟨hw1, hw2⟩, hword1⟩, hword2⟩ := hrest
  have hVeq' : V (fld h 0) = V (fld h 1) := Nat.eq_of_beq_eq_true hVeq
  have hword1' : mat3 c (V (fld h 0)) = (w1.map fun p =>
      mat3 c (V (R p.1)) ^ p.2).prod := ksFV_wordV_mat hV hR hw1 hword1
  have hword2' : mat3 c (V (fld h 1)) = (w2.map fun p =>
      mat3 c (V (R p.1)) ^ p.2).prod := ksFV_wordV_mat hV hR hw2 hword2
  obtain ⟨hw1f, hmat1⟩ := ksFV_evalW_spec hV hR w1 hw1
  obtain ⟨hw2f, hmat2⟩ := ksFV_evalW_spec hV hR w2 hw2
  simp only [factOK, Bool.and_eq_true]
  refine ⟨⟨hw1, hw2⟩, ?_⟩
  refine eqM_of_toMat_eq hw1f hw2f ?_
  rw [hmat1, hmat2, ← hword1', ← hword2', hVeq']

private theorem ksFV_factOK_V3 {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {n : Nat} {R : Nat → Nat} {Rn : Array (Array FV)} (hR : ksFV_CorrN c V N n R Rn)
    {h : Nat} {f : MFact} (hf : factV c V P N R n h f = true) :
    factOK (ops3 c.d) Rn n f = true := by
  cases f with
  | ord r e => exact ksFV_factOK_V3_ord hV hR hf
  | conj g u w => exact ksFV_factOK_V3_conj hV hR hf
  | ne w1 w2 t => exact ksFV_factOK_V3_ne hV hR hf
  | eq w1 w2 => exact ksFV_factOK_V3_eq hV hR hf

theorem factOK_of_V3 {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {sA sB : String} (hsA : sA = String.ofList LA)
    (hsB : sB = String.ofList LB) {V P T Rf : Nat → Nat} {N n : Nat} {prog : List Op}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : regsV c V P T N n prog Rf = true) (h : Nat)
    (f : MFact) (hf : factV c V P N Rf n h f = true) :
    factOK (ops3 d) ((ops3 d).regsOf sA sB n prog) n f = true := by
  subst hd
  have hN : N ≤ 1048576 := by
    have h := hr
    unfold regsV at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1
  have hV := vals_of hc hp hN hA hB h1 hs
  obtain ⟨-, hcorr⟩ := ksFV_replay hc hp hsA hsB hA hB h1 hs hr
  exact ksFV_factOK_V3 hV hcorr hf

theorem seed_of_V3 {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {sA sB : String} (hsA : sA = String.ofList LA)
    (hsB : sB = String.ofList LB) {V P T Rf : Nat → Nat} {N n : Nat} {prog : List Op}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : regsV c V P T N n prog Rf = true) {r : Nat}
    (hrn : r < n) :
    (Rf r = 0 → (ops3 d).eq ((ops3 d).regsOf sA sB n prog)[r]! ((ops3 d).decode sA) = true) ∧
      (Rf r = 1 → (ops3 d).eq ((ops3 d).regsOf sA sB n prog)[r]! ((ops3 d).decode sB) = true) := by
  subst hd
  obtain ⟨-, hcorr⟩ := ksFV_replay hc hp hsA hsB hA hB h1 hs hr
  obtain ⟨-, hwf, hmat⟩ := hcorr.2 r hrn
  have hdecA : CFSG.F3.Native.toMat c.d ((ops3 c.d).decode sA) = mat3 c (V 0) := by
    change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.rowsOf c.d sA) = mat3 c (V 0)
    exact ((spec3b c.d).toMat_decode sA).trans
      (by rw [hsA]; exact (mat3_decode c hc hp hA).2.symm)
  have hdecB : CFSG.F3.Native.toMat c.d ((ops3 c.d).decode sB) = mat3 c (V 1) := by
    change CFSG.F3.Native.toMat c.d (CFSG.F3.Native.rowsOf c.d sB) = mat3 c (V 1)
    exact ((spec3b c.d).toMat_decode sB).trans
      (by rw [hsB]; exact (mat3_decode c hc hp hB).2.symm)
  refine ⟨fun h0 => ?_, fun h1r => ?_⟩
  · refine eqM_of_toMat_eq hwf (wfb_rowsOf c.d sA) ?_
    rw [hmat, h0, hdecA]
  · refine eqM_of_toMat_eq hwf (wfb_rowsOf c.d sB) ?_
    rw [hmat, h1r, hdecB]


private def ksFV_ArrCanon (p d : Nat) (X : Array (Array Nat)) : Prop :=
  X.size = d ∧ ∀ i < d, (X[i]!).size = d ∧ ∀ j < d, (X[i]!)[j]! < p

private theorem ksFV_canon_rowsOf {p d : Nat} (hp : 0 < p) (s : String) :
    ksFV_ArrCanon p d (CFSG.Sporadic.He.Native.rowsOf p d s) := by
  refine ⟨by simp [CFSG.Sporadic.He.Native.rowsOf], fun i hi => ?_⟩
  unfold CFSG.Sporadic.He.Native.rowsOf
  rw [CFSG.Sporadic.He.Native.getElem!_ofFn _ hi]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [CFSG.Sporadic.He.Native.getElem!_ofFn _ hj]
  exact Nat.mod_lt _ hp

private theorem ksFV_canon_idM {p d : Nat} (hp : 1 < p) :
    ksFV_ArrCanon p d (CFSG.Sporadic.He.Native.idM d) := by
  refine ⟨by simp [CFSG.Sporadic.He.Native.idM], fun i hi => ?_⟩
  unfold CFSG.Sporadic.He.Native.idM
  rw [CFSG.Sporadic.He.Native.getElem!_ofFn _ hi]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [CFSG.Sporadic.He.Native.getElem!_ofFn _ hj]
  split <;> omega

private theorem ksFV_canon_mulM {p d : Nat} (hp : 0 < p) {X Y : Array (Array Nat)}
    (_hX : X.size = d) (_hY : ∀ i < d, (Y[i]!).size = d) :
    ksFV_ArrCanon p d (CFSG.Sporadic.He.Native.mulM p d X Y) := by
  refine ⟨by simp [CFSG.Sporadic.He.Native.mulM], fun i hi => ?_⟩
  unfold CFSG.Sporadic.He.Native.mulM
  rw [CFSG.Sporadic.He.Native.getElem!_ofFn _ hi]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [CFSG.Sporadic.He.Native.getElem!_ofFn _ hj]
  exact Nat.mod_lt _ hp

private theorem ksFV_canon_pow {p d : Nat} (hp : 1 < p) {X : Array (Array Nat)}
    (hX : ksFV_ArrCanon p d X) (e : Nat) :
    ksFV_ArrCanon p d ((opsP p d).pow X e) := by
  have hp0 : 0 < p := by omega
  induction e using Nat.strong_induction_on generalizing X with
  | _ e ih =>
    unfold Ops.pow
    by_cases h0 : e = 0
    · rw [if_pos h0]
      exact ksFV_canon_idM hp
    by_cases h1 : e = 1
    · rw [if_neg h0, if_pos h1]
      exact hX
    rw [if_neg h0, if_neg h1]
    have hXX := ksFV_canon_mulM hp0 hX.1 fun i _ => (hX.2 i (by omega)).1
    have hpow := ih (e / 2) (by omega) hXX
    by_cases ho : e % 2 = 1
    · rw [if_pos ho]
      exact ksFV_canon_mulM hp0 hX.1 fun i _ => (hpow.2 i (by omega)).1
    · rw [if_neg ho]
      exact hpow

private theorem ksFV_toMat_unpackL {p d w S X : Nat} (i j : Fin d) :
    CFSG.Sporadic.He.Native.toMat p d (unpackL d w S X) i j = ordMat p d w S X i j := by
  rw [CFSG.Sporadic.He.Native.toMat_apply, ordMat_apply, unpackL_get i.isLt j.isLt]

private theorem ksFV_toMat_unpackL_eq {p d w S X : Nat} :
    CFSG.Sporadic.He.Native.toMat p d (unpackL d w S X) = ordMat p d w S X := by
  ext i j
  exact ksFV_toMat_unpackL i j

private theorem ksFV_eq_of_toMat_eq {p d : Nat} {X Y : Array (Array Nat)}
    (hX : ksFV_ArrCanon p d X) (hY : ksFV_ArrCanon p d Y)
    (h : CFSG.Sporadic.He.Native.toMat p d X = CFSG.Sporadic.He.Native.toMat p d Y) : X = Y := by
  apply Array.ext
  · rw [hX.1, hY.1]
  · intro i hi hi'
    have hid : i < d := by rwa [hX.1] at hi
    have hXi : i < X.size := hi
    have hYi : i < Y.size := by rwa [hY.1]
    have hszX : (X[i]!).size = d := (hX.2 i hid).1
    have hszY : (Y[i]!).size = d := (hY.2 i hid).1
    have hXi' : (X[i]).size = d := by rw [← getElem!_pos X i hXi]; exact hszX
    have hYi' : (Y[i]).size = d := by rw [← getElem!_pos Y i hYi]; exact hszY
    apply Array.ext
    · rw [hXi', hYi']
    · intro j hj hj'
      have hjd : j < d := by rw [← hXi']; exact hj
      have hXj : j < (X[i]).size := hj
      have hYj : j < (Y[i]).size := by rwa [hYi']
      have e := congrFun (congrFun h ⟨i, hid⟩) ⟨j, hjd⟩
      rw [CFSG.Sporadic.He.Native.toMat_apply, CFSG.Sporadic.He.Native.toMat_apply] at e
      rw [getElem!_pos X i hXi, getElem!_pos Y i hYi,
        getElem!_pos (X[i]) j hXj, getElem!_pos (Y[i]) j hYj] at e
      have hbX : X[i][j] < p := by
        rw [← getElem!_pos (X[i]) j hXj, ← getElem!_pos X i hXi]
        exact (hX.2 i hid).2 j hjd
      have hbY : Y[i][j] < p := by
        rw [← getElem!_pos (Y[i]) j hYj, ← getElem!_pos Y i hYi]
        exact (hY.2 i hid).2 j hjd
      exact eq_of_cast hbX hbY e

private theorem ksFV_unpackL_inj {c : Lay} {p X Y : Nat} (hc : c.ok = true)
    (hX : Canon p c.d c.w X) (hY : Canon p c.d c.w Y)
    (h : CFSG.Sporadic.He.Native.toMat p c.d (unpackL c.d c.w c.S X) =
      CFSG.Sporadic.He.Native.toMat p c.d (unpackL c.d c.w c.S Y)) : X = Y := by
  obtain ⟨-, hS, -, -⟩ := cfacts hc
  apply canon_ext hX hY
  intro i hi j hj
  have e := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  rw [ksFV_toMat_unpackL, ksFV_toMat_unpackL, hS] at e
  rw [ordMat_apply, ordMat_apply] at e
  exact eq_of_cast (canon_ent hX hi hj) (canon_ent hY hi hj) e

private structure ksFV_PVals (c : Lay) (V P : Nat → Nat) (N : Nat) : Prop where
  hc : c.ok = true
  hN : N ≤ 1048576
  valid : ∀ n, (n < N ∨ n < 3) → validM c.p (c.d * c.S) c.L c.H (V n) = true
  step : StepsTo (stepOK c V P) N
  two : V 2 = c.ONE

private theorem ksFV_pvalid_lt {c : Lay} {V P : Nat → Nat} {N : Nat} (hc : c.ok = true)
    (hs : StepsTo (stepOK c V P) N)
    (h0 : validM c.p (c.d * c.S) c.L c.H (V 0) = true)
    (h1 : validM c.p (c.d * c.S) c.L c.H (V 1) = true) (h2 : V 2 = c.ONE) :
    ∀ n, n < N → validM c.p (c.d * c.S) c.L c.H (V n) = true := by
  have h2v : validM c.p (c.d * c.S) c.L c.H c.ONE = true :=
    CFSG.KS.OrdCanon.validM_of_canon hc (one_sound hc).1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnN
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · exact h0
      · exact h1
      · rw [h2]; exact h2v
    · have hstep : stepOK c V P n = true := hs n (by omega) hnN
      obtain ⟨ha, hb, hVn⟩ := stepOK_spec hstep
      have hva : validM c.p (c.d * c.S) c.L c.H (V (Nat.land (P n) 1048575)) = true :=
        ih (Nat.land (P n) 1048575) (by omega) (by omega)
      have hvb : validM c.p (c.d * c.S) c.L c.H (V (Nat.shiftRight (P n) 20)) = true :=
        ih (Nat.shiftRight (P n) 20) (by omega) (by omega)
      have hm := (mulR_eqL hc hva hvb).2
      rw [hVn]
      change validM c.p (c.d * c.S) c.L c.H
        (mulR c.p c.w c.S c.d c.T c.L c.H c.CM c.RM
          (V (Nat.land (P n) 1048575)) (V (Nat.shiftRight (P n) 20))) = true
      exact hm

private theorem ksFV_pvalid {c : Lay} {V P : Nat → Nat} {N : Nat} (hc : c.ok = true)
    (_hN : N ≤ 1048576) (hs : StepsTo (stepOK c V P) N)
    (h0 : validM c.p (c.d * c.S) c.L c.H (V 0) = true)
    (h1 : validM c.p (c.d * c.S) c.L c.H (V 1) = true) (h2 : V 2 = c.ONE) :
    ∀ n, (n < N ∨ n < 3) → validM c.p (c.d * c.S) c.L c.H (V n) = true := by
  have h2v : validM c.p (c.d * c.S) c.L c.H c.ONE = true :=
    CFSG.KS.OrdCanon.validM_of_canon hc (one_sound hc).1
  intro n hn
  rcases hn with hnN | hn3
  · exact ksFV_pvalid_lt hc hs h0 h1 h2 n hnN
  · interval_cases n
    · exact h0
    · exact h1
    · rw [h2]; exact h2v

private theorem ksFV_pvals {c : Lay} {V P : Nat → Nat} {N : Nat} (hc : c.ok = true)
    (hN : N ≤ 1048576) (hs : StepsTo (stepOK c V P) N)
    (h0 : validM c.p (c.d * c.S) c.L c.H (V 0) = true)
    (h1 : validM c.p (c.d * c.S) c.L c.H (V 1) = true) (h2 : V 2 = c.ONE) :
    ksFV_PVals c V P N :=
  ⟨hc, hN, ksFV_pvalid hc hN hs h0 h1 h2, hs, h2⟩


private theorem ksFV_pexpoK_mat {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) (a : Nat) :
    ∀ (f t : Nat), (t < N ∨ t ≤ 2) → expoK P a f t < expoFail →
      ordMat c.p c.d c.w c.S (V t) =
        ordMat c.p c.d c.w c.S (V a) ^ expoK P a f t := by
  intro f
  induction f with
  | zero =>
    intro t _ h
    rw [expoK] at h
    exact absurd h (lt_irrefl _)
  | succ f ih =>
    intro t ht h
    rw [expoK] at h ⊢
    by_cases h1 : t = a
    · rw [if_pos h1] at h ⊢
      rw [h1, pow_one]
    · rw [if_neg h1] at h ⊢
      by_cases h2 : t = 2
      · rw [if_pos h2] at h ⊢
        rw [h2, hV.two, (one_sound hV.hc).2, pow_zero]
      · rw [if_neg h2] at h ⊢
        by_cases h3 : t < 2
        · rw [if_pos h3] at h
          exact absurd h (lt_irrefl _)
        · rw [if_neg h3] at h ⊢
          have ht3 : 3 ≤ t := by omega
          have htN : t < N := by rcases ht with h' | h' <;> omega
          have hstep : stepOK c V P t = true := hV.step t ht3 htN
          obtain ⟨ha, hb, hVt⟩ := stepOK_spec hstep
          have hca : Canon c.p c.d c.w (V (Nat.land (P t) 1048575)) :=
            validM_canon hV.hc (hV.valid _ (Or.inl (by omega)))
          have hcb : Canon c.p c.d c.w (V (Nat.shiftRight (P t) 20)) :=
            validM_canon hV.hc (hV.valid _ (Or.inl (by omega)))
          have hmul := (mulR_sound hV.hc hca hcb).2
          have ihA := ih (Nat.land (P t) 1048575) (Or.inl (by omega)) (by omega)
          have ihB := ih (Nat.shiftRight (P t) 20) (Or.inl (by omega)) (by omega)
          rw [hVt]
          change ordMat c.p c.d c.w c.S
            (mulR c.p c.w c.S c.d c.T c.L c.H c.CM c.RM
              (V (Nat.land (P t) 1048575)) (V (Nat.shiftRight (P t) 20))) = _
          rw [hmul, ihA, ihB, ← pow_add]

private def ksFV_PCorr (c : Lay) (V : Nat → Nat) (N n : Nat) (R : Nat → Nat)
    (Rn : Array (Array (Array Nat))) : Prop :=
  Rn.size = n ∧ ∀ r < n, (R r < N ∨ R r < 3) ∧
    validM c.p (c.d * c.S) c.L c.H (V (R r)) = true ∧
    ksFV_ArrCanon c.p c.d (Rn[r]!) ∧
    CFSG.Sporadic.He.Native.toMat c.p c.d (Rn[r]!) = ordMat c.p c.d c.w c.S (V (R r))

private theorem ksFV_pevalW_spec {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat} {Rn : Array (Array (Array Nat))}
    (hR : ksFV_PCorr c V N n R Rn) (w : Word) (hw : wordLt n w = true) :
    ksFV_ArrCanon c.p c.d (evalW (opsP c.p c.d) Rn w) ∧
      CFSG.Sporadic.He.Native.toMat c.p c.d (evalW (opsP c.p c.d) Rn w) =
        (w.map fun p => ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod := by
  have hp2 : 1 < c.p := (cfacts hV.hc).1
  induction w with
  | nil =>
    refine ⟨ksFV_canon_idM hp2, ?_⟩
    rw [List.map_nil, List.prod_nil, evalW]
    change CFSG.Sporadic.He.Native.toMat c.p c.d
      (CFSG.Sporadic.He.Native.idM c.d) = 1
    rw [CFSG.Sporadic.He.Native.toMat_idM]
  | cons p w ih =>
    obtain ⟨r, e⟩ := p
    simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hr, hw'⟩ := hw
    obtain ⟨hwf, hmat⟩ := ih hw'
    have hrw := hR.2 r hr
    have hpowcan := ksFV_canon_pow hp2 hrw.2.2.1 e
    have hmulcan := ksFV_canon_mulM (p := c.p) (d := c.d) (by omega) hpowcan.1
      (fun i _ => (hwf.2 i (by omega)).1)
    refine ⟨hmulcan, ?_⟩
    have hpowmat := OpsSpec.pow_spec (specP c.p c.d) (X := Rn[r]!) trivial e
    have hpowmat' : CFSG.Sporadic.He.Native.toMat c.p c.d ((opsP c.p c.d).pow Rn[r]! e) =
        CFSG.Sporadic.He.Native.toMat c.p c.d Rn[r]! ^ e := hpowmat.2
    have hmulmat := CFSG.Sporadic.He.Native.toMat_mulM c.p c.d
      ((opsP c.p c.d).pow Rn[r]! e) (evalW (opsP c.p c.d) Rn w)
    change CFSG.Sporadic.He.Native.toMat c.p c.d
      (CFSG.Sporadic.He.Native.mulM c.p c.d ((opsP c.p c.d).pow Rn[r]! e)
        (evalW (opsP c.p c.d) Rn w)) = _
    rw [hmulmat, hpowmat', hrw.2.2.2, hmat, List.map_cons, List.prod_cons]


private theorem ksFV_pwordRV_cons {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat}
    {Rn : Array (Array (Array Nat))} (_hR : ksFV_PCorr c V N n R Rn)
    {r e r' e' : Nat} {ws : Word} {t : Nat}
    (hw' : wordLt n ((r', e') :: ws) = true)
    (h : wordRV P N R ((r, e) :: (r', e') :: ws) t = true)
    (ih : ∀ (t : Nat), wordLt n ((r', e') :: ws) = true →
      wordRV P N R ((r', e') :: ws) t = true →
        ordMat c.p c.d c.w c.S (V t) = (((r', e') :: ws).reverse.map fun p =>
          ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod) :
    ordMat c.p c.d c.w c.S (V t) = (((r, e) :: (r', e') :: ws).reverse.map fun p =>
      ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod := by
  rw [show wordRV P N R ((r, e) :: (r', e') :: ws) t =
    (decide (3 ≤ t) && decide (t < N) && decide (e < expoFail) &&
      Nat.beq (expoK P (R r) 64 (Nat.shiftRight (P t) 20)) e &&
      wordRV P N R ((r', e') :: ws) (Nat.land (P t) 1048575)) from rfl] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h3, htN⟩, hef⟩, hE⟩, htail⟩ := h
  have hstep : stepOK c V P t = true := by
    have hs : ∀ m, 3 ≤ m → m < N → stepOK c V P m = true := hV.step
    exact hs t h3 htN
  obtain ⟨ha, hb, hVt⟩ := stepOK_spec hstep
  have hca : Canon c.p c.d c.w (V (Nat.land (P t) 1048575)) :=
    validM_canon hV.hc (hV.valid _ (Or.inl (by omega)))
  have hcb : Canon c.p c.d c.w (V (Nat.shiftRight (P t) 20)) :=
    validM_canon hV.hc (hV.valid _ (Or.inl (by omega)))
  have hmul := (mulR_sound hV.hc hca hcb).2
  have hA := ih (Nat.land (P t) 1048575) (by simpa [wordLt] using hw') htail
  have hE' : expoK P (R r) 64 (Nat.shiftRight (P t) 20) = e :=
    Nat.eq_of_beq_eq_true hE
  have hB := ksFV_pexpoK_mat hV (R r) 64 (Nat.shiftRight (P t) 20)
    (Or.inl (by omega)) (by rw [hE']; exact hef)
  rw [hVt]
  change ordMat c.p c.d c.w c.S
    (mulR c.p c.w c.S c.d c.T c.L c.H c.CM c.RM
      (V (Nat.land (P t) 1048575)) (V (Nat.shiftRight (P t) 20))) = _
  rw [hmul, hA, hB, hE']
  simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]


private theorem ksFV_pwordRV_mat {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat} {Rn : Array (Array (Array Nat))}
    (hR : ksFV_PCorr c V N n R Rn) :
    ∀ (w : Word) (t : Nat), wordLt n w = true → wordRV P N R w t = true →
      ordMat c.p c.d c.w c.S (V t) =
        (w.reverse.map fun p => ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod := by
  intro w
  induction w with
  | nil =>
    intro t _ h
    rw [show wordRV P N R [] t = Nat.beq t 2 from rfl, Nat.beq_eq] at h
    subst h
    rw [List.reverse_nil, List.map_nil, List.prod_nil, hV.two, (one_sound hV.hc).2]
  | cons p w ih =>
    intro t hw h
    obtain ⟨r, e⟩ := p
    have hr : r < n := by
      have h' := hw
      simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact h'.1
    have hw' : wordLt n w = true := by
      have h' := hw
      simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact h'.2
    clear hw
    revert hw'
    rcases w with _ | ⟨q, ws⟩
    · intro hw'
      rw [show wordRV P N R [(r, e)] t =
        (decide (t < N) && decide (e < expoFail) &&
          Nat.beq (expoK P (R r) 64 t) e) from rfl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨htN, hef⟩, hE⟩ := h
      have hE' : expoK P (R r) 64 t = e := Nat.eq_of_beq_eq_true hE
      have hspec := ksFV_pexpoK_mat hV (R r) 64 t (Or.inl htN) (by rw [hE']; exact hef)
      rw [List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil]
      simpa [hE'] using hspec
    · intro hw'
      exact ksFV_pwordRV_cons hV hR hw' h ih
private theorem ksFV_pwordV_mat {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat} {Rn : Array (Array (Array Nat))}
    (hR : ksFV_PCorr c V N n R Rn) {w : Word} {t : Nat}
    (hwl : wordLt n w = true) (hw : wordV P N R w t = true) :
    ordMat c.p c.d c.w c.S (V t) =
      (w.map fun p => ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod := by
  change wordRV P N R w.reverse t = true at hw
  have h := ksFV_pwordRV_mat hV hR w.reverse t
    (by simpa [wordLt, List.all_reverse] using hwl) hw
  rwa [List.reverse_reverse] at h

private theorem ksFV_pword_evalW {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat} {Rn : Array (Array (Array Nat))}
    (hR : ksFV_PCorr c V N n R Rn) {w : Word} {t : Nat}
    (hwl : wordLt n w = true) (hw : wordV P N R w t = true) :
    CFSG.Sporadic.He.Native.toMat c.p c.d (evalW (opsP c.p c.d) Rn w) =
      ordMat c.p c.d c.w c.S (V t) := by
  rw [(ksFV_pevalW_spec hV hR w hwl).2, ksFV_pwordV_mat hV hR hwl hw]


private def ksFV_PCorrL (c : Lay) (V : Nat → Nat) (N n : Nat) (Rk : List Nat)
    (Rn : Array (Array (Array Nat))) : Prop :=
  Rk.length = n ∧ Rn.size = n ∧ ∀ r < n,
    (Rk.getD r 0 < N ∨ Rk.getD r 0 < 3) ∧
    validM c.p (c.d * c.S) c.L c.H (V (Rk.getD r 0)) = true ∧
    ksFV_ArrCanon c.p c.d (Rn[r]!) ∧
    CFSG.Sporadic.He.Native.toMat c.p c.d (Rn[r]!) =
      ordMat c.p c.d c.w c.S (V (Rk.getD r 0))

private theorem ksFV_pcorr_of_list {c : Lay} {V : Nat → Nat} {N n : Nat}
    {Rk : List Nat} {Rn : Array (Array (Array Nat))} (h : ksFV_PCorrL c V N n Rk Rn) :
    ksFV_PCorr c V N n (fun r => Rk.getD r 0) Rn :=
  ⟨h.2.1, fun r hr => h.2.2 r hr⟩

private theorem ksFV_pcorr_set {c : Lay} {V : Nat → Nat} {N n : Nat} {Rk : List Nat}
    {Rn : Array (Array (Array Nat))} (h : ksFV_PCorrL c V N n Rk Rn) {k t : Nat}
    {X : Array (Array Nat)} (hk : k < n) (ht : t < N ∨ t < 3)
    (hv : validM c.p (c.d * c.S) c.L c.H (V t) = true)
    (hcan : ksFV_ArrCanon c.p c.d X)
    (hmat : CFSG.Sporadic.He.Native.toMat c.p c.d X = ordMat c.p c.d c.w c.S (V t)) :
    ksFV_PCorrL c V N n (Rk.set k t) (Rn.set! k X) := by
  obtain ⟨hlen, hsize, h'⟩ := h
  have hkR : k < Rk.length := by omega
  have hkRn : k < Rn.size := by omega
  refine ⟨by rw [List.length_set, hlen], by rw [Array.size_set!, hsize], fun r hr => ?_⟩
  by_cases hrk : r = k
  · subst r
    have e1 : (Rk.set k t).getD k 0 = t := by
      rw [List.getD_eq_getElem?_getD]
      simp [hkR]
    have e2 : (Rn.set! k X)[k]! = X := Array.getElem!_set!_self Rn k X hkRn
    rw [e1, e2]
    exact ⟨ht, hv, hcan, hmat⟩
  · have e1 : (Rk.set k t).getD r 0 = Rk.getD r 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_set_ne (Ne.symm hrk)]
    have e2 : (Rn.set! k X)[r]! = Rn[r]! :=
      Array.getElem!_set!_ne Rn k r X (Ne.symm hrk)
    rw [e1, e2]
    exact h' r hr

private theorem ksFV_pcorr_mul {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {Rk : List Nat} {Rn : Array (Array (Array Nat))}
    (hR : ksFV_PCorrL c V N n Rk Rn) {i j k t : Nat} (hi : i < n) (hj : j < n) (hk : k < n)
    (h3 : 3 ≤ t) (hlt : t < N)
    (hP : P t = Rk.getD i 0 + 1048576 * Rk.getD j 0) :
    ksFV_PCorrL c V N n (Rk.set k t)
      (Rn.set! k (CFSG.Sporadic.He.Native.mulM c.p c.d Rn[i]! Rn[j]!)) := by
  have hRi := hR.2.2 i hi
  have hRj := hR.2.2 j hj
  have hN : N ≤ 1048576 := hV.hN
  have ha : Rk.getD i 0 < 1048576 := by rcases hRi.1 with h | h <;> omega
  have hstep : stepOK c V P t = true := hV.step t h3 hlt
  obtain ⟨-, -, hVt⟩ := stepOK_of_pair hstep hP ha
  have hcanX := hRi.2.2.1
  have hcanY := hRj.2.2.1
  have hp0 : 0 < c.p := by have := (cfacts hV.hc).1; omega
  have hcan := ksFV_canon_mulM (p := c.p) (d := c.d) hp0 hcanX.1
    (fun i hi => (hcanY.2 i hi).1)
  have hmat : CFSG.Sporadic.He.Native.toMat c.p c.d
      (CFSG.Sporadic.He.Native.mulM c.p c.d Rn[i]! Rn[j]!) = ordMat c.p c.d c.w c.S (V t) := by
    rw [CFSG.Sporadic.He.Native.toMat_mulM, hRi.2.2.2, hRj.2.2.2,
      ← (mulR_sound hV.hc (validM_canon hV.hc hRi.2.1)
        (validM_canon hV.hc hRj.2.1)).2, hVt]
    rfl
  exact ksFV_pcorr_set hR hk (Or.inl hlt) (hV.valid _ (Or.inl hlt)) hcan hmat

private theorem ksFV_pcorr_pow {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {Rk : List Nat} {Rn : Array (Array (Array Nat))}
    (hR : ksFV_PCorrL c V N n Rk Rn) {e i k t : Nat} (hi : i < n) (hk : k < n)
    (ht : (e = 0 ∧ t = 2) ∨ (t < N ∧ e < expoFail ∧ expoK P (Rk.getD i 0) 64 t = e)) :
    ksFV_PCorrL c V N n (Rk.set k t)
      (Rn.set! k ((opsP c.p c.d).pow Rn[i]! e)) := by
  have hRi := hR.2.2 i hi
  have hp2 : 1 < c.p := (cfacts hV.hc).1
  have hcanX := hRi.2.2.1
  have hcan := ksFV_canon_pow hp2 hcanX e
  rcases ht with ⟨he0, ht2⟩ | ⟨htN, hef, hek⟩
  · subst he0
    subst ht2
    have hmat : CFSG.Sporadic.He.Native.toMat c.p c.d ((opsP c.p c.d).pow Rn[i]! 0) =
        ordMat c.p c.d c.w c.S (V 2) := by
      rw [hV.two, (one_sound hV.hc).2]
      rw [Ops.pow]
      simp
      change CFSG.Sporadic.He.Native.toMat c.p c.d (CFSG.Sporadic.He.Native.idM c.d) = 1
      rw [CFSG.Sporadic.He.Native.toMat_idM]
    exact ksFV_pcorr_set hR hk (Or.inr (by norm_num)) (hV.valid _ (Or.inr (by norm_num)))
      hcan hmat
  · have hmat : CFSG.Sporadic.He.Native.toMat c.p c.d ((opsP c.p c.d).pow Rn[i]! e) =
        ordMat c.p c.d c.w c.S (V t) := by
      have hspec := ksFV_pexpoK_mat hV (Rk.getD i 0) 64 t (Or.inl htN)
        (by rw [hek]; exact hef)
      have hpow := OpsSpec.pow_spec (specP c.p c.d) (X := Rn[i]!) trivial e
      rw [show CFSG.Sporadic.He.Native.toMat c.p c.d ((opsP c.p c.d).pow Rn[i]! e) =
          CFSG.Sporadic.He.Native.toMat c.p c.d Rn[i]! ^ e from hpow.2,
        hRi.2.2.2, hspec, hek]
    exact ksFV_pcorr_set hR hk (Or.inl htN) (hV.valid _ (Or.inl htN)) hcan hmat

private theorem ksFV_preplay {c : Lay} {V P T : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) :
    ∀ (ops : List Op) (s n : Nat) (Rk : List Nat) (Rn : Array (Array (Array Nat))),
      ops.all (Op.lt Rk.length) = true → ksFV_PCorrL c V N n Rk Rn →
      (replayK c V P T N ops s Rk).1 = true →
      ksFV_PCorrL c V N n (replayK c V P T N ops s Rk).2
        (ops.foldl (opsP c.p c.d).step Rn) := by
  intro ops
  induction ops with
  | nil => intro s n Rk Rn _ hR _; simpa [replayK] using hR
  | cons op ops ih =>
    intro s n Rk Rn hall hR hok
    rw [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hop, hall'⟩ := hall
    cases op with
    | mul i j k =>
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
      obtain ⟨⟨hi, hj⟩, hk⟩ := hop
      simp only [replayK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨h3, hlt⟩, hP⟩, hrest⟩ := hok
      have hin : i < n := hR.1 ▸ hi
      have hjn : j < n := hR.1 ▸ hj
      have hkn : k < n := hR.1 ▸ hk
      have hcorr := ksFV_pcorr_mul hV hR hin hjn hkn h3 hlt (Nat.eq_of_beq_eq_true hP)
      have hall2 : ops.all (Op.lt (Rk.set k (T s)).length) = true := by
        rw [List.length_set]; exact hall'
      have key := ih (s + 1) n (Rk.set k (T s))
        (Rn.set! k (CFSG.Sporadic.He.Native.mulM c.p c.d Rn[i]! Rn[j]!)) hall2 hcorr hrest
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
      have hin : i < n := hR.1 ▸ hi
      have hkn : k < n := hR.1 ▸ hk
      have hcorr := ksFV_pcorr_pow hV hR hin hkn ht
      have hall2 : ops.all (Op.lt (Rk.set k (T s)).length) = true := by
        rw [List.length_set]; exact hall'
      have key := ih (s + 1) n (Rk.set k (T s))
        (Rn.set! k ((opsP c.p c.d).pow Rn[i]! e)) hall2 hcorr hrest
      exact key


private theorem ksFV_toVec_unitP (p d t : Nat) :
    (specP p d).toVec ((opsP p d).unit t) =
      fun j : Fin d => if (j : Nat) = t then (1 : ZMod p) else 0 := by
  funext j
  show CFSG.Sporadic.He.Native.toVec p d ((opsP p d).unit t) j = _
  rw [CFSG.Sporadic.He.Native.toVec_apply]
  unfold opsP
  rw [CFSG.Sporadic.He.Native.getElem!_ofFn _ j.isLt]
  split <;> simp

private theorem ksFV_pvne_of_toVec_ne {p d : Nat} {u w : Array Nat}
    (h : (specP p d).toVec u ≠ (specP p d).toVec w) : (opsP p d).vne u w = true := by
  by_contra hc
  apply h
  funext j
  change CFSG.Sporadic.He.Native.toVec p d u j = CFSG.Sporadic.He.Native.toVec p d w j
  rw [CFSG.Sporadic.He.Native.toVec_apply, CFSG.Sporadic.He.Native.toVec_apply]
  by_contra hne
  have hb : (u[j.val]! % p != w[j.val]! % p) = true := by
    rw [bne_iff_ne]
    intro he
    exact hne (by rw [ZMod.natCast_eq_natCast_iff'] at *; omega)
  have hany : (List.range d).any (fun k => u[k]! % p != w[k]! % p) = true :=
    List.any_eq_true.2 ⟨j.val, List.mem_range.2 j.isLt, hb⟩
  exact hc (by simpa [opsP] using hany)

private theorem ksFV_rowV_eq_of_toVecP {c : Lay} (hc : c.ok = true) {X Y : Nat}
    (hX : Canon c.p c.d c.w X) (hY : Canon c.p c.d c.w Y) {t : Nat} (ht : t < c.d)
    (h : (fun j : Fin c.d => ordMat c.p c.d c.w c.S X ⟨t, ht⟩ j) =
      fun j : Fin c.d => ordMat c.p c.d c.w c.S Y ⟨t, ht⟩ j) :
    rowV c X t = rowV c Y t := by
  obtain ⟨hS, -⟩ := ksFV_consts hc
  refine ksFV_rowV_eq_of_lane hc fun j hj => ?_
  have he := congrFun h ⟨j, hj⟩
  rw [ordMat_apply, ordMat_apply] at he
  have hidx : c.d * t + j < c.d * c.d := by nlinarith
  have hxl : X / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w < c.p := by
    have hl := hX.2 (c.d * t + j) hidx
    unfold lane at hl
    rwa [show c.w * (c.d * t + j) = c.S * t + c.w * j by rw [hS]; ring] at hl
  have hyl : Y / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w < c.p := by
    have hl := hY.2 (c.d * t + j) hidx
    unfold lane at hl
    rwa [show c.w * (c.d * t + j) = c.S * t + c.w * j by rw [hS]; ring] at hl
  have he' : ((X / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w : Nat) : ZMod c.p) =
      ((Y / 2 ^ (c.S * t + c.w * j) % 2 ^ c.w : Nat) : ZMod c.p) := by simpa using he
  have e := eq_of_cast hxl hyl he'
  rw [ksFV_rowV_lane hc (X := X) (t := t) (j := j) hj,
    ksFV_rowV_lane hc (X := Y) (t := t) (j := j) hj]
  exact e

private theorem ksFV_toVec_vmul_unitP {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat}
    {Rn : Array (Array (Array Nat))} (hR : ksFV_PCorr c V N n R Rn)
    {w : Word} {u t : Nat} (ht : t < c.d) (hwl : wordLt n w = true)
    (hword : wordV P N R w u = true) :
    (specP c.p c.d).toVec ((opsP c.p c.d).vmul ((opsP c.p c.d).unit t)
      (evalW (opsP c.p c.d) Rn w)) =
      fun j : Fin c.d => ordMat c.p c.d c.w c.S (V u) ⟨t, ht⟩ j := by
  obtain ⟨hwf, -⟩ := ksFV_pevalW_spec hV hR w hwl
  have hmat' := ksFV_pword_evalW hV hR hwl hword
  funext j
  rw [(specP c.p c.d).toVec_vmul trivial trivial, ksFV_toVec_unitP c.p c.d t, ← hmat']
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [if_pos rfl, one_mul]
    rfl
  · intro b _ hb
    have hb' : (b : Nat) ≠ t := fun h => hb (Fin.ext h)
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem ksFV_pfactOK_VP_ord {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat}
    {Rn : Array (Array (Array Nat))} (hR : ksFV_PCorr c V N n R Rn)
    {h r e : Nat} (hf : factV c V P N R n h (MFact.ord r e) = true) :
    factOK (opsP c.p c.d) Rn n (MFact.ord r e) = true := by
  have hp2 : 1 < c.p := (cfacts hV.hc).1
  simp only [factV, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hrest, hVone⟩ := hf
  obtain ⟨⟨hr, he⟩, hword⟩ := hrest
  have hrw := hR.2 r hr
  have hwl : wordLt n [(r, e)] = true := by
    simpa [wordLt] using decide_eq_true hr
  have hword' : ordMat c.p c.d c.w c.S (V (fld h 0)) =
      ordMat c.p c.d c.w c.S (V (R r)) ^ e := by
    simpa [List.map_cons, List.prod_cons] using ksFV_pwordV_mat hV hR hwl hword
  have hVone' : V (fld h 0) = c.ONE := Nat.eq_of_beq_eq_true hVone
  have hcan := ksFV_canon_pow hp2 hrw.2.2.1 e
  have hmat : CFSG.Sporadic.He.Native.toMat c.p c.d ((opsP c.p c.d).pow Rn[r]! e) =
      CFSG.Sporadic.He.Native.toMat c.p c.d (opsP c.p c.d).one := by
    have hpow := OpsSpec.pow_spec (specP c.p c.d) (X := Rn[r]!) trivial e
    rw [show CFSG.Sporadic.He.Native.toMat c.p c.d ((opsP c.p c.d).pow Rn[r]! e) =
        CFSG.Sporadic.He.Native.toMat c.p c.d Rn[r]! ^ e from hpow.2,
      hrw.2.2.2, ← hword', hVone', (one_sound hV.hc).2]
    change 1 = CFSG.Sporadic.He.Native.toMat c.p c.d (CFSG.Sporadic.He.Native.idM c.d)
    rw [CFSG.Sporadic.He.Native.toMat_idM]
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hr, he⟩, ?_⟩
  have heq := ksFV_eq_of_toMat_eq hcan (ksFV_canon_idM hp2) hmat
  rw [heq]; exact beq_self_eq_true _

private theorem ksFV_pfactOK_VP_conj {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat}
    {Rn : Array (Array (Array Nat))} (hR : ksFV_PCorr c V N n R Rn)
    {h : Nat} {g : Nat} {u w : Word} (hf : factV c V P N R n h (MFact.conj g u w) = true) :
    factOK (opsP c.p c.d) Rn n (MFact.conj g u w) = true := by
  have hp0 : 0 < c.p := by have := (cfacts hV.hc).1; omega
  simp only [factV, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hrest, hVeq⟩ := hf
  obtain ⟨⟨⟨⟨hg, hwu⟩, hww⟩, hvu⟩, hvw⟩ := hrest
  have hgu : wordLt n ((g, 1) :: u) = true := by
    simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hg, hwu⟩
  have hgw : wordLt n (w ++ [(g, 1)]) = true := by
    simp only [wordLt, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hww, hg⟩
  have hvu' : ordMat c.p c.d c.w c.S (V (fld h 0)) =
      ordMat c.p c.d c.w c.S (V (R g)) * (u.map fun p =>
        ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod := by
    simpa [List.map_cons, List.prod_cons] using ksFV_pwordV_mat hV hR hgu hvu
  have hvw' : ordMat c.p c.d c.w c.S (V (fld h 1)) = (w.map fun p =>
      ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod *
        ordMat c.p c.d c.w c.S (V (R g)) := by
    simpa [List.map_append, List.map_cons, List.prod_append, List.prod_cons] using
      ksFV_pwordV_mat hV hR hgw hvw
  have hVeq' : V (fld h 0) = V (fld h 1) := Nat.eq_of_beq_eq_true hVeq
  have hgR := hR.2 g hg
  obtain ⟨huwf, humat⟩ := ksFV_pevalW_spec hV hR u hwu
  obtain ⟨hwwf, hwmat⟩ := ksFV_pevalW_spec hV hR w hww
  have hcan1 := ksFV_canon_mulM hp0 hgR.2.2.1.1 (fun i hi => (huwf.2 i hi).1)
  have hcan2 := ksFV_canon_mulM hp0 hwwf.1 (fun i hi => (hgR.2.2.1.2 i hi).1)
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]; refine ⟨⟨⟨hg, hwu⟩, hww⟩, ?_⟩
  have hmat : CFSG.Sporadic.He.Native.toMat c.p c.d
      (CFSG.Sporadic.He.Native.mulM c.p c.d Rn[g]! (evalW (opsP c.p c.d) Rn u)) =
      CFSG.Sporadic.He.Native.toMat c.p c.d
        (CFSG.Sporadic.He.Native.mulM c.p c.d (evalW (opsP c.p c.d) Rn w) Rn[g]!) := by
    rw [CFSG.Sporadic.He.Native.toMat_mulM, CFSG.Sporadic.He.Native.toMat_mulM,
      hgR.2.2.2, humat, hwmat]
    calc
      ordMat c.p c.d c.w c.S (V (R g)) *
          (u.map fun p => ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod =
          ordMat c.p c.d c.w c.S (V (fld h 0)) := hvu'.symm
      _ = ordMat c.p c.d c.w c.S (V (fld h 1)) := by rw [hVeq']
      _ = (w.map fun p => ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod *
          ordMat c.p c.d c.w c.S (V (R g)) := hvw' 
  have heq := ksFV_eq_of_toMat_eq hcan1 hcan2 hmat
  change (opsP c.p c.d).eq
    (CFSG.Sporadic.He.Native.mulM c.p c.d Rn[g]! (evalW (opsP c.p c.d) Rn u))
    (CFSG.Sporadic.He.Native.mulM c.p c.d (evalW (opsP c.p c.d) Rn w) Rn[g]!) = true
  rw [heq]; exact beq_self_eq_true _

private theorem ksFV_pfactOK_VP_ne {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat}
    {Rn : Array (Array (Array Nat))} (hR : ksFV_PCorr c V N n R Rn)
    {h : Nat} {w1 w2 : Word} {t : Nat} (hf : factV c V P N R n h (MFact.ne w1 w2 t) = true) :
    factOK (opsP c.p c.d) Rn n (MFact.ne w1 w2 t) = true := by
  simp only [factV, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hrest, hne⟩ := hf
  obtain ⟨⟨⟨⟨hw1, hw2⟩, ht⟩, hword1⟩, hword2⟩ := hrest
  have hrowne : rowV c (V (fld h 0)) t ≠ rowV c (V (fld h 1)) t := by
    have hb : Nat.beq (rowV c (V (fld h 0)) t) (rowV c (V (fld h 1)) t) = false := by
      have := hne
      rwa [Bool.not_eq_true'] at this
    exact Nat.ne_of_beq_eq_false hb
  have hb0 := ksFV_wordV_bound (P := P) (N := N) (R := R) hword1
  have hb1 := ksFV_wordV_bound (P := P) (N := N) (R := R) hword2
  have hcan0 := validM_canon hV.hc (hV.valid _ hb0)
  have hcan1 := validM_canon hV.hc (hV.valid _ hb1)
  simp only [factOK, Bool.and_eq_true]
  refine ⟨⟨hw1, hw2⟩, ?_⟩
  apply ksFV_pvne_of_toVec_ne
  intro heq
  have hv1 := ksFV_toVec_vmul_unitP hV hR ht hw1 hword1
  have hv2 := ksFV_toVec_vmul_unitP hV hR ht hw2 hword2
  rw [hv1, hv2] at heq
  exact hrowne (ksFV_rowV_eq_of_toVecP hV.hc hcan0 hcan1 ht heq)

private theorem ksFV_pfactOK_VP_eq {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat}
    {Rn : Array (Array (Array Nat))} (hR : ksFV_PCorr c V N n R Rn)
    {h : Nat} {w1 w2 : Word} (hf : factV c V P N R n h (MFact.eq w1 w2) = true) :
    factOK (opsP c.p c.d) Rn n (MFact.eq w1 w2) = true := by
      simp only [factV, Bool.and_eq_true] at hf
      obtain ⟨hrest, hVeq⟩ := hf
      obtain ⟨⟨⟨hw1, hw2⟩, hword1⟩, hword2⟩ := hrest
      have hVeq' : V (fld h 0) = V (fld h 1) := Nat.eq_of_beq_eq_true hVeq
      have hword1' : ordMat c.p c.d c.w c.S (V (fld h 0)) = (w1.map fun p =>
          ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod := ksFV_pwordV_mat hV hR hw1 hword1
      have hword2' : ordMat c.p c.d c.w c.S (V (fld h 1)) = (w2.map fun p =>
          ordMat c.p c.d c.w c.S (V (R p.1)) ^ p.2).prod := ksFV_pwordV_mat hV hR hw2 hword2
      obtain ⟨hw1f, hmat1⟩ := ksFV_pevalW_spec hV hR w1 hw1
      obtain ⟨hw2f, hmat2⟩ := ksFV_pevalW_spec hV hR w2 hw2
      simp only [factOK, Bool.and_eq_true]
      refine ⟨⟨hw1, hw2⟩, ?_⟩
      have heq := ksFV_eq_of_toMat_eq hw1f hw2f (by rw [hmat1, hmat2, ← hword1', ← hword2', hVeq'])
      rw [heq]
      exact beq_self_eq_true _


private theorem ksFV_pdecode_mat {c : Lay} {V : Nat → Nat} {M : Nat} {s : String}
    (e : (opsP c.p c.d).decode s = unpackL c.d c.w c.S (V M)) :
    CFSG.Sporadic.He.Native.toMat c.p c.d ((opsP c.p c.d).decode s) =
      ordMat c.p c.d c.w c.S (V M) := by
  rw [e, ksFV_toMat_unpackL_eq]

private theorem ksFV_pinitial {c : Lay} (hc : c.ok = true) {V : Nat → Nat} {N n : Nat}
    {sA sB : String} (h0 : validM c.p (c.d * c.S) c.L c.H (V 0) = true)
    (h1 : validM c.p (c.d * c.S) c.L c.H (V 1) = true) (h2 : V 2 = c.ONE)
    (eA : (opsP c.p c.d).decode sA = unpackL c.d c.w c.S (V 0))
    (eB : (opsP c.p c.d).decode sB = unpackL c.d c.w c.S (V 1)) :
    ksFV_PCorrL c V N n (initK n)
      ((opsP c.p c.d).initRegs ((opsP c.p c.d).decode sA) ((opsP c.p c.d).decode sB) n) := by
  have hp0 : 0 < c.p := by have := (cfacts hc).1; omega
  have h1p : 1 < c.p := (cfacts hc).1
  have h2v : validM c.p (c.d * c.S) c.L c.H c.ONE = true :=
    CFSG.KS.OrdCanon.validM_of_canon hc (one_sound hc).1
  have hAmat := ksFV_pdecode_mat (c := c) (V := V) (M := 0) eA
  have hBmat := ksFV_pdecode_mat (c := c) (V := V) (M := 1) eB
  have hAcan : ksFV_ArrCanon c.p c.d ((opsP c.p c.d).decode sA) := by
    change ksFV_ArrCanon c.p c.d (CFSG.Sporadic.He.Native.rowsOf c.p c.d sA)
    exact ksFV_canon_rowsOf hp0 sA
  have hBcan : ksFV_ArrCanon c.p c.d ((opsP c.p c.d).decode sB) := by
    change ksFV_ArrCanon c.p c.d (CFSG.Sporadic.He.Native.rowsOf c.p c.d sB)
    exact ksFV_canon_rowsOf hp0 sB
  have hOmat : CFSG.Sporadic.He.Native.toMat c.p c.d (opsP c.p c.d).one =
      ordMat c.p c.d c.w c.S (V 2) := by
    rw [h2, (one_sound hc).2]
    change CFSG.Sporadic.He.Native.toMat c.p c.d (CFSG.Sporadic.He.Native.idM c.d) = 1
    rw [CFSG.Sporadic.He.Native.toMat_idM]
  refine ⟨by simp only [initK, List.length_map, List.length_range],
    by simp [Ops.initRegs], fun r hr => ?_⟩
  have hRk : (initK n).getD r 0 = if r = 0 then 0 else if r = 1 then 1 else 2 := by
    rw [List.getD_eq_getElem?_getD, initK, List.getElem?_map,
      List.getElem?_eq_getElem (by simpa using hr)]
    by_cases h0r : r = 0 <;> by_cases h1r : r = 1 <;> simp [h0r, h1r]
  have hRn : ((opsP c.p c.d).initRegs ((opsP c.p c.d).decode sA)
      ((opsP c.p c.d).decode sB) n)[r]! =
      if r = 0 then (opsP c.p c.d).decode sA
      else if r = 1 then (opsP c.p c.d).decode sB else (opsP c.p c.d).one := by
    rw [getElem!_pos _ r (by simpa [Ops.initRegs] using hr)]
    simp [Ops.initRegs]
  rw [hRk, hRn]
  by_cases h0r : r = 0
  · subst h0r
    simp only [if_true]
    exact ⟨Or.inr (by norm_num), h0, hAcan, hAmat⟩
  by_cases h1r : r = 1
  · subst h1r
    simp only [if_false, if_true, one_ne_zero]
    exact ⟨Or.inr (by norm_num), h1, hBcan, hBmat⟩
  · simp only [h0r, h1r, if_false]
    exact ⟨Or.inr (by norm_num), by rw [h2]; exact h2v, ksFV_canon_idM h1p, hOmat⟩


private theorem ksFV_pcorr_of_Rf {c : Lay} {V : Nat → Nat} {N n : Nat} {Rk : List Nat}
    {Rn : Array (Array (Array Nat))} {Rf : Nat → Nat} (h : ksFV_PCorrL c V N n Rk Rn)
    (hRf : ∀ r < n, Rf r = Rk.getD r 0) : ksFV_PCorr c V N n Rf Rn := by
  refine ⟨h.2.1, fun r hr => ?_⟩
  have hh := h.2.2 r hr
  rwa [← hRf r hr] at hh

private theorem ksFV_pfactOK_VP {c : Lay} {V P : Nat → Nat} {N : Nat}
    (hV : ksFV_PVals c V P N) {n : Nat} {R : Nat → Nat}
    {Rn : Array (Array (Array Nat))} (hR : ksFV_PCorr c V N n R Rn)
    {h : Nat} {f : MFact} (hf : factV c V P N R n h f = true) :
    factOK (opsP c.p c.d) Rn n f = true := by
  cases f with
  | ord r e => exact ksFV_pfactOK_VP_ord hV hR hf
  | conj g u w => exact ksFV_pfactOK_VP_conj hV hR hf
  | ne w1 w2 t => exact ksFV_pfactOK_VP_ne hV hR hf
  | eq w1 w2 => exact ksFV_pfactOK_VP_eq hV hR hf

theorem factOK_of_VP {c : Lay} {p d : Nat} (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hd0 : 0 < d) {sA sB : String} {V P T Rf : Nat → Nat} {N n : Nat} {prog : List Op}
    (eA : (opsP p d).decode sA = unpackL c.d c.w c.S (V 0))
    (eB : (opsP p d).decode sB = unpackL c.d c.w c.S (V 1))
    (vA : validM c.p (c.d * c.S) c.L c.H (V 0) = true)
    (vB : validM c.p (c.d * c.S) c.L c.H (V 1) = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : regsV c V P T N n prog Rf = true) (h : Nat)
    (f : MFact) (hf : factV c V P N Rf n h f = true) :
    factOK (opsP p d) ((opsP p d).regsOf sA sB n prog) n f = true := by
  subst hp
  subst hd
  unfold regsV at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨hN, h2⟩, hprog⟩, hrep⟩, hlist⟩ := hr
  have hV := ksFV_pvals hc hN hs vA vB h1
  set Rk0 : List Nat := initK n with hRk0
  set Rn0 : Array (Array (Array Nat)) :=
    (opsP c.p c.d).initRegs ((opsP c.p c.d).decode sA) ((opsP c.p c.d).decode sB) n with hRn0
  have hRk0len : Rk0.length = n := by simp [hRk0, initK]
  have hprog' : prog.all (Op.lt Rk0.length) = true := by rw [hRk0len]; exact hprog
  have hinit : ksFV_PCorrL c V N n Rk0 Rn0 := by
    simpa [hRk0, hRn0] using ksFV_pinitial hc vA vB h1 eA eB
  have hcorr := ksFV_preplay hV prog 0 n Rk0 Rn0 hprog' hinit hrep
  have hlen : (replayK c V P T N prog 0 Rk0).2.length = n := by
    rw [replayK_length, hRk0len]
  have hregs : (opsP c.p c.d).regsOf sA sB n prog =
      prog.foldl (opsP c.p c.d).step Rn0 := rfl
  rw [hregs]
  have hRf : ∀ r < n, Rf r = (replayK c V P T N prog 0 Rk0).2.getD r 0 := by
    intro r hr
    have hq : r < (replayK c V P T N prog 0 Rk0).2.length := by rw [hlen]; exact hr
    have hget : (replayK c V P T N prog 0 Rk0).2.getD r 0 =
        (replayK c V P T N prog 0 Rk0).2[r]! := by
      rw [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem hq]
      rfl
    rw [hget, ksFV_listIs _ 0 hlist r hq, Nat.zero_add]
  exact ksFV_pfactOK_VP hV (ksFV_pcorr_of_Rf hcorr hRf) hf

theorem factsFrom_spec {c : Lay} {V P : Nat → Nat} {N : Nat} {R : Nat → Nat} {n : Nat}
    {H : Nat → Nat} {sel : MFact → Bool} :
    ∀ (fs : List MFact) (j₀ : Nat), factsFrom c V P N R n H sel fs j₀ = true →
      ∀ (q : Nat) (hq : q < fs.length), sel fs[q] = true →
        factV c V P N R n (H (j₀ + q)) fs[q] = true
  | [], _, _, q, hq, _ => absurd hq (by simp)
  | f :: fs, j₀, h, q, hq, hs => by
    unfold factsFrom at h
    rw [Bool.and_eq_true] at h
    rcases q with _ | q
    · simp only [List.getElem_cons_zero] at hs ⊢
      rw [hs, Bool.not_true, Bool.false_or] at h
      simpa using h.1
    · simp only [List.getElem_cons_succ] at hs ⊢
      have := factsFrom_spec fs (j₀ + 1) h.2 q (by simpa using hq) hs
      rwa [Nat.add_right_comm, Nat.add_assoc] at this

theorem facts_of_chunks {c : Lay} {V P : Nat → Nat} {N : Nat} {R : Nat → Nat} {n : Nat}
    {Q : MFact → Bool} (hQ : ∀ h f, factV c V P N R n h f = true → Q f = true)
    {fs : List MFact} {H : Nat → Nat} {sel : MFact → Bool} {k m : Nat} (hm : fs.length ≤ m * k)
    (h : ∀ i < m, chunkV c V P N R n fs H sel k i = true) :
    fs.all (fun f => !sel f || Q f) = true := by
  rw [List.all_eq_true]
  intro f hf
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [Nat.mul_zero] at hm
      omega
    · exact h0
  have hi : j / k < m := by
    rw [Nat.div_lt_iff_lt_mul hk]
    omega
  have hjk : j / k * k + j % k = j := Nat.div_add_mod' j k
  have hmod : j % k < k := Nat.mod_lt j hk
  have hc := h (j / k) hi
  unfold chunkV at hc
  have hq : j % k < ((fs.drop (j / k * k)).take k).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have he : ((fs.drop (j / k * k)).take k)[j % k] = fs[j] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
  cases hs : sel fs[j]
  · rfl
  · have := factsFrom_spec _ _ hc (j % k) hq (by rw [he]; exact hs)
    rw [he] at this
    rw [hQ _ _ this]
    rfl

end CFSG.KC.LocalComp.FactsV

end
