module

public import CFSG.Certificates.Kernel.K3Defs
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.MulHInvSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.K3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Th.Native CFSG.KS.MulH
open CFSG.EvenSmallLie.Child3.SelK3

namespace SP

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem bA {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem bIt {c : Bool} (h : Bool.rec (motive := fun _ => Bool) true false c = true) :
    c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

abbrev Cn (K : K3C) (P : Nat) : Prop := canonK K.n K.w (mask K.w) (K.n * K.w) P = true

noncomputable abbrev tb (K : K3C) (P : Nat) : Table := tabT (unpack K.n K.w P)

variable {K : K3C}

theorem cn_pc {P Q : Nat} (hP : Cn K P) (hQ : Cn K Q) : Cn K (K.pc P Q) :=
  CFSG.KC.BfsPin.canonK_pcomp hP hQ

theorem tb_pc {P Q : Nat} (hP : Cn K P) (hQ : Cn K Q) :
    compT K.n (tb K P) (tb K Q) = tb K (K.pc P Q) := by
  change _ = tabT (unpack K.n K.w (pcomp K.n K.w (mask K.w) P Q))
  rw [compT_tabT _ _ (fun i _ => unpack_lt hQ), CFSG.KC.BfsPin.compA_unpack hP hQ]

theorem cn_one (hs : szOK K.n K.w = true) : Cn K K.one := (CFSG.KC.BfsPin.PP.id hs).1

theorem tb_one (hs : szOK K.n K.w = true) : tb K K.one = idT K.n := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq hs]
  rfl

theorem pw_succ (P e : Nat) : K.pw P (e + 1) = K.pc P (K.pw P e) := by
  change strictN (K.pw P e) (fun a => K.pc P a) = _
  exact sN _ _

theorem pw_facts (hs : szOK K.n K.w = true) {P : Nat} (hP : Cn K P) :
    ∀ e, Cn K (K.pw P e) ∧ tb K (K.pw P e) = powT K.n e (tb K P)
  | 0 => ⟨cn_one hs, tb_one hs⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := pw_facts hs hP e
    rw [pw_succ]
    refine ⟨cn_pc hP h1, ?_⟩
    rw [← tb_pc hP h1, h2]
    rfl

theorem pg_lt {P i : Nat} (hP : Cn K P) (hi : i < K.n) : pg K.w (mask K.w) P i < 2 ^ 32 := by
  have := unpack_lt (i := i) hP
  rwa [CFSG.KS.Raw.Orb.unpack_get hi] at this

theorem ap_tb {P i : Nat} (hP : Cn K P) (hi : i < K.n) : ap (tb K P) i = pg K.w (mask K.w) P i := by
  rw [ap_tabT _ (unpack_lt hP), CFSG.KS.Raw.Orb.unpack_get hi]

theorem invOK_tb {P Q : Nat} (hP : Cn K P) (hQ : Cn K Q)
    (h : permOK K.n K.w (mask K.w) (K.n * K.w) P Q = true) : invOK K.n (tb K P) (tb K Q) = true := by
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  unfold invOK
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  rw [ap_tb hP hi, ap_tb hQ (h3 i hi).1, (h3 i hi).2]
  exact beq_self_eq_true i

theorem invT_tb {P Q : Nat} (hP : Cn K P)
    (h : permOK K.n K.w (mask K.w) (K.n * K.w) P Q = true) : invT K.n (tb K P) = tb K Q :=
  invT_unpack (lt_of_canonK hP) h

@[expose] noncomputable def VV (K : K3C) : Nat → Nat → Nat
  | 0, r => K.val r
  | t + 1, r => if K.tg t = r then K.W t else VV K t r

theorem VV_succ (t r : Nat) : VV K (t + 1) r = if K.tg t = r then K.W t else VV K t r := rfl

theorem VV_none {r : Nat} : ∀ t, (∀ v < t, K.tg v ≠ r) → VV K t r = K.val r
  | 0, _ => rfl
  | t + 1, h => by
    rw [VV_succ, ite_eq_right (h t (Nat.lt_succ_self t))]
    exact VV_none t fun v hv => h v (Nat.lt_succ_of_lt hv)

theorem VV_last {r u : Nat} (hu : K.tg u = r) :
    ∀ d, (∀ d' < d, K.tg (u + 1 + d') ≠ r) → VV K (u + 1 + d) r = K.W u
  | 0, _ => by
    rw [Nat.add_zero, VV_succ, ite_eq_left hu]
  | d + 1, h => by
    rw [← Nat.add_assoc, VV_succ, ite_eq_right (h d (Nat.lt_succ_self d))]
    exact VV_last hu d fun d' hd' => h d' (Nat.lt_succ_of_lt hd')

theorem val_ge {v : Nat} (hv : K.R ≤ v) : K.val v = K.W (v - K.R) := by
  unfold K3C.val
  have e : Nat.blt v K.R = false := by
    cases h : Nat.blt v K.R
    · rfl
    · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt.2 hv)
  rw [e]
  rfl

theorem val_lt {v : Nat} (hv : v < K.R) :
    K.val v = if v < K.g then K.GP v else K.one := by
  unfold K3C.val
  rw [Nat.blt_eq.mpr hv]
  by_cases h : v < K.g
  · rw [Nat.blt_eq.mpr h, ite_eq_left h]
  · have e : Nat.blt v K.g = false := by
      cases h' : Nat.blt v K.g
      · rfl
      · exact absurd (Nat.blt_eq.mp h') h
    rw [e, ite_eq_right h]

theorem srcOK_spec {r t s : Nat} (h : K.srcOK r t s = true) :
    K.val s = VV K t r ∧ (s < K.R ∨ (K.R ≤ s ∧ s - K.R < t)) := by
  unfold K3C.srcOK at h
  by_cases hs : s < K.R
  · rw [Nat.blt_eq.mpr hs] at h
    obtain ⟨h1, h2⟩ := bA.1 h
    have e : s = r := Nat.eq_of_beq_eq_true h1
    subst e
    refine ⟨(VV_none t fun v hv => ?_).symm, Or.inl hs⟩
    have := allN_spec h2 v hv
    intro e
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)
  · have e : Nat.blt s K.R = false := by
      cases h' : Nat.blt s K.R
      · rfl
      · exact absurd (Nat.blt_eq.mp h') hs
    rw [e] at h
    change strictB _ _ = true at h
    rw [sB] at h
    obtain ⟨h1, h2⟩ := bA.1 h
    obtain ⟨h3, h4⟩ := bA.1 h2
    have hu : Nat.sub s K.R < t := Nat.blt_eq.mp h1
    have htg : K.tg (Nat.sub s K.R) = r := Nat.eq_of_beq_eq_true h3
    have hs' : K.R ≤ s := Nat.le_of_not_lt hs
    refine ⟨?_, Or.inr ⟨hs', hu⟩⟩
    rw [val_ge hs']
    have key := VV_last htg (t - Nat.sub s K.R - 1) fun d' hd' => by
      have := allN_spec h4 d' hd'
      intro e'
      have e'' : Nat.add (Nat.succ (Nat.sub s K.R)) d' = Nat.sub s K.R + 1 + d' := rfl
      rw [e'', e', Nat.beq_refl] at this
      exact absurd this (by decide)
    rw [show Nat.sub s K.R + 1 + (t - Nat.sub s K.R - 1) = t by omega] at key
    exact key.symm

theorem stepK_facts {t : Nat} (h : K.stepK t = true) :
    Cn K (K.W t) ∧ K.OP t < 3 ∧ K.tg t < K.R ∧ K.r1 t < K.R ∧
      K.srcOK (K.r1 t) t (K.S1 t) = true ∧
      (K.OP t = 0 → K.A2 t < K.R ∧ K.srcOK (K.A2 t) t (K.S2 t) = true ∧
        K.W t = K.pc (K.val (K.S1 t)) (K.val (K.S2 t))) ∧
      (K.OP t = 1 → K.W t = K.pw (K.val (K.S1 t)) (K.A1 t)) ∧
      (K.OP t = 2 → permOK K.n K.w (mask K.w) (K.n * K.w) (K.val (K.S1 t)) (K.W t) = true) := by
  unfold K3C.stepK at h
  rw [sB] at h
  obtain ⟨h1, h2⟩ := bA.1 h
  obtain ⟨h3, h4⟩ := bA.1 h2
  obtain ⟨h5, h6⟩ := bA.1 h4
  obtain ⟨h7, h8⟩ := bA.1 h6
  obtain ⟨h9, h10⟩ := bA.1 h8
  refine ⟨h1, Nat.blt_eq.mp h3, Nat.blt_eq.mp h5, Nat.blt_eq.mp h7, h9, fun e => ?_, fun e => ?_,
    fun e => ?_⟩
  · rw [e] at h10
    obtain ⟨a1, a2⟩ := bA.1 h10
    obtain ⟨a3, a4⟩ := bA.1 a2
    exact ⟨Nat.blt_eq.mp a1, a3, Nat.eq_of_beq_eq_true a4⟩
  · rw [e] at h10
    exact Nat.eq_of_beq_eq_true h10
  · rw [e] at h10
    exact h10

theorem getElem!_set!' {α : Type} [Inhabited α] (a : Array α) (k r : Nat) (v : α)
    (hr : r < a.size) : (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

def RegInv (K : K3C) (t : Nat) (st : Array Table × Bool) : Prop :=
  st.2 = true ∧ st.1.size = K.R ∧ ∀ r < K.R, st.1[r]! = tb K (VV K t r) ∧ Cn K (VV K t r)

theorem regInv_step (hs : szOK K.n K.w = true) {t : Nat} (hk : K.stepK t = true)
    {st : Array Table × Bool} (hI : RegInv K t st) :
    RegInv K (t + 1) (stepT K.n st (instrOf K t)) := by
  obtain ⟨hf, hsz, hr⟩ := hI
  obtain ⟨hW, hop, htg, hr1, hs1, h0, h1, h2⟩ := stepK_facts hk
  obtain ⟨e1, -⟩ := srcOK_spec hs1
  have hcn1 : Cn K (VV K t (K.r1 t)) := (hr _ hr1).2
  have key : ∀ (v : Table) (b : Bool), b = true → v = tb K (K.W t) →
      RegInv K (t + 1) (st.1.set! (K.tg t) v, b) := by
    intro v b hb hv
    refine ⟨hb, by simp [hsz], fun r hrR => ?_⟩
    change (st.1.set! (K.tg t) v)[r]! = _ ∧ _
    rw [VV_succ, getElem!_set!' _ _ _ _ (by omega)]
    by_cases e : K.tg t = r
    · rw [ite_eq_left e, ite_eq_left e, hv]
      exact ⟨rfl, hW⟩
    · rw [ite_eq_right e, ite_eq_right e]
      exact hr r hrR
  rcases (by omega : K.OP t = 0 ∨ K.OP t = 1 ∨ K.OP t = 2) with e | e | e
  · obtain ⟨ha2, hs2, hWe⟩ := h0 e
    obtain ⟨e2, -⟩ := srcOK_spec hs2
    have hi : instrOf K t = .mu (K.A1 t) (K.A2 t) (K.A3 t) := by
      simp [instrOf, e]
    have htg' : K.tg t = K.A3 t := by
      unfold K3C.tg
      rw [e]
      rfl
    have hr1' : K.r1 t = K.A1 t := by
      unfold K3C.r1
      rw [e]
      rfl
    rw [hi]
    rw [hr1'] at hcn1 e1 hr1
    have hcn2 : Cn K (VV K t (K.A2 t)) := (hr _ ha2).2
    have hv : compT K.n st.1[K.A1 t]! st.1[K.A2 t]! = tb K (K.W t) := by
      rw [(hr _ hr1).1, (hr _ ha2).1, tb_pc hcn1 hcn2, hWe, e1, e2]
    change RegInv K (t + 1) (st.1.set! (K.A3 t) (compT K.n st.1[K.A1 t]! st.1[K.A2 t]!), st.2)
    rw [← htg']
    exact key _ _ hf hv
  · have hWe := h1 e
    have hi : instrOf K t = .pwr (K.A1 t) (K.A2 t) (K.A3 t) := by
      simp [instrOf, e]
    have htg' : K.tg t = K.A3 t := by
      unfold K3C.tg
      rw [e]
      rfl
    have hr1' : K.r1 t = K.A2 t := by
      unfold K3C.r1
      rw [e]
      rfl
    rw [hi]
    rw [hr1'] at hcn1 e1 hr1
    have hv : powT K.n (K.A1 t) st.1[K.A2 t]! = tb K (K.W t) := by
      rw [(hr _ hr1).1, ← (pw_facts hs hcn1 _).2, hWe, e1]
    change RegInv K (t + 1) (st.1.set! (K.A3 t) (powT K.n (K.A1 t) st.1[K.A2 t]!), st.2)
    rw [← htg']
    exact key _ _ hf hv
  · have hp := h2 e
    have hi : instrOf K t = .iv (K.A1 t) (K.A2 t) := by
      have e0 : K.OP t ≠ 0 := by omega
      have e1' : K.OP t ≠ 1 := by omega
      simp [instrOf, e0, e1']
    have htg' : K.tg t = K.A2 t := by
      unfold K3C.tg
      rw [e]
      rfl
    have hr1' : K.r1 t = K.A1 t := by
      unfold K3C.r1
      rw [e]
      rfl
    rw [hi]
    rw [hr1'] at hcn1 e1 hr1
    rw [← e1] at hcn1
    have hP : st.1[K.A1 t]! = tb K (K.val (K.S1 t)) := by
      rw [(hr _ hr1).1, e1]
    have hv : invT K.n st.1[K.A1 t]! = tb K (K.W t) := by
      rw [hP, invT_tb hcn1 hp]
    change RegInv K (t + 1) (st.1.set! (K.A2 t) (invT K.n st.1[K.A1 t]!),
      st.2 && invOK K.n st.1[K.A1 t]! (invT K.n st.1[K.A1 t]!))
    rw [← htg']
    refine key _ _ ?_ hv
    rw [hf, hv, hP, invOK_tb hcn1 hW hp, Bool.true_and]

theorem regs0_get {D : Data} (hn : D.n = K.n) (hR : D.regs = K.R) (hg : D.gens.size = K.g)
    (hgt : ∀ i < K.g, D.gens[i]! = tblOf K (K.GP i)) (hs : szOK K.n K.w = true)
    (hgR : K.g ≤ K.R) : (regs0 D).size = K.R ∧ ∀ r < K.R, (regs0 D)[r]! = tb K (K.val r) := by
  have hsz : (regs0 D).size = K.R := by
    simp [regs0, hg, hR]
    omega
  refine ⟨hsz, fun r hr => ?_⟩
  rw [val_lt hr, getElem!_pos _ r (by omega)]
  unfold regs0
  by_cases h : r < K.g
  · rw [ite_eq_left h, Array.getElem_append_left (by omega), ← getElem!_pos D.gens r (by omega), hgt r h]
    rfl
  · rw [ite_eq_right h, Array.getElem_append_right (by omega), Array.getElem_replicate, hn,
      tb_one hs]

theorem slp_run {D : Data} (hn : D.n = K.n) (hR : D.regs = K.R)
    (hprog : D.prog = (List.range K.N).map (instrOf K)) (hg : D.gens.size = K.g)
    (hgt : ∀ i < K.g, D.gens[i]! = tblOf K (K.GP i)) (hs : szOK K.n K.w = true) (hgR : K.g ≤ K.R)
    (hgc : ∀ i < K.g, Cn K (K.GP i)) (hst : ∀ t < K.N, K.stepK t = true) :
    RegInv K K.N (runSLP D.n D.prog (regs0 D)) := by
  obtain ⟨hsz0, hget0⟩ := regs0_get hn hR hg hgt hs hgR
  have base : RegInv K 0 (regs0 D, true) := by
    refine ⟨rfl, hsz0, fun r hr => ⟨hget0 r hr, ?_⟩⟩
    change Cn K (K.val r)
    rw [val_lt hr]
    split
    · exact hgc r ‹_›
    · exact cn_one hs
  have key : ∀ t ≤ K.N, RegInv K t (((List.range t).map (instrOf K)).foldl (stepT K.n)
      (regs0 D, true)) := by
    intro t
    induction t with
    | zero => intro _; exact base
    | succ t ih =>
      intro ht
      rw [List.range_succ, List.map_append, List.foldl_append]
      exact regInv_step hs (hst t (by omega)) (ih (by omega))
  rw [hprog, hn]
  exact key K.N (Nat.le_refl _)

theorem slp_final {st : Array Table × Bool} (hI : RegInv K K.N st)
    (hf : ∀ r < K.R, K.finK r = true) :
    st.2 = true ∧ st.1.size = K.R ∧ ∀ r < K.R, st.1[r]! = tb K (K.reg r) ∧ Cn K (K.reg r) := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨h1, h2, fun r hr => ?_⟩
  have e := (srcOK_spec (hf r hr)).1
  change st.1[r]! = tb K (K.val (K.FR r)) ∧ Cn K (K.val (K.FR r))
  rw [e]
  exact h3 r hr

theorem instrLt_all {D : Data} (hR : D.regs = K.R) (hprog : D.prog = (List.range K.N).map (instrOf K))
    (hst : ∀ t < K.N, K.stepK t = true) : D.prog.all (instrLtB D.regs) = true := by
  rw [hprog, hR, List.all_eq_true]
  intro ins hins
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hins
  obtain ⟨-, hop, htg, hr1, -, h0, -, -⟩ := stepK_facts (hst t (List.mem_range.1 ht))
  rcases (by omega : K.OP t = 0 ∨ K.OP t = 1 ∨ K.OP t = 2) with e | e | e
  · have htg' : K.tg t = K.A3 t := by
      unfold K3C.tg
      rw [e]
      rfl
    have hr1' : K.r1 t = K.A1 t := by
      unfold K3C.r1
      rw [e]
      rfl
    have ha2 := (h0 e).1
    simp [instrOf, e, instrLtB]
    omega
  · have htg' : K.tg t = K.A3 t := by
      unfold K3C.tg
      rw [e]
      rfl
    have hr1' : K.r1 t = K.A2 t := by
      unfold K3C.r1
      rw [e]
      rfl
    simp [instrOf, e, instrLtB]
    omega
  · have htg' : K.tg t = K.A2 t := by
      unfold K3C.tg
      rw [e]
      rfl
    have hr1' : K.r1 t = K.A1 t := by
      unfold K3C.r1
      rw [e]
      rfl
    have e0 : K.OP t ≠ 0 := by omega
    have e1 : K.OP t ≠ 1 := by omega
    simp [instrOf, e0, e1, instrLtB]
    omega

end SP

end CFSG.KC.K3

end
