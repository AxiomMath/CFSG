module

public import CFSG.Certificates.Kernel.DceS5Step

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Loop CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw
open scoped Classical

set_option exponentiation.threshold 400

variable {G : Type*} [Group G] {LT LI TL VL NL : ℕ}

theorem wordOK_spec {WD RR : ℕ → ℕ} {NR WH w : ℕ} (h : wordOK WD RR LI NL NR WH w = true) :
    byte WH w < NR ∧ (∀ q < bits (WD w) 2 10, byte (Nat.shiftRight (WD w) 12) q < NL ∨
      byte (Nat.shiftRight (WD w) 12) q = 255) ∧
      CFSG.KC.Th.chkWord LI (Nat.shiftRight (WD w) 12) (bits (WD w) 2 10)
        (Nat.shiftRight (RR (byte WH w)) 12) (bits (RR (byte WH w)) 2 10) = true := by
  unfold wordOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andL_iff.1 h
  obtain ⟨e2, e3⟩ := andL_iff.1 r
  refine ⟨Nat.blt_eq.mp e1, fun q hq => ?_, e3⟩
  have := (allL_iff (fun i => orB (Nat.blt (byte (Nat.shiftRight (WD w) 12) i) NL)
    (Nat.beq (byte (Nat.shiftRight (WD w) 12) i) 255)) _).1 e2 q hq
  rcases orL_iff.1 this with h1 | h1
  · exact Or.inl (Nat.blt_eq.mp h1)
  · exact Or.inr (Nat.eq_of_beq_eq_true h1)

theorem words_sem {x : ℕ → G} {WD RR : ℕ → ℕ} {NR WH nW : ℕ} (hL : LetOK LT LI TL VL NL)
    (hrels : ∀ r < NR, rval x (RR r) = 1) (hnorm : CFSG.Certificates.LCE.relsNorm RR NR = true)
    (hinv : ∀ c < NL, isN TL VL NL c = true → x (byte LI c) = (x c)⁻¹) (hu : x VL = (x TL)⁻¹)
    (hw : wordsOK WD RR LI NL NR WH nW = true) :
    ∀ w < nW, wv (lvE x) (Nat.shiftRight (WD w) 12) (bits (WD w) 2 10) = 1 := by
  have hall : ∀ c < NL, x (byte LI c) = (x c)⁻¹ := by
    intro c hc
    by_cases hN : isN TL VL NL c = true
    · exact hinv c hc hN
    · have : c = TL ∨ c = VL := by
        by_contra hne
        push Not at hne
        exact hN (isN_iff.2 ⟨hc, hne.1, hne.2⟩)
      rcases this with rfl | rfl
      · rw [hL.tli, hu]
      · rw [hL.vli, hu, inv_inv]
  intro w hw'
  obtain ⟨h1, h2, h3⟩ := wordOK_spec ((allL_iff (fun w => wordOK WD RR LI NL NR WH w) nW).1 hw w hw')
  exact chkWord_sound x (relsNorm_spec hnorm _ h1) (hrels _ h1) (fun q hq hne =>
    hall _ ((h2 q hq).resolve_right hne)) h3

theorem sD_lt (S : ℕ) : sD S < 256 := land255_lt S

section Walk

variable {HB GB TB FB : ℕ → ℕ} {NO nT W Wi ND sh wd : ℕ} {x : ℕ → G} {φ : Mg LT LI TL VL NL →* G}
  (h : SCtx HB GB TB LT LI TL VL NL NO nT W Wi x φ) (hND : ND < 255)
include h hND

theorem walk_sem (w : ℕ → G) {i Ri ft fd Wd n S0 : ℕ} {Ss : ℕ → ℕ}
    (hprev : ∀ k < i, RecGood ND NO (rec FB sh wd k) ∧ InM LT LI TL VL NL (rPi (rec FB sh wd k)) ∧
      FM φ HB GB x w (rec FB sh wd k))
    (hRi : RecGood ND NO Ri) (h0 : Ss 0 = S0) (hn : Ss n = S0)
    (hS0 : InM LT LI TL VL NL (sPi S0)) (hS0D : sD S0 < 255)
    (hst : ∀ q < n, WStep (isN TL VL NL) (fun S c => mkSt (sD S) (mul7 (sPi S) (let7 LT c)))
      (fun c R dir e S => stepL HB GB TB TL VL nT W Wi c R dir e S) (rec FB sh wd) i Ri ft fd Wd q
        (Ss q) (Ss (q + 1)))
    (hft : ft < n) (hftN : isN TL VL NL (byteG Wd ft) = false) (hval : wv (lvE x) Wd n = 1) :
    InM LT LI TL VL NL (rPi Ri) ∧ FM φ HB GB x w Ri := by
  have hc := h.hc
  have hL := h.hL
  have hTV := hL.tv
  have hT255 : TL ≠ 255 := by have := hL.tl; have := hL.nl; omega
  have hV255 : VL ≠ 255 := by have := hL.vl; have := hL.nl; omega
  have hrec : ∀ q < n, isN TL VL NL (byteG Wd q) = false → ∃ R dir e,
      Ss (q + 1) = stepL HB GB TB TL VL nT W Wi (byteG Wd q) R dir e (Ss q) ∧ RecGood ND NO R ∧
      (q = ft ∧ R = Ri ∨ q ≠ ft ∧ InM LT LI TL VL NL (rPi R) ∧ FM φ HB GB x w R) := by
    intro q hq hN
    rcases hst q hq with ⟨hN', -⟩ | ⟨-, R, dir, e, he, hR⟩
    · rw [hN] at hN'
      exact absurd hN' Bool.false_ne_true
    rcases hR with ⟨hq1, rfl, -⟩ | ⟨hq1, k, hk, rfl, -⟩
    · exact ⟨_, dir, e, he, hRi, Or.inl ⟨hq1, rfl⟩⟩
    · obtain ⟨g1, g2, g3⟩ := hprev k hk
      exact ⟨_, dir, e, he, g1, Or.inr ⟨hq1, g2, g3⟩⟩
  have hNstep : ∀ q < n, isN TL VL NL (byteG Wd q) = true →
      Ss (q + 1) = mkSt (sD (Ss q)) (mul7 (sPi (Ss q)) (let7 LT (byteG Wd q))) := by
    intro q hq hN
    rcases hst q hq with ⟨-, he⟩ | ⟨hN', -⟩
    · exact he
    · rw [hN] at hN'
      exact absurd hN' (by decide)
  have hbad : ∀ q < n, sD (Ss q) = 255 → sD (Ss (q + 1)) = 255 := by
    intro q hq hS
    cases hN : isN TL VL NL (byteG Wd q)
    · obtain ⟨R, dir, e, he, hR, -⟩ := hrec q hq hN
      rw [he]
      exact step_bad hTV hT255 hV255 hR hND hS
    · rw [hNstep q hq hN, sD_mkSt (sD_lt _)]
      exact hS
  have hgood : ∀ q ≤ n, sD (Ss q) ≠ 255 := by
    intro q hq hS
    have key : ∀ d, q + d ≤ n → sD (Ss (q + d)) = 255 := by
      intro d
      induction d with
      | zero => exact fun _ => hS
      | succ d ih => exact fun hd => hbad (q + d) (by omega) (ih (by omega))
    have := key (n - q) (by omega)
    rw [show q + (n - q) = n by omega, hn] at this
    omega
  have hshape : ∀ q < n, isN TL VL NL (byteG Wd q) = false → ∃ R e,
      Shape HB GB TB TL VL nT W Wi (byteG Wd q) R e (Ss q) (Ss (q + 1)) ∧ RecGood ND NO R ∧
      (q = ft ∧ R = Ri ∨ q ≠ ft ∧ InM LT LI TL VL NL (rPi R) ∧ FM φ HB GB x w R) := by
    intro q hq hN
    obtain ⟨R, dir, e, he, hR, hk⟩ := hrec q hq hN
    have hne : stepL HB GB TB TL VL nT W Wi (byteG Wd q) R dir e (Ss q) ≠ bad := fun e' =>
      hgood (q + 1) (by omega) (by rw [he, e']; rfl)
    exact ⟨R, e, he ▸ stepL_shape hTV hT255 hV255 hne, hR, hk⟩
  have hNlt : ∀ q, isN TL VL NL (byteG Wd q) = true → byteG Wd q ≠ 255 := fun q hN e => by
    have := (isN_iff.1 hN).1
    have := hL.nl
    omega
  have hC : ∀ q ≤ n, C7 (sPi (Ss q)) := by
    intro q
    induction q with
    | zero => exact fun _ => h0 ▸ hS0.1
    | succ q ih =>
      intro hq
      cases hN : isN TL VL NL (byteG Wd q)
      · obtain ⟨R, e, hsh, hR, -⟩ := hshape q (by omega) hN
        exact step_C7 h hR hsh (ih (by omega))
      · rw [hNstep q (by omega) hN, sPi_mkSt (sD_lt _)]
        exact (mul7_sound hc (ih (by omega)) (letter_C7 hc hL hN)).1
  have hF : ∀ q ≤ ft, InM LT LI TL VL NL (sPi (Ss q)) := by
    intro q
    induction q with
    | zero => exact fun _ => h0 ▸ hS0
    | succ q ih =>
      intro hq
      cases hN : isN TL VL NL (byteG Wd q)
      · obtain ⟨R, e, hsh, hR, hk⟩ := hshape q (by omega) hN
        rcases hk with ⟨hq', -⟩ | ⟨-, hRm, -⟩
        · omega
        · exact step_fwd h hR hsh hRm (ih (by omega))
      · rw [hNstep q (by omega) hN, sPi_mkSt (sD_lt _)]
        exact InM_mul hc (ih (by omega)) (InM_letter hc hL hN)
  have hB : ∀ d, ft + 1 + d ≤ n → InM LT LI TL VL NL (sPi (Ss (n - d))) := by
    intro d
    induction d with
    | zero => exact fun _ => by rw [Nat.sub_zero, hn]; exact hS0
    | succ d ih =>
      intro hd
      have ihd := ih (by omega)
      obtain ⟨q, hq⟩ : ∃ q, q = n - (d + 1) := ⟨_, rfl⟩
      rw [show n - d = q + 1 by omega] at ihd
      rw [← hq]
      cases hN : isN TL VL NL (byteG Wd q)
      · obtain ⟨R, e, hsh, hR, hk⟩ := hshape q (by omega) hN
        rcases hk with ⟨hq', -⟩ | ⟨-, hRm, -⟩
        · omega
        · exact step_back h hR hsh hRm (hC q (by omega)) ihd
      · rw [hNstep q (by omega) hN, sPi_mkSt (sD_lt _)] at ihd
        exact InM_cancelR (InM_letter hc hL hN) ihd (hC q (by omega)) hc
  have hM : ∀ q ≤ n, InM LT LI TL VL NL (sPi (Ss q)) := by
    intro q hq
    by_cases h1 : q ≤ ft
    · exact hF q h1
    · have := hB (n - q) (by omega)
      rwa [Nat.sub_sub_self hq] at this
  obtain ⟨R0, e0, hsh0, hR0, hk0⟩ := hshape ft hft hftN
  have hR0i : R0 = Ri := by
    rcases hk0 with ⟨-, e⟩ | ⟨hne, -⟩
    · exact e
    · exact absurd rfl hne
  subst hR0i
  have hRm := step_own h hR0 hsh0 (hM ft (by omega)) (hM (ft + 1) (by omega))
  refine ⟨hRm, ?_⟩
  have hchain := chain_own (N := Ncl x TL VL NL) (fun q => rep φ w (Ss q))
    (fun q => lvE x (byteG Wd q)) hft ?_ hval (by simp only [hn, h0])
  · exact (step_sem h hR0 hsh0 w hRm (hM ft (by omega))).1 hchain
  · intro q hq hqf
    cases hN : isN TL VL NL (byteG Wd q)
    · obtain ⟨R, e, hsh, hR, hk⟩ := hshape q hq hN
      rcases hk with ⟨hq', -⟩ | ⟨-, hRm', hFM⟩
      · exact absurd hq' hqf
      · exact (step_sem h hR hsh w hRm' (hM q (by omega))).2 hFM
    · apply RelT.of_eq
      rw [hNstep q hq hN]
      unfold rep
      rw [sD_mkSt (sD_lt _), sPi_mkSt (sD_lt _),
        rc_mul hc φ (hM q (by omega)) (InM_letter hc hL hN), rc_letter hc hL φ h.hφ hN, lvE,
        ite_eq_right (hNlt q hN), mul_assoc]

end Walk

theorem treeOK_spec {HB GB : ℕ → ℕ} {nx R : ℕ} (h : treeOK HB GB nx R = true) :
    0 < rJ R ∧ rDp R = nx ∧ rD R < nx ∧ rPi R = ONE7 := by
  unfold treeOK at h
  obtain ⟨e1, r⟩ := andL_iff.1 h
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, -⟩ := andL_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, Nat.blt_eq.mp e3, Nat.eq_of_beq_eq_true e4⟩

theorem axiomOK_spec {HB : ℕ → ℕ} {nH Jf R : ℕ} (h : axiomOK HB nH Jf R = true) :
    rD R = 0 ∧ rJ R = 0 ∧ rDp R = 0 ∧ ∃ a < nH, ∃ b < nH, rPi R = mul7 (mat HB a) (mat HB b) := by
  unfold axiomOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andL_iff.1 h
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, r⟩ := andL_iff.1 r
  obtain ⟨e5, e6⟩ := andL_iff.1 r
  exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3, _,
    Nat.blt_eq.mp e4, _, Nat.blt_eq.mp e5, Nat.eq_of_beq_eq_true e6⟩

theorem walkOK_spec {FB HB GB TB WD : ℕ → ℕ} {sh wd ND nH nT nW W Wi i Jf R : ℕ}
    (h : walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi i Jf R = true) :
    ∃ ww < nW, ∃ D0 < ND, ∃ a < nH, ∃ b < nH, ∃ ft fd J,
      ft < bits (WD ww) 2 10 ∧ isN TL VL NL (byte (Nat.shiftRight (WD ww) 12) ft) = false ∧
      walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi i R ft fd (Nat.shiftRight (WD ww) 12)
        (bits (WD ww) 2 10) (bits (WD ww) 2 10) J (mkSt D0 (mul7 (mat HB a) (mat HB b))) =
        mkSt D0 (mul7 (mat HB a) (mat HB b)) := by
  unfold walkOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andL_iff.1 h
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, r⟩ := andL_iff.1 r
  obtain ⟨e5, r⟩ := andL_iff.1 r
  obtain ⟨e6, e7⟩ := andL_iff.1 r
  exact ⟨_, Nat.blt_eq.mp e1, _, Nat.blt_eq.mp e2, _, Nat.blt_eq.mp e3, _, Nat.blt_eq.mp e4, _, _, _,
    Nat.blt_eq.mp e5, (notL_eq _).1 e6, Nat.eq_of_beq_eq_true e7⟩

section Facts

variable {HB GB TB FB WD : ℕ → ℕ} {NO nT W Wi ND sh wd nH nW NF : ℕ} {x : ℕ → G}
  {φ : Mg LT LI TL VL NL →* G}

abbrev FOK (HB GB TB FB WD : ℕ → ℕ) (LT TL VL NL ND NO nH nT nW W Wi sh wd : ℕ) :=
  FactOK (recOK ND NO) (treeOK HB GB) (axiomOK HB nH)
    (fun i Jf R => walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi i Jf R) (rec FB sh wd)

theorem exists_w {nxf : ℕ → ℕ}
    (hf : ∀ i < NF, FOK HB GB TB FB WD LT TL VL NL ND NO nH nT nW W Wi sh wd i (nxf i) (nxf (i + 1))) :
    ∃ w : ℕ → G, w 0 = 1 ∧ ∀ i < NF, nxf (i + 1) = nxf i + 1 →
      w (rDp (rec FB sh wd i)) = w (rD (rec FB sh wd i)) * uv φ HB GB x (rJ (rec FB sh wd i)) := by
  have htree : ∀ i < NF, nxf (i + 1) = nxf i + 1 → treeOK HB GB (nxf i) (rec FB sh wd i) = true := by
    intro i hi ht
    rcases (hf i hi).2 with ⟨-, h⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact h
    · omega
    · omega
  refine exists_tree NF (fun i => nxf (i + 1) = nxf i + 1) (fun i => rD (rec FB sh wd i))
    (fun i => rDp (rec FB sh wd i)) (fun i => uv φ HB GB x (rJ (rec FB sh wd i)))
    (fun i hi ht => ?_) (fun i hi i' hi' ht ht' e => ?_)
  · obtain ⟨-, h2, h3, -⟩ := treeOK_spec (htree i hi ht)
    show rD (rec FB sh wd i) < rDp (rec FB sh wd i)
    omega
  · exact tree_unique hf rDp (fun nx R h => (treeOK_spec h).2.1) hi hi' ht ht' e

variable (h : SCtx HB GB TB LT LI TL VL NL NO nT W Wi x φ) (hND : ND < 255)
  (hφN : ∀ m, φ m ∈ Ncl x TL VL NL)
  (hhdr : ∀ k < nH, InM LT LI TL VL NL (mat HB k))
  (hwords : ∀ ww < nW, wv (lvE x) (Nat.shiftRight (WD ww) 12) (bits (WD ww) 2 10) = 1)
include h hND hφN hhdr hwords

theorem facts_mean {nxf : ℕ → ℕ}
    (hf : ∀ i < NF, FOK HB GB TB FB WD LT TL VL NL ND NO nH nT nW W Wi sh wd i (nxf i) (nxf (i + 1)))
    (w : ℕ → G) (hw0 : w 0 = 1) (hwt : ∀ i < NF, nxf (i + 1) = nxf i + 1 →
      w (rDp (rec FB sh wd i)) = w (rD (rec FB sh wd i)) * uv φ HB GB x (rJ (rec FB sh wd i))) :
    ∀ i < NF, RecGood ND NO (rec FB sh wd i) ∧ InM LT LI TL VL NL (rPi (rec FB sh wd i)) ∧
      FM φ HB GB x w (rec FB sh wd i) := by
  have hc := h.hc
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨hrk, hk⟩ := hf i hi
    have hR := recOK_spec hrk
    refine ⟨hR, ?_⟩
    rcases hk with ⟨ht, htk⟩ | ⟨-, Jf, hax⟩ | ⟨-, Jf, hwk⟩
    · obtain ⟨-, -, -, hP⟩ := treeOK_spec htk
      refine ⟨hP ▸ InM_one hc, ?_⟩
      unfold FM
      rw [hP, rc_one hc φ, mul_one, hwt i hi ht]
      exact RelT.refl _
    · obtain ⟨e1, e2, e3, a, ha, b, hb, hP⟩ := axiomOK_spec hax
      have hm : InM LT LI TL VL NL (rPi (rec FB sh wd i)) := hP ▸ InM_mul hc (hhdr a ha) (hhdr b hb)
      refine ⟨hm, ?_⟩
      unfold FM
      rw [e1, e2, e3, uv, ite_eq_left rfl, hw0, one_mul, one_mul]
      unfold RelT rc
      rw [one_mul]
      exact (Ncl x TL VL NL).inv_mem (hφN _)
    · obtain ⟨ww, hww, D0, hD0, a, ha, b, hb, ft, fd, J, hft, hftN, hwalk⟩ := walkOK_spec hwk
      rw [walkGo_eq] at hwalk
      set n := bits (WD ww) 2 10
      set S0 := mkSt D0 (mul7 (mat HB a) (mat HB b))
      have hD0' : D0 < 256 := by omega
      have hS0bad : S0 ≠ bad := bad_ne (by omega)
      rcases walkG_spec _ _ _ _ _ _ _ _ _ _ _ _ n le_rfl J S0 with hb' | ⟨Ss, h0, hn, hst⟩
      · rw [hwalk] at hb'
        exact absurd hb' hS0bad
      rw [Nat.sub_self] at h0
      rw [hwalk] at hn
      have hS0m : InM LT LI TL VL NL (sPi S0) := by
        rw [sPi_mkSt hD0']
        exact InM_mul hc (hhdr a ha) (hhdr b hb)
      have hS0D : sD S0 < 255 := by
        rw [sD_mkSt hD0']
        omega
      exact walk_sem h hND w (fun k hk => ih k hk (by omega)) hR h0 hn hS0m hS0D
        (fun q hq => hst q (by omega) hq) hft hftN (hwords ww hww)

end Facts

end CFSG.Certificates.DS5

end
