module

public import CFSG.Certificates.Kernel.McLDceStep
import CFSG.Certificates.Kernel.Co1DceLemmas
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat CFSG.Certificates.LCE

set_option exponentiation.threshold 700

@[expose] noncomputable def fR (FB : ℕ → ℕ) (h : ℕ) : ℕ := McL.Dce.rec FB (nat_lit 6) McL.Dce.RW h

@[expose] def WStep (FB HB GB TB : ℕ → ℕ) (LT TL NL nT i Ri ft fd Wd q S A S' A' : ℕ) : Prop :=
  (McL.Dce.isN TL NL (McL.Dce.byte Wd q) = true ∧
      S' = McL.Dce.mkSt (McL.Dce.sD S) (mul25 (McL.Dce.sPi S) (McL.Dce.let25 LT (McL.Dce.byte Wd q))) ∧
      A' = A) ∨
    (McL.Dce.isN TL NL (McL.Dce.byte Wd q) = false ∧ ∃ R dir e,
      S' = McL.Dce.stepL HB GB TB TL nT (McL.Dce.byte Wd q) R dir e S ∧ A' = mul25 A (mR R dir) ∧
      (q = ft ∧ R = Ri ∧ dir = fd ∨ q ≠ ft ∧ ∃ h < i, R = fR FB h))

@[expose] noncomputable def wBody (FB HB GB TB : ℕ → ℕ) (LT TL NL nT i Ri ft fd Wd n k : ℕ)
    (ih : ℕ → ℕ → ℕ → ℕ) (J S A : ℕ) : ℕ :=
  (fun q => (fun c =>
      Bool.rec (motive := fun _ => Nat)
        (ih J (McL.Dce.mkSt (McL.Dce.sD S) (mul25 (McL.Dce.sPi S) (McL.Dce.let25 LT c))) A)
        ((fun own => (fun h => (fun R dir =>
            Bool.rec (motive := fun _ => Nat) McL.Dce.bad
              (Loop.strictN (McL.Dce.stepL HB GB TB TL nT c R dir
                  (Bool.rec (motive := fun _ => Nat) (McL.Dce.bits J (nat_lit 21) (nat_lit 17))
                    (McL.Dce.bits J (nat_lit 0) (nat_lit 17)) own) S)
                (fun S2 => ih (Nat.shiftRight J (McL.Dce.posBits TL c own)) S2
                  (mul25 A (Bool.rec (motive := fun _ => Nat) (McL.Dce.rN R) (McL.Dce.rNI R)
                    (Nat.beq dir (nat_lit 1))))))
              (Th.orB own (Nat.blt h i)))
            (Bool.rec (motive := fun _ => Nat) (McL.Dce.rec FB (nat_lit 6) McL.Dce.RW h) Ri own)
            (Bool.rec (motive := fun _ => Nat) (Nat.land J (nat_lit 1)) fd own))
          (McL.Dce.bits J (nat_lit 1) (nat_lit 20)))
         (Nat.beq q ft))
        (McL.Dce.notB (McL.Dce.isN TL NL c)))
      (McL.Dce.byte Wd q)) (Nat.sub n (Nat.succ k))

theorem walkGo_spec (FB HB GB TB : ℕ → ℕ) (LT TL NL nT i Ri ft fd Wd n : ℕ) : ∀ k, k ≤ n →
    ∀ J S A, McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k J S A = McL.Dce.bad ∨
      ∃ Ss As : ℕ → ℕ, Ss (n - k) = S ∧ As (n - k) = A ∧
        McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k J S A =
          Nat.lor (Ss n) (Nat.shiftLeft (As n) 640) ∧
        ∀ q, n - k ≤ q → q < n →
          WStep FB HB GB TB LT TL NL nT i Ri ft fd Wd q (Ss q) (As q) (Ss (q + 1)) (As (q + 1))
  | 0, _, J, S, A => Or.inr ⟨fun _ => S, fun _ => A, rfl, rfl, rfl,
      fun q h1 h2 => absurd h2 (by omega)⟩
  | k + 1, hk, J, S, A => by
    have ih := walkGo_spec FB HB GB TB LT TL NL nT i Ri ft fd Wd n k (by omega)
    have ext : ∀ S' A', WStep FB HB GB TB LT TL NL nT i Ri ft fd Wd (n - (k + 1)) S A S' A' →
        ∀ J', (McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k J' S' A' = McL.Dce.bad ∨
          ∃ Ss As : ℕ → ℕ, Ss (n - k) = S' ∧ As (n - k) = A' ∧
            McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k J' S' A' =
              Nat.lor (Ss n) (Nat.shiftLeft (As n) 640) ∧
            ∀ q, n - k ≤ q → q < n →
              WStep FB HB GB TB LT TL NL nT i Ri ft fd Wd q (Ss q) (As q) (Ss (q + 1))
                (As (q + 1))) →
        McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k J' S' A' = McL.Dce.bad ∨
          ∃ Ss As : ℕ → ℕ, Ss (n - (k + 1)) = S ∧ As (n - (k + 1)) = A ∧
            McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k J' S' A' =
              Nat.lor (Ss n) (Nat.shiftLeft (As n) 640) ∧
            ∀ q, n - (k + 1) ≤ q → q < n →
              WStep FB HB GB TB LT TL NL nT i Ri ft fd Wd q (Ss q) (As q) (Ss (q + 1))
                (As (q + 1)) := by
      intro S' A' hst J' h
      rcases h with h | ⟨Ss, As, h0, h0A, hn, hs⟩
      · exact Or.inl h
      refine Or.inr ⟨fun q => if q = n - (k + 1) then S else Ss q,
        fun q => if q = n - (k + 1) then A else As q, by simp, by simp, ?_, ?_⟩
      · simp only []
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact hn
      · intro q hq1 hq2
        simp only []
        rcases Nat.eq_or_lt_of_le hq1 with rfl | hq1
        · rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
            show n - (k + 1) + 1 = n - k by omega, h0, h0A]
          exact hst
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega)]
          exact hs q (by omega) hq2
    change wBody FB HB GB TB LT TL NL nT i Ri ft fd Wd n k
      (McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k) J S A = McL.Dce.bad ∨
        ∃ Ss As : ℕ → ℕ, Ss (n - (k + 1)) = S ∧ As (n - (k + 1)) = A ∧
          wBody FB HB GB TB LT TL NL nT i Ri ft fd Wd n k
            (McL.Dce.walkGo FB HB GB TB LT TL NL nT i Ri ft fd Wd n k) J S A =
            Nat.lor (Ss n) (Nat.shiftLeft (As n) 640) ∧
          ∀ q, n - (k + 1) ≤ q → q < n →
            WStep FB HB GB TB LT TL NL nT i Ri ft fd Wd q (Ss q) (As q) (Ss (q + 1)) (As (q + 1))
    unfold wBody
    simp only []
    have eq : Nat.sub n (Nat.succ k) = n - (k + 1) := rfl
    rw [eq]
    cases hN : McL.Dce.isN TL NL (McL.Dce.byte Wd (n - (k + 1)))
    ·
      dsimp only [McL.Dce.notB]
      cases hc : Th.orB (Nat.beq (n - (k + 1)) ft) (Nat.blt (McL.Dce.bits J 1 20) i)
      · exact Or.inl rfl
      · dsimp only
        rw [strictN_eq]
        apply ext _ _ _ _ (ih _ _ _)
        refine Or.inr ⟨hN, _, _, _, rfl, rfl, ?_⟩
        cases ho : Nat.beq (n - (k + 1)) ft
        · rw [ho] at hc
          change Nat.blt (McL.Dce.bits J 1 20) i = true at hc
          rw [Nat.blt_eq] at hc
          exact Or.inr ⟨Nat.ne_of_beq_eq_false ho, _, hc, rfl⟩
        · exact Or.inl ⟨Nat.eq_of_beq_eq_true ho, rfl, rfl⟩
    ·
      dsimp only [McL.Dce.notB]
      exact ext _ _ (Or.inl ⟨hN, rfl, rfl⟩) _ (ih _ _ _)

theorem recOK_spec {ND NO R : ℕ} (h : McL.Dce.recOK ND NO R = true) :
    McL.Dce.rD R < ND ∧ McL.Dce.rDp R < ND ∧ McL.Dce.rJ R ≤ NO ∧
      mul25 (McL.Dce.rPi R) (McL.Dce.rFI R) = ident ∧ mul25 (McL.Dce.rN R) (McL.Dce.rNI R) = ident := by
  unfold McL.Dce.recOK at h
  simp only [andB_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  exact h

theorem walkOK_spec {FB HB GB TB WD : ℕ → ℕ} {LT TL NL ND nH nT nW i Jf R : ℕ}
    (h : McL.Dce.walkOK FB HB GB TB WD LT TL NL ND nH nT nW i Jf R = true) :
    ∃ w < nW, ∃ D0 < ND, ∃ x < nH, ∃ b < nH, ∃ ft fd J : ℕ, ft < LceS.wLen (WD w) ∧
      McL.Dce.isN TL NL (McL.Dce.byte (LceS.wWord (WD w)) ft) = false ∧
      McL.Dce.walkGo FB HB GB TB LT TL NL nT i R ft fd (LceS.wWord (WD w)) (LceS.wLen (WD w))
          (LceS.wLen (WD w)) J (McL.Dce.mkSt D0 (mul25 (McL.Dce.mat HB x) (McL.Dce.mat HB b)))
          ident =
        Nat.lor (McL.Dce.mkSt D0 (mul25 (McL.Dce.mat HB x) (McL.Dce.mat HB b)))
          (Nat.shiftLeft ident 640) := by
  unfold McL.Dce.walkOK at h
  beta_reduce at h
  simp only [andB_iff, Nat.blt_eq, notB_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨_, h1, _, h2, _, h3, _, h4, _, _, _, h5, h6, h7⟩

theorem lor_dec {a b a' b' : ℕ} (ha : a < 2 ^ 640) (ha' : a' < 2 ^ 640)
    (h : Nat.lor a (Nat.shiftLeft b 640) = Nat.lor a' (Nat.shiftLeft b' 640)) :
    a = a' ∧ b = b' := by
  rw [Co1D.lor_shl ha, Co1D.lor_shl ha'] at h
  have h1 : a = a' := by
    have := congrArg (· % 2 ^ 640) h
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
    exact this
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 640) (Nat.add_left_cancel h)⟩

theorem lor_ge {a b : ℕ} (ha : a < 2 ^ 640) (hb : 0 < b) :
    2 ^ 640 ≤ Nat.lor a (Nat.shiftLeft b 640) := by
  rw [Co1D.lor_shl ha]
  exact Nat.le_trans (Nat.le_mul_of_pos_left _ hb) (Nat.le_add_left _ _)

theorem WStep_lt {FB HB GB TB : ℕ → ℕ} {LT TL NL nT i Ri ft fd Wd q S A S' A' : ℕ}
    (h : WStep FB HB GB TB LT TL NL nT i Ri ft fd Wd q S A S' A') : S' < 2 ^ 640 := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, R, dir, e, rfl, -, -⟩
  · exact mkSt_lt (sD_lt _) (mul25_lt _ _)
  · rcases @stepL_cases HB GB TB TL nT (McL.Dce.byte Wd q) R dir e S with e1 | e1
    · rw [e1]
      change 255 < 2 ^ 640
      norm_num
    · exact LStep_lt e1

section Walk

variable {G : Type*} [Group G]

@[expose] def FOK {LT TL NL : ℕ} (φ : Mg LT TL NL →* G) (gen : ℕ → G) (HB GB : ℕ → ℕ)
    (ND NO : ℕ) (w : ℕ → G) (R : ℕ) : Prop :=
  McL.Dce.recOK ND NO R = true ∧ InM LT TL NL (McL.Dce.rPi R) ∧ InM LT TL NL (McL.Dce.rN R) ∧
    FM φ gen HB GB w R

@[expose] noncomputable def Ev {LT TL NL : ℕ} (φ : Mg LT TL NL →* G) (w : ℕ → G) (S A : ℕ) : G :=
  rc φ A * (w (McL.Dce.sD S) * rc φ (McL.Dce.sPi S))

theorem wv_succ (gen : ℕ → G) (W q : ℕ) :
    wv gen W (q + 1) = wv gen W q * lv gen (McL.Dce.byte W q) := by
  unfold wv
  rw [List.range_succ, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem wv_zero (gen : ℕ → G) (W : ℕ) : wv gen W 0 = 1 := by
  simp [wv]

variable {gen : ℕ → G} {LT LI TL NL : ℕ} (φ : Mg LT TL NL →* G)
  {FB HB GB TB WD : ℕ → ℕ} {ND NO nH nT nW : ℕ}

theorem walk_mean (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
    (hH : ∀ h < nH, InM LT TL NL (McL.Dce.mat HB h))
    (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident)
    (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) ∧
      gen TL * rc φ (McL.Dce.tSig HB TB e) * gen TL = rc φ (tPsi HB TB e))
    (ht : gen TL * gen TL = 1) (hND : ND ≤ 256)
    (hwords : ∀ w < nW, wv gen (LceS.wWord (WD w)) (LceS.wLen (WD w)) = 1)
    {w : ℕ → G} {i Jf : ℕ}
    (hprev : ∀ h < i, FOK φ gen HB GB ND NO w (fR FB h))
    (hrec : McL.Dce.recOK ND NO (fR FB i) = true)
    (hW : McL.Dce.walkOK FB HB GB TB WD LT TL NL ND nH nT nW i Jf (fR FB i) = true) :
    FOK φ gen HB GB ND NO w (fR FB i) := by
  obtain ⟨-, -, hrJ, hrPF, hrNN⟩ := recOK_spec hrec
  have hS2 : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) :=
    fun e he => ⟨(hS e he).1, (hS e he).2.1⟩
  have hT255 : TL ≠ 255 := by omega
  have hL : ∀ c, McL.Dce.isN TL NL c = true → c < 3 ∧ InM LT TL NL (McL.Dce.let25 LT c) ∧
      rc φ (McL.Dce.let25 LT c) = gen c := by
    intro c hc
    have := isN_iff.1 hc
    have h3 : c < 3 := by omega
    exact ⟨h3, InM_letter hTL hNL hlet h3, rc_letter φ hφ hTL hNL hlet h3⟩
  obtain ⟨wd, hwd, D0, hD0, x, hx, b, hb, ft, fd, J, hft, hnN, hgo⟩ := walkOK_spec hW
  have hval := hwords wd hwd
  generalize LceS.wWord (WD wd) = W at hnN hgo hval
  generalize LceS.wLen (WD wd) = n at hft hgo hval
  have hX : InM LT TL NL (mul25 (McL.Dce.mat HB x) (McL.Dce.mat HB b)) :=
    InM_mul (hH x hx) (hH b hb)
  have hXlt := mul25_lt (McL.Dce.mat HB x) (McL.Dce.mat HB b)
  generalize mul25 (McL.Dce.mat HB x) (McL.Dce.mat HB b) = X at hX hXlt hgo
  have hD0' : D0 < 256 := by omega
  have hS0lt : McL.Dce.mkSt D0 X < 2 ^ 640 := mkSt_lt hD0' hXlt
  rcases walkGo_spec FB HB GB TB LT TL NL nT i (fR FB i) ft fd W n n le_rfl J
      (McL.Dce.mkSt D0 X) ident with hbad | ⟨Ss, As, h0S, h0A, hend, hst⟩
  · exfalso
    have h1 := lor_ge (b := ident) hS0lt (Nat.pos_of_ne_zero ident_ne_zero)
    rw [← hgo, hbad] at h1
    change 2 ^ 640 ≤ 255 at h1
    norm_num at h1
  rw [Nat.sub_self] at h0S h0A
  have hSnlt : Ss n < 2 ^ 640 := by
    have e : n = (n - 1) + 1 := by omega
    rw [e]
    exact WStep_lt (hst (n - 1) (by omega) (by omega))
  obtain ⟨hSn, hAn⟩ := lor_dec hSnlt hS0lt (hend.symm.trans hgo)
  have hnz : ∀ d ≤ n, McL.Dce.sPi (Ss (n - d)) ≠ 0 := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, hSn, sPi_mkSt hD0']
      exact inM_ne_zero hX
    | succ d ih =>
      intro hd h0
      have hq : n - (d + 1) + 1 = n - d := by omega
      apply ih (by omega)
      rw [← hq]
      rcases hst (n - (d + 1)) (by omega) (by omega) with ⟨-, e1, -⟩ | ⟨-, R, dir, e, e1, -, -⟩
      · rw [e1, sPi_mkSt (sD_lt _), h0, mul25_zero_left]
      · rw [e1]
        rcases @stepL_cases HB GB TB TL nT (McL.Dce.byte W (n - (d + 1))) R dir e
            (Ss (n - (d + 1))) with e2 | e2
        · rw [e2]
          rfl
        · exact step_zero hS2 e2 h0
  have hnz' : ∀ q ≤ n, McL.Dce.sPi (Ss q) ≠ 0 := fun q hq => by
    have := hnz (n - q) (by omega)
    rwa [Nat.sub_sub_self hq] at this
  have hgood : ∀ q < n, (McL.Dce.isN TL NL (McL.Dce.byte W q) = true ∧
      Ss (q + 1) = McL.Dce.mkSt (McL.Dce.sD (Ss q))
        (mul25 (McL.Dce.sPi (Ss q)) (McL.Dce.let25 LT (McL.Dce.byte W q))) ∧ As (q + 1) = As q) ∨
      (∃ R dir e, LStep HB GB TB TL nT (McL.Dce.byte W q) R dir e (Ss q) (Ss (q + 1)) ∧
        As (q + 1) = mul25 (As q) (mR R dir) ∧
        (q = ft ∧ R = fR FB i ∧ dir = fd ∨ q ≠ ft ∧ ∃ h < i, R = fR FB h)) := by
    intro q hq
    rcases hst q (by omega) hq with h1 | ⟨-, R, dir, e, e1, e2, e3⟩
    · exact Or.inl h1
    · right
      refine ⟨R, dir, e, ?_, e2, e3⟩
      rcases @stepL_cases HB GB TB TL nT (McL.Dce.byte W q) R dir e (Ss q) with e4 | e4
      · exfalso
        apply hnz' (q + 1) (by omega)
        rw [e1, e4]
        rfl
      · rw [e1]
        exact e4
  have hfwd : ∀ q ≤ ft, InM LT TL NL (McL.Dce.sPi (Ss q)) ∧ InM LT TL NL (As q) := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [h0S, h0A, sPi_mkSt hD0']
      exact ⟨hX, InM_ident⟩
    | succ q ih =>
      intro hq
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rcases hgood q (by omega) with ⟨hN, e1, e2⟩ |
          ⟨R, dir, e, hl, e2, ⟨hq', -⟩ | ⟨-, h, hh, rfl⟩⟩
      · rw [e1, e2, sPi_mkSt (sD_lt _)]
        exact ⟨InM_mul ih1 (hL _ hN).2.1, ih2⟩
      · omega
      · obtain ⟨hr, hp, hn, -⟩ := hprev h hh
        obtain ⟨-, -, hJ, hPF, hNN⟩ := recOK_spec hr
        rw [e2]
        exact ⟨(step_mean hG hS ht hT255 (w := w) hl hJ hPF hNN hp hn ih1).1,
          InM_mul ih2 (mR_inM hn hNN)⟩
  have hbwd : ∀ d, ft + 1 + d ≤ n →
      InM LT TL NL (McL.Dce.sPi (Ss (n - d))) ∧ InM LT TL NL (As (n - d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, hSn, hAn, sPi_mkSt hD0']
      exact ⟨hX, InM_ident⟩
    | succ d ih =>
      intro hd
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hq : n - (d + 1) + 1 = n - d := by omega
      rw [← hq] at ih1 ih2
      rcases hgood (n - (d + 1)) (by omega) with ⟨hN, e1, e2⟩ |
          ⟨R, dir, e, hl, e2, ⟨hq', -⟩ | ⟨-, h, hh, rfl⟩⟩
      · rw [e1, sPi_mkSt (sD_lt _)] at ih1
        rw [e2] at ih2
        exact ⟨InM_cancel_right (hL _ hN).2.1 ih1, ih2⟩
      · omega
      · obtain ⟨hr, hp, hn, -⟩ := hprev h hh
        obtain ⟨-, -, hJ, hPF, hNN⟩ := recOK_spec hr
        rw [e2] at ih2
        exact ⟨step_back hG hS2 hl hJ hPF hp ih1, InM_cancel_right (mR_inM hn hNN) ih2⟩
  have hall : ∀ q ≤ n, InM LT TL NL (McL.Dce.sPi (Ss q)) ∧ InM LT TL NL (As q) := by
    intro q hq
    by_cases h1 : q ≤ ft
    · exact hfwd q h1
    · have := hbwd (n - q) (by omega)
      rwa [Nat.sub_sub_self hq] at this
  rcases hgood ft hft with ⟨hN, -, -⟩ | ⟨R, dir, e, hl, e2, ⟨-, hR, -⟩ | ⟨hne, -⟩⟩
  · rw [hN] at hnN
    exact absurd hnN (by decide)
  swap
  · exact absurd rfl hne
  subst hR
  obtain ⟨hp0, ha0⟩ := hall ft (by omega)
  obtain ⟨hp1, ha1⟩ := hall (ft + 1) (by omega)
  have hRP := step_own hG hS2 hl hrJ hrPF hp0 hp1
  have hm : InM LT TL NL (mR (fR FB i) dir) := by
    rw [e2] at ha1
    exact InM_cancel_left ha0 ha1
  have hRN : InM LT TL NL (McL.Dce.rN (fR FB i)) := by
    unfold mR at hm
    cases hb : Nat.beq dir 1
    · rw [hb] at hm
      exact hm
    · rw [hb] at hm
      exact InM_invL hm hrNN
  refine ⟨hrec, hRP, hRN, ?_⟩
  have hrel : ∀ q < n, q ≠ ft →
      Ev φ w (Ss q) (As q) * lv gen (McL.Dce.byte W q) = Ev φ w (Ss (q + 1)) (As (q + 1)) := by
    intro q hq hqf
    obtain ⟨hp, ha⟩ := hall q (by omega)
    have e0 : Ev φ w (Ss q) (As q) * lv gen (McL.Dce.byte W q) = rc φ (As q) *
        (w (McL.Dce.sD (Ss q)) * rc φ (McL.Dce.sPi (Ss q)) * lv gen (McL.Dce.byte W q)) := by
      unfold Ev
      group
    rw [e0]
    rcases hgood q hq with ⟨hN, e1, e3⟩ | ⟨R, dir, e, hl', e3, ⟨hq', -⟩ | ⟨-, h, hh, rfl⟩⟩
    · obtain ⟨h3, hLm, hLr⟩ := hL _ hN
      unfold Ev
      rw [e1, e3, sD_mkSt (sD_lt _), sPi_mkSt (sD_lt _), rc_mul φ hp hLm, hLr, lv,
        ite_eq_right (by omega)]
      group
    · exact absurd hq' hqf
    · obtain ⟨hr, hRp, hRn, hF⟩ := hprev h hh
      obtain ⟨-, -, hJ, hPF, hNN⟩ := recOK_spec hr
      have hsr := ((step_mean hG hS ht hT255 (w := w) hl' hJ hPF hNN hRp hRn hp).2).2 hF
      unfold SR at hsr
      rw [hsr]
      unfold Ev
      rw [e3, rc_mul φ ha (mR_inM hRn hNN)]
      group
  have c1 : ∀ q ≤ ft, Ev φ w (Ss 0) (As 0) * wv gen W q = Ev φ w (Ss q) (As q) := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [wv_zero, mul_one]
    | succ q ih =>
      intro hq
      rw [wv_succ, ← mul_assoc, ih (by omega), hrel q (by omega) (by omega)]
  have c2 : ∀ d, ft + 1 + d ≤ n → Ev φ w (Ss (ft + 1)) (As (ft + 1)) * (wv gen W (ft + 1))⁻¹ *
      wv gen W (ft + 1 + d) = Ev φ w (Ss (ft + 1 + d)) (As (ft + 1 + d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.add_zero, inv_mul_cancel_right]
    | succ d ih =>
      intro hd
      rw [← Nat.add_assoc, wv_succ gen W (ft + 1 + d), ← mul_assoc, ih (by omega),
        hrel _ (by omega) (by omega)]
  have f2 := c2 (n - (ft + 1)) (by omega)
  rw [show ft + 1 + (n - (ft + 1)) = n by omega, hval, mul_one, hSn, hAn, ← h0S, ← h0A] at f2
  have f1 := c1 ft le_rfl
  have key : Ev φ w (Ss ft) (As ft) * lv gen (McL.Dce.byte W ft) =
      Ev φ w (Ss (ft + 1)) (As (ft + 1)) := by
    rw [← f1, mul_assoc, ← wv_succ, ← f2, inv_mul_cancel_right]
  have key2 : w (McL.Dce.sD (Ss ft)) * rc φ (McL.Dce.sPi (Ss ft)) * lv gen (McL.Dce.byte W ft) =
      rc φ (mR (fR FB i) dir) * w (McL.Dce.sD (Ss (ft + 1))) * rc φ (McL.Dce.sPi (Ss (ft + 1))) := by
    apply mul_left_cancel (a := rc φ (As ft))
    unfold Ev at key
    rw [e2, rc_mul φ ha0 hm] at key
    calc _ = rc φ (As ft) * (w (McL.Dce.sD (Ss ft)) * rc φ (McL.Dce.sPi (Ss ft))) *
          lv gen (McL.Dce.byte W ft) := by group
      _ = _ := key
      _ = _ := by group
  exact ((step_mean hG hS ht hT255 (w := w) hl hrJ hrPF hrNN hRP hRN hp0).2).1 key2

end Walk

end CFSG.Certificates.McLD

end
