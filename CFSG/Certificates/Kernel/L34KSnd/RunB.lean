module

public import Certificates.Data.Kernel.L34KB
public import CFSG.Certificates.Kernel.L34KSnd.Run
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.L34KSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (fget)

@[expose] noncomputable def pointRecB (ng : Nat) (st : Nat → Nat → Nat) (eqb : Nat → Nat → Nat → Bool)
    (T E : Nat → Nat) (ew i r : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (genStepB st eqb T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c)
      ih) r

section Run

variable {ng : Nat} {st : Nat → Nat → Nat} {eqb : Nat → Nat → Nat → Bool} {T E : Nat → Nat}
  {ew : Nat} {P : Nat → Prop}

theorem genStepB_eq (t row k c : Nat) :
    genStepB st eqb T ew t row k c =
      if c = 0 then 0
      else if fget row k ew < c then (if eqb k t (T (fget row k ew)) = true then c else 0)
      else if fget row k ew = c then (if T c = st k t then c + 1 else 0) else 0 := by
  unfold genStepB
  simp only [strictN_app, nIf_ite, Nat.beq_eq, Nat.blt_eq]

theorem genStepB_spec {k t row c r : Nat} (hst : ∀ t, P t → P (st k t))
    (heq : ∀ t y, P t → P y → eqb k t y = true → y = st k t) (hP : P t)
    (hI : ∀ j < c, P (T j)) (hr : genStepB st eqb T ew t row k c = r) (h0 : r ≠ 0) :
    genStepW st T ew t row k c = r ∧ ∀ j < r, P (T j) := by
  rw [genStepB_eq] at hr
  rw [genStepW_eq]
  generalize fget row k ew = q at hr ⊢
  by_cases hc : c = 0
  · rw [if_pos hc] at hr
    exact absurd hr.symm h0
  rw [if_neg hc] at hr ⊢
  by_cases hq : q < c
  · rw [if_pos hq] at hr ⊢
    by_cases hb : eqb k t (T q) = true
    · rw [if_pos hb] at hr
      rw [if_pos (heq t (T q) hP (hI q hq) hb)]
      subst hr
      exact ⟨rfl, hI⟩
    · rw [if_neg hb] at hr
      exact absurd hr.symm h0
  · rw [if_neg hq] at hr ⊢
    by_cases hqc : q = c
    · rw [if_pos hqc] at hr ⊢
      by_cases hT : T c = st k t
      · rw [if_pos hT] at hr ⊢
        subst hr
        refine ⟨rfl, fun j hj => ?_⟩
        rcases Nat.lt_or_ge j c with a | a
        · exact hI j a
        · have e : j = c := by omega
          subst e
          rw [hT]
          exact hst t hP
      · rw [if_neg hT] at hr
        exact absurd hr.symm h0
    · rw [if_neg hqc] at hr
      exact absurd hr.symm h0

theorem genStepB_zero (t row k : Nat) : genStepB st eqb T ew t row k 0 = 0 := by
  rw [genStepB_eq, if_pos rfl]

theorem pointRecB_zero (i : Nat) : ∀ r, pointRecB ng st eqb T E ew i r 0 = 0
  | 0 => rfl
  | r + 1 => by
    have s : pointRecB ng st eqb T E ew i (r + 1) 0 = pointRecB ng st eqb T E ew i r
        (genStepB st eqb T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) 0) :=
      strictN_app (genStepB st eqb T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) 0)
        (pointRecB ng st eqb T E ew i r)
    rw [s, genStepB_zero]
    exact pointRecB_zero i r

theorem pointRecB_spec (hst : ∀ k < ng, ∀ t, P t → P (st k t))
    (heq : ∀ k < ng, ∀ t y, P t → P y → eqb k t y = true → y = st k t) {i : Nat} (hP : P (T i)) :
    ∀ r, r ≤ ng → ∀ c x, (∀ j < c, P (T j)) → pointRecB ng st eqb T E ew i r c = x → x ≠ 0 →
      pointRecW ng st T E ew i r c = x ∧ ∀ j < x, P (T j)
  | 0, _, c, x, hI, hr, _ => by
    have e : c = x := hr
    subst e
    exact ⟨rfl, hI⟩
  | r + 1, hr1, c, x, hI, hr, h0 => by
    have s : pointRecB ng st eqb T E ew i (r + 1) c = pointRecB ng st eqb T E ew i r
        (genStepB st eqb T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) :=
      strictN_app (genStepB st eqb T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c)
        (pointRecB ng st eqb T E ew i r)
    have sW : pointRecW ng st T E ew i (r + 1) c = pointRecW ng st T E ew i r
        (genStepW st T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) :=
      strictN_app (genStepW st T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c)
        (pointRecW ng st T E ew i r)
    rw [s] at hr
    have hk : Nat.sub (Nat.sub ng r) (nat_lit 1) < ng := by
      change ng - r - 1 < ng
      omega
    have hc0 : genStepB st eqb T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c ≠ 0 := by
      intro z
      rw [z, pointRecB_zero] at hr
      exact h0 hr.symm
    obtain ⟨e1, hI'⟩ := genStepB_spec (hst _ hk) (heq _ hk) hP hI rfl hc0
    rw [sW, e1]
    exact pointRecB_spec hst heq hP r (by omega) _ x hI' hr h0

theorem pointStepB_eq (i c : Nat) :
    pointStepB ng st eqb T E ew i c = pointRecB ng st eqb T E ew i ng c := by
  unfold pointStepB
  rw [strictN_app, strictN_app]
  rfl

theorem pointStepW_rec (i c : Nat) :
    pointStepW ng st T E ew i c = pointRecW ng st T E ew i ng c := by
  unfold pointStepW
  rw [strictN_app, strictN_app]
  rfl

theorem runFB_succ (len lo c : Nat) :
    runFB ng st eqb T E ew (len + 1) lo c =
      runFB ng st eqb T E ew len (Nat.succ lo) (nIf(Nat.blt lo c, pointStepB ng st eqb T E ew lo c,
        nat_lit 0)) :=
  strictN_app _ _

theorem runFB_zero : ∀ len lo, runFB ng st eqb T E ew len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    rw [runFB_succ]
    have hb : Nat.blt lo 0 = false := by
      cases h : Nat.blt lo 0
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt_zero lo)
    rw [hb]
    exact runFB_zero len _

theorem runFB_add : ∀ (a b lo c : Nat),
    runFB ng st eqb T E ew (a + b) lo c =
      runFB ng st eqb T E ew b (lo + a) (runFB ng st eqb T E ew a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : Nat.succ lo + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm, runFB_succ, runFB_succ, runFB_add a b (Nat.succ lo), e]

theorem runFB_blocks (L : Nat) (C : Nat → Nat) : ∀ K,
    (∀ s < K, runSlB ng st eqb T E ew L C s = true) → runFB ng st eqb T E ew (L * K) 0 (C 0) = C K
  | 0, _ => rfl
  | K + 1, h => by
    rw [Nat.mul_succ, runFB_add, runFB_blocks L C K (fun s hs => h s (by omega)), Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h K (by omega))

theorem runFB_spec (hst : ∀ k < ng, ∀ t, P t → P (st k t))
    (heq : ∀ k < ng, ∀ t y, P t → P y → eqb k t y = true → y = st k t) :
    ∀ len lo c x, (∀ j < c, P (T j)) → runFB ng st eqb T E ew len lo c = x → x ≠ 0 →
      runFW ng st T E ew len lo c = x ∧ ∀ j < x, P (T j)
  | 0, lo, c, x, hI, hr, _ => by
    have e : c = x := hr
    subst e
    exact ⟨rfl, hI⟩
  | len + 1, lo, c, x, hI, hr, h0 => by
    rw [runFB_succ] at hr
    rw [runFW_succ]
    cases hb : Nat.blt lo c
    · rw [hb] at hr
      change runFB ng st eqb T E ew len (Nat.succ lo) 0 = x at hr
      rw [runFB_zero] at hr
      exact absurd hr.symm h0
    · rw [hb] at hr
      change runFB ng st eqb T E ew len (Nat.succ lo) (pointStepB ng st eqb T E ew lo c) = x at hr
      change runFW ng st T E ew len (Nat.succ lo) (pointStepW ng st T E ew lo c) = x ∧ _
      have hlt : lo < c := Nat.blt_eq.mp hb
      have hp0 : pointStepB ng st eqb T E ew lo c ≠ 0 := by
        intro z
        rw [z, runFB_zero] at hr
        exact h0 hr.symm
      obtain ⟨e1, hI'⟩ := pointRecB_spec hst heq (hI lo hlt) ng (le_refl _) c _ hI
        (pointStepB_eq lo c).symm hp0
      rw [pointStepW_rec, e1]
      exact runFB_spec hst heq len (Nat.succ lo) _ x hI' hr h0

theorem runW_of_runB {N L K : Nat} {C : Nat → Nat} (hst : ∀ k < ng, ∀ t, P t → P (st k t))
    (heq : ∀ k < ng, ∀ t y, P t → P y → eqb k t y = true → y = st k t) (h0 : P (T 0))
    (hC0 : C 0 = 1) (hCK : C K = N) (hN : N = L * K) (hN0 : N ≠ 0)
    (hs : ∀ s < K, runSlB ng st eqb T E ew L C s = true) :
    runFW ng st T E ew N 0 1 = N ∧ ∀ j < N, P (T j) := by
  have hb := runFB_blocks L C K hs
  rw [hC0, hCK, ← hN] at hb
  exact runFB_spec hst heq N 0 1 N (fun j hj => by
    have e : j = 0 := by omega
    subst e
    exact h0) hb hN0

end Run

theorem baseEqL_spec {w m : Nat} {G : Nat → Nat} {k t y : Nat} :
    ∀ {B : List Nat}, baseEqL w m G B k t y = true →
      ∀ b ∈ B, pg w m y b = pg w m (G k) (pg w m t b)
  | [], _ => fun b hb => absurd hb List.not_mem_nil
  | a :: B, h => by
    unfold baseEqL at h
    rw [strictB_app] at h
    change Bool.rec (motive := fun _ => Bool) false (List.rec (motive := fun _ => Bool) true
      (fun b _ ih => bAnd(Nat.beq (pg w m y b) (pg w m (G k) (pg w m t b)), ih)) B)
      (Nat.beq (pg w m y a) (pg w m (G k) (pg w m t a))) = true at h
    cases ha : Nat.beq (pg w m y a) (pg w m (G k) (pg w m t a))
    · rw [ha] at h
      exact absurd h Bool.false_ne_true
    · rw [ha] at h
      have hB : baseEqL w m G B k t y = true := by
        unfold baseEqL
        rw [strictB_app]
        exact h
      intro b hb
      rcases List.mem_cons.1 hb with e | e
      · subst e
        exact Nat.eq_of_beq_eq_true ha
      · exact baseEqL_spec hB b e

end CFSG.KC.L34KSnd

end
