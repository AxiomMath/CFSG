module

public import CFSG.Certificates.Kernel.Co1DceGroup
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.Co1D

open CFSG.KC CFSG.KC.DceS CFSG.KC.Loop CFSG.KS.P16
open scoped Pointwise

section Rel

variable {G : Type*} [Group G]

def RelN (N : Subgroup G) (a b : G) : Prop := a * b⁻¹ ∈ N

variable {N : Subgroup G} {a b c : G}

theorem RelN.of_eq (h : a = b) : RelN N a b := by
  rw [RelN, h, mul_inv_cancel]
  exact N.one_mem

theorem RelN.symm (h : RelN N a b) : RelN N b a := by
  have e : b * a⁻¹ = (a * b⁻¹)⁻¹ := by group
  rw [RelN, e]
  exact N.inv_mem h

theorem RelN.trans (h : RelN N a b) (h' : RelN N b c) : RelN N a c := by
  have e : a * c⁻¹ = a * b⁻¹ * (b * c⁻¹) := by group
  rw [RelN, e]
  exact N.mul_mem h h'

theorem RelN.mul_right (h : RelN N a b) (g : G) : RelN N (a * g) (b * g) := by
  have e : a * g * (b * g)⁻¹ = a * b⁻¹ := by group
  rw [RelN, e]
  exact h

end Rel

section InM

variable {LT : ℕ → ℕ} {NL TL : ℕ}

def InM (LT : ℕ → ℕ) (NL TL P : ℕ) : Prop := IsP P ∧ perm16 P ∈ Mg LT NL TL

theorem inM_idP : InM LT NL TL idP :=
  ⟨isP_idP, by
    rw [perm16_idP]
    exact (Mg LT NL TL).one_mem⟩

theorem inM_pmul {a b : ℕ} (ha : InM LT NL TL a) (hb : InM LT NL TL b) :
    InM LT NL TL (pmul a b) :=
  ⟨isP_pmul ha.1 hb.1, by
    rw [perm16_pmul ha.1 hb.1]
    exact (Mg LT NL TL).mul_mem ha.2 hb.2⟩

theorem inM_pinv {a : ℕ} (ha : InM LT NL TL a) : InM LT NL TL (pinv a) :=
  ⟨isP_pinv ha.1, by
    rw [perm16_pinv ha.1]
    exact (Mg LT NL TL).inv_mem ha.2⟩

theorem inM_cancel_right {a b : ℕ} (ha : IsP a) (hb : InM LT NL TL b)
    (hab : InM LT NL TL (pmul a b)) : InM LT NL TL a := by
  refine ⟨ha, ?_⟩
  have e : perm16 a = perm16 (pmul a b) * (perm16 b)⁻¹ := by
    rw [perm16_pmul ha hb.1, mul_inv_cancel_right]
  rw [e]
  exact (Mg LT NL TL).mul_mem hab.2 ((Mg LT NL TL).inv_mem hb.2)

theorem inM_cancel_left {a b : ℕ} (ha : InM LT NL TL a) (hb : IsP b)
    (hab : InM LT NL TL (pmul a b)) : InM LT NL TL b := by
  refine ⟨hb, ?_⟩
  have e : perm16 b = (perm16 a)⁻¹ * perm16 (pmul a b) := by
    rw [perm16_pmul ha.1 hb, inv_mul_cancel_left]
  rw [e]
  exact (Mg LT NL TL).mul_mem ((Mg LT NL TL).inv_mem ha.2) hab.2

theorem inM_of_pinv {a : ℕ} (ha : IsP a) (h : InM LT NL TL (pinv a)) : InM LT NL TL a := by
  refine ⟨ha, ?_⟩
  have e : perm16 a = (perm16 (pinv a))⁻¹ := by rw [perm16_pinv ha, inv_inv]
  rw [e]
  exact (Mg LT NL TL).inv_mem h.2

variable {PBT : ℕ → ℕ} {NB BB c R D P D' P' : ℕ}

theorem rstep_isP (hR : IsP (dP R)) (hP0 : IsP P) (hs : RStep PBT NB BB c R D P D' P') :
    IsP P' := by
  rcases hs with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · exact isP_pmul hR hP0
  · exact isP_pmul (isP_pinv hR) hP0

theorem rstep_inM (hR : InM LT NL TL (dP R)) (hP0 : InM LT NL TL P)
    (hs : RStep PBT NB BB c R D P D' P') : InM LT NL TL P' := by
  rcases hs with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · exact inM_pmul hR hP0
  · exact inM_pmul (inM_pinv hR) hP0

theorem rstep_inM_back (hR : InM LT NL TL (dP R)) (hP0 : IsP P) (hP1 : InM LT NL TL P')
    (hs : RStep PBT NB BB c R D P D' P') : InM LT NL TL P := by
  rcases hs with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · exact inM_cancel_left hR hP0 hP1
  · exact inM_cancel_left (inM_pinv hR) hP0 hP1

theorem rstep_own (hR : IsP (dP R)) (hP0 : InM LT NL TL P) (hP1 : InM LT NL TL P')
    (hs : RStep PBT NB BB c R D P D' P') : InM LT NL TL (dP R) := by
  rcases hs with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · exact inM_cancel_right hR hP0 hP1
  · exact inM_of_pinv hR (inM_cancel_right (isP_pinv hR) hP0 hP1)

end InM

section Mean

variable {G : Type*} [Group G]

noncomputable def tv (LT HT GT : ℕ → ℕ) (NL TL : ℕ) (x : ℕ → G) (J : ℕ) : G :=
  if J = 0 then 1 else tj LT HT GT NL TL x (J - 1)

noncomputable def lv (x : ℕ → G) (c : ℕ) : G := if c = 255 then 1 else x c

def FM (LT HT GT : ℕ → ℕ) (NL TL : ℕ) (x wv : ℕ → G) (R : ℕ) : Prop :=
  RelN (Nsub x NL TL) (wv (dD R) * tv LT HT GT NL TL x (dJ R)) (wv (dDp R) * rc LT NL TL x (dP R))

def TCHyp (LT HT GT PBT : ℕ → ℕ) (NL TL NO NB BB : ℕ) (x : ℕ → G) : Prop :=
  ∀ Q j, InM LT NL TL Q → j < NO → allIn NB BB (imgMasks Q (PBT j)) = true →
    rc LT NL TL x Q * x TL * (rc LT NL TL x Q)⁻¹ = tj LT HT GT NL TL x j

variable {LT HT GT PBT : ℕ → ℕ} {NL TL NO NB BB : ℕ} {x wv : ℕ → G}

theorem tj_inv (ht : x TL * x TL = 1) (j : ℕ) :
    (tj LT HT GT NL TL x j)⁻¹ = tj LT HT GT NL TL x j := by
  apply inv_eq_of_mul_eq_one_right
  unfold tj
  have e : ∀ a t : G, a⁻¹ * t * a * (a⁻¹ * t * a) = a⁻¹ * (t * t) * a := fun a t => by group
  rw [e, ht]
  group

theorem grp1 (a p q b : G) : a * p * 1 * (b * (q * p))⁻¹ = a * 1 * (b * q)⁻¹ := by group

theorem grp2 (a p q b T : G) : a * p * (p⁻¹ * T * p) * (b * (q * p))⁻¹ = a * T * (b * q)⁻¹ := by
  group

theorem grp3 (a p q b : G) : a * p * 1 * (b * (q⁻¹ * p))⁻¹ = (b * 1 * (a * q)⁻¹)⁻¹ := by group

theorem grp4 (a p q b T : G) :
    a * p * ((q⁻¹ * p)⁻¹ * T * (q⁻¹ * p)) * (b * (q⁻¹ * p))⁻¹ = (b * T⁻¹ * (a * q)⁻¹)⁻¹ := by
  group

theorem step_iff (hTC : TCHyp LT HT GT PBT NL TL NO NB BB x) (ht : x TL * x TL = 1)
    {c R D P D' P' : ℕ} (hJ : dJ R ≤ NO) (hRM : InM LT NL TL (dP R))
    (hPM : InM LT NL TL P) (hc : c = 255 ∨ c = TL) (hs : RStep PBT NB BB c R D P D' P') :
    InM LT NL TL P' ∧ (RelN (Nsub x NL TL) (wv D * rc LT NL TL x P * lv x c)
      (wv D' * rc LT NL TL x P') ↔ FM LT HT GT NL TL x wv R) := by
  rcases hs with ⟨rfl, rfl, rfl, hk⟩ | ⟨rfl, rfl, rfl, hk⟩
  · refine ⟨inM_pmul hRM hPM, ?_⟩
    unfold FM RelN
    rw [(rc_mul (x := x) hRM.1 hPM.1 hRM.2 hPM.2).2]
    rcases hk with ⟨rfl, hj0⟩ | ⟨hc255, hj, hall⟩
    · unfold lv tv
      rw [ite_eq_left rfl, ite_eq_left hj0, grp1]
    · have hcT : c = TL := hc.resolve_left hc255
      have hT := hTC P (dJ R - 1) hPM (by omega) hall
      unfold lv tv
      rw [ite_eq_right hc255, ite_eq_right (by omega : dJ R ≠ 0), hcT]
      have ex : x TL = (rc LT NL TL x P)⁻¹ * tj LT HT GT NL TL x (dJ R - 1) * rc LT NL TL x P := by
        rw [← hT]
        group
      rw [ex, grp2]
  · have hRi := inM_pinv hRM
    refine ⟨inM_pmul hRi hPM, ?_⟩
    unfold FM RelN
    have hrc : rc LT NL TL x (pmul (pinv (dP R)) P) =
        (rc LT NL TL x (dP R))⁻¹ * rc LT NL TL x P := by
      rw [(rc_mul (x := x) hRi.1 hPM.1 hRi.2 hPM.2).2, (rc_inv (x := x) hRM.1 hRM.2).2]
    rw [hrc]
    rcases hk with ⟨rfl, hj0⟩ | ⟨hc255, hj, hall⟩
    · unfold lv tv
      rw [ite_eq_left rfl, ite_eq_left hj0, grp3, inv_mem_iff]
    · have hcT : c = TL := hc.resolve_left hc255
      have hT := hTC _ (dJ R - 1) (inM_pmul hRi hPM) (by omega) hall
      rw [hrc] at hT
      unfold lv tv
      rw [ite_eq_right hc255, ite_eq_right (by omega : dJ R ≠ 0), hcT]
      have ex : x TL = ((rc LT NL TL x (dP R))⁻¹ * rc LT NL TL x P)⁻¹ *
          tj LT HT GT NL TL x (dJ R - 1) * ((rc LT NL TL x (dP R))⁻¹ * rc LT NL TL x P) := by
        rw [← hT]
        group
      rw [ex, grp4, tj_inv ht, inv_mem_iff]

theorem walk_mean {blk : ℕ → ℕ} (hTC : TCHyp LT HT GT PBT NL TL NO NB BB x)
    (ht : x TL * x TL = 1)
    (hLet : ∀ c < NL, c ≠ TL → InM LT NL TL (Nat.land (LT c) m64) ∧
      rc LT NL TL x (Nat.land (LT c) m64) = x c)
    {i R W n D0 P0 : ℕ}
    (hprev : ∀ h < i, dJ (fct blk h) ≤ NO ∧ InM LT NL TL (dP (fct blk h)) ∧
      FM LT HT GT NL TL x wv (fct blk h))
    (hRJ : dJ R ≤ NO) (hRP : IsP (dP R)) (hP0 : InM LT NL TL P0) (hval : bvF (lv x) W n = 1)
    (hW : WalkOn blk LT PBT NL TL NB BB i R W n D0 P0) :
    InM LT NL TL (dP R) ∧ FM LT HT GT NL TL x wv R := by
  obtain ⟨Ds, Ps, qo, hqo, h0D, h0P, hnD, hnP, hown, hst⟩ := hW
  have hIsP : ∀ q ≤ n, IsP (Ps q) := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [h0P]
      exact hP0.1
    | succ q ih =>
      intro hq
      obtain ⟨hNl, hOw, hRf⟩ := hst q (by omega)
      by_cases hc : wLet W q = 255 ∨ wLet W q = TL
      · by_cases hq0 : q = qo
        · exact rstep_isP hRP (ih (by omega)) (hOw hq0)
        · obtain ⟨h', hh', hs⟩ := hRf hq0 hc
          exact rstep_isP (hprev h' hh').2.1.1 (ih (by omega)) hs
      · have h1 : wLet W q ≠ 255 := fun e => hc (Or.inl e)
        have h2 : wLet W q ≠ TL := fun e => hc (Or.inr e)
        obtain ⟨hcl, -, -, e⟩ := hNl h1 h2
        rw [e]
        exact isP_pmul (ih (by omega)) (hLet _ hcl h2).1.1
  have hF : ∀ q ≤ qo, InM LT NL TL (Ps q) := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [h0P]
      exact hP0
    | succ q ih =>
      intro hq
      obtain ⟨hNl, -, hRf⟩ := hst q (by omega)
      have hq0 : q ≠ qo := by omega
      by_cases hc : wLet W q = 255 ∨ wLet W q = TL
      · obtain ⟨h', hh', hs⟩ := hRf hq0 hc
        exact rstep_inM (hprev h' hh').2.1 (ih (by omega)) hs
      · have h1 : wLet W q ≠ 255 := fun e => hc (Or.inl e)
        have h2 : wLet W q ≠ TL := fun e => hc (Or.inr e)
        obtain ⟨hcl, -, -, e⟩ := hNl h1 h2
        rw [e]
        exact inM_pmul (ih (by omega)) (hLet _ hcl h2).1
  have hB : ∀ d, qo + 1 + d ≤ n → InM LT NL TL (Ps (n - d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, hnP]
      exact hP0
    | succ d ih =>
      intro hd
      have ihd := ih (by omega)
      obtain ⟨q, hq⟩ : ∃ q, q = n - (d + 1) := ⟨_, rfl⟩
      have e1 : n - d = q + 1 := by omega
      rw [e1] at ihd
      rw [← hq]
      obtain ⟨hNl, -, hRf⟩ := hst q (by omega)
      have hq0 : q ≠ qo := by omega
      have hqn : q ≤ n := by omega
      by_cases hc : wLet W q = 255 ∨ wLet W q = TL
      · obtain ⟨h', hh', hs⟩ := hRf hq0 hc
        exact rstep_inM_back (hprev h' hh').2.1 (hIsP q hqn) ihd hs
      · have h1 : wLet W q ≠ 255 := fun e => hc (Or.inl e)
        have h2 : wLet W q ≠ TL := fun e => hc (Or.inr e)
        obtain ⟨hcl, -, -, e⟩ := hNl h1 h2
        rw [e] at ihd
        exact inM_cancel_right (hIsP q hqn) (hLet _ hcl h2).1 ihd
  have hM : ∀ q ≤ n, InM LT NL TL (Ps q) := by
    intro q hq
    by_cases h1 : q ≤ qo
    · exact hF q h1
    · have := hB (n - q) (by omega)
      rwa [Nat.sub_sub_self hq] at this
  have hRM : InM LT NL TL (dP R) :=
    rstep_own hRP (hM qo (by omega)) (hM (qo + 1) (by omega)) ((hst qo hqo).2.1 rfl)
  refine ⟨hRM, ?_⟩
  have hstep : ∀ q < n, q ≠ qo → RelN (Nsub x NL TL)
      (wv (Ds q) * rc LT NL TL x (Ps q) * lv x (wLet W q))
      (wv (Ds (q + 1)) * rc LT NL TL x (Ps (q + 1))) := by
    intro q hq hq0
    obtain ⟨hNl, -, hRf⟩ := hst q hq
    by_cases hc : wLet W q = 255 ∨ wLet W q = TL
    · obtain ⟨h', hh', hs⟩ := hRf hq0 hc
      exact ((step_iff hTC ht (hprev h' hh').1 (hprev h' hh').2.1 (hM q (by omega)) hc hs).2).2
        (hprev h' hh').2.2
    · have h1 : wLet W q ≠ 255 := fun e => hc (Or.inl e)
      have h2 : wLet W q ≠ TL := fun e => hc (Or.inr e)
      obtain ⟨hcl, -, e1, e2⟩ := hNl h1 h2
      have hPq := hM q (by omega)
      have hl := hLet _ hcl h2
      rw [e1, e2, (rc_mul (x := x) hPq.1 hl.1.1 hPq.2 hl.1.2).2, hl.2]
      unfold lv
      rw [ite_eq_right h1, mul_assoc]
      exact RelN.of_eq rfl
  have c1 : ∀ q ≤ qo, RelN (Nsub x NL TL) (wv (Ds 0) * rc LT NL TL x (Ps 0) * bvF (lv x) W q)
      (wv (Ds q) * rc LT NL TL x (Ps q)) := by
    intro q
    induction q with
    | zero =>
      intro _
      have e : bvF (lv x) W 0 = 1 := by simp [bvF]
      rw [e, mul_one]
      exact RelN.of_eq rfl
    | succ q ih =>
      intro hq
      have := (ih (by omega)).mul_right (lv x (wLet W q))
      have hq1 : q < n := by omega
      have hq2 : q ≠ qo := by omega
      rw [bvF_succ, ← mul_assoc]
      exact this.trans (hstep q hq1 hq2)
  have c2 : ∀ d, qo + 1 + d ≤ n → RelN (Nsub x NL TL)
      (wv (Ds (qo + 1)) * rc LT NL TL x (Ps (qo + 1)) * (bvF (lv x) W (qo + 1))⁻¹ *
        bvF (lv x) W (qo + 1 + d))
      (wv (Ds (qo + 1 + d)) * rc LT NL TL x (Ps (qo + 1 + d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.add_zero, inv_mul_cancel_right]
      exact RelN.of_eq rfl
    | succ d ih =>
      intro hd
      have := (ih (by omega)).mul_right (lv x (wLet W (qo + 1 + d)))
      have e : qo + 1 + (d + 1) = qo + 1 + d + 1 := by omega
      have hq1 : qo + 1 + d < n := by omega
      have hq2 : qo + 1 + d ≠ qo := by omega
      rw [e, bvF_succ (lv x) W (qo + 1 + d), ← mul_assoc]
      exact this.trans (hstep _ hq1 hq2)
  have f1 := (c1 qo le_rfl).mul_right (lv x (wLet W qo))
  have f2 := c2 (n - (qo + 1)) (by omega)
  have e3 : qo + 1 + (n - (qo + 1)) = n := by omega
  rw [e3, hval, mul_one, hnD, hnP, ← h0D, ← h0P] at f2
  have f3 := f2.mul_right (bvF (lv x) W (qo + 1))
  rw [inv_mul_cancel_right, bvF_succ, ← mul_assoc] at f3
  exact ((step_iff hTC ht hRJ hRM (hM qo (by omega)) hown ((hst qo hqo).2.1 rfl)).2).1
    (f1.symm.trans f3.symm)

end Mean

section Generic

variable {G : Type*} [Group G]

theorem exists_tree_w (nf : ℕ) (T : ℕ → Prop) (p c : ℕ → ℕ) (g : ℕ → G)
    (hpc : ∀ i < nf, T i → p i < c i)
    (hinj : ∀ i < nf, ∀ i' < nf, T i → T i' → c i = c i' → i = i') :
    ∃ wv : ℕ → G, wv 0 = 1 ∧ ∀ i < nf, T i → wv (c i) = wv (p i) * g i := by
  classical
  have key : ∀ B, ∃ wv : ℕ → G, wv 0 = 1 ∧
      ∀ i < nf, T i → c i < B → wv (c i) = wv (p i) * g i := by
    intro B
    induction B with
    | zero => exact ⟨fun _ => 1, rfl, fun i _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ B ih =>
      obtain ⟨wv, hw0, hw⟩ := ih
      refine ⟨fun D => if D = B then
          (if hB : ∃ i, i < nf ∧ T i ∧ c i = B then wv (p hB.choose) * g hB.choose else wv B)
        else wv D, ?_, ?_⟩
      · dsimp only
        by_cases h0 : (0 : ℕ) = B
        · have hn : ¬∃ i, i < nf ∧ T i ∧ c i = B := fun ⟨i, hi, hT, hc⟩ => by
            have := hpc i hi hT
            omega
          rw [ite_eq_left h0, dite_eq_right hn, ← h0, hw0]
        · rw [ite_eq_right h0, hw0]
      · intro i hi hTi hci
        dsimp only
        have hpB : p i ≠ B := by
          have := hpc i hi hTi
          omega
        rw [ite_eq_right hpB]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hci with hlt | heq
        · rw [ite_eq_right (by omega : c i ≠ B)]
          exact hw i hi hTi hlt
        · have hB : ∃ i, i < nf ∧ T i ∧ c i = B := ⟨i, hi, hTi, heq⟩
          rw [ite_eq_left heq, dite_eq_left hB]
          have hs := hB.choose_spec
          rw [hinj _ hs.1 _ hi hs.2.1 hTi (hs.2.2.trans heq.symm)]
  obtain ⟨wv, hw0, hw⟩ := key ((Finset.range nf).sup c + 1)
  exact ⟨wv, hw0, fun i hi hTi =>
    hw i hi hTi (Nat.lt_succ_of_le (Finset.le_sup (f := c) (Finset.mem_range.2 hi)))⟩

theorem dcoset_reps (N : Subgroup G) [Finite N] (w : G) (H : Subgroup N)
    (hH : ∀ k ∈ H, w * (k : G) * w⁻¹ ∈ N) :
    ∃ R : Finset G, R.card ≤ H.index ∧ (∀ r ∈ R, r ∈ N) ∧
      ∀ a ∈ N, ∀ b ∈ N, ∃ a' ∈ N, ∃ r ∈ R, a * w * b = a' * w * r := by
  classical
  let _ : Fintype (N ⧸ H) := Fintype.ofFinite _
  refine ⟨(Finset.univ.image fun q : N ⧸ H => (q.out)⁻¹).image Subtype.val, ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · intro r hr
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hr
    exact y.2
  · intro a ha b hb
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H (⟨b, hb⟩⁻¹ : N)
    refine ⟨a * (w * ((k : N) : G) * w⁻¹), N.mul_mem ha (hH _ k.2),
      ((((⟨b, hb⟩⁻¹ : N) : N ⧸ H).out)⁻¹ : N),
      Finset.mem_image.2 ⟨_, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, rfl⟩, ?_⟩
    have e : ((((⟨b, hb⟩⁻¹ : N) : N ⧸ H).out)⁻¹ : N) = (k : N)⁻¹ * ⟨b, hb⟩ := by
      rw [hk, mul_inv_rev, inv_inv]
    rw [e, Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem card_cover (N : Subgroup G) [Finite N] (A : Finset ℕ) (w : ℕ → G) (R : ℕ → Finset G)
    (K : Subgroup G) (hcov : ∀ g ∈ K, ∃ D ∈ A, ∃ a ∈ N, ∃ r ∈ R D, g = a * w D * r) :
    Finite K ∧ Nat.card K ≤ ∑ D ∈ A, Nat.card N * (R D).card := by
  classical
  have hNf : (N : Set G).Finite := Set.toFinite _
  let F : Finset G := A.biUnion fun D => (hNf.toFinset ×ˢ R D).image fun q => q.1 * w D * q.2
  have hsub : (K : Set G) ⊆ (F : Set G) := by
    intro g hg
    obtain ⟨D, hD, a, ha, r, hr, rfl⟩ := hcov g hg
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨D, hD, Finset.mem_image.2
      ⟨(a, r), Finset.mem_product.2 ⟨hNf.mem_toFinset.2 ha, hr⟩, rfl⟩⟩)
  have hfin : (K : Set G).Finite := F.finite_toSet.subset hsub
  refine ⟨hfin.to_subtype, ?_⟩
  have eK : Nat.card K = (K : Set G).ncard := Nat.card_coe_set_eq _
  have eN : Nat.card N = hNf.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hNf]
    exact Nat.card_coe_set_eq _
  rw [eK, eN]
  calc (K : Set G).ncard ≤ (F : Set G).ncard := Set.ncard_le_ncard hsub
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ ∑ D ∈ A, ((hNf.toFinset ×ˢ R D).image fun q => q.1 * w D * q.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ D ∈ A, hNf.toFinset.card * (R D).card := Finset.sum_le_sum fun D _ => by
      rw [← Finset.card_product]
      exact Finset.card_image_le

theorem natRec_add_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_add_sum F k, Finset.sum_range_succ, Nat.add_comm]

theorem sumBelow_g (m : ℕ) (f : ℕ → ℕ) : ∀ hi, sumBelow m hi f =
    ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m)
  | 0 => by simp [sumBelow]
  | hi + 1 => by
    have e : sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (sumBelow m hi f) := rfl
    have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, natRec_add_sum, sumBelow_g m f hi, Nat.mul_succ, Finset.sum_range_add]
    simp only [e2]
    exact Nat.add_comm _ _

theorem sumBelow_spec {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  rw [sumBelow_g]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact Finset.mem_range.1 hi
  rw [hb]

end Generic

section Codes

variable {G : Type*} [Group G] {LT : ℕ → ℕ} {NL TL : ℕ} {x : ℕ → G}
  (hLv : ∀ c < NL, c ≠ TL → IsP (Nat.land (LT c) m64) ∧
    pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) = idP)
  (hx : ∀ c < NL, x c * x c = 1)
  (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
include hLv hx hρ

theorem N_code {n : G} (hn : n ∈ Nsub x NL TL) : ∃ Q, InM LT NL TL Q ∧ rc LT NL TL x Q = n := by
  rw [← rhoM_range hLv hx hρ] at hn
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hn
  obtain ⟨u, hu, e⟩ := Mg_word hLv y.2
  exact ⟨wc LT u, ⟨(perm16_wc hLv hu).1, e ▸ y.2⟩, rc_eq y e.symm⟩

theorem rhoM_mem (y : Mg LT NL TL) : rhoM LT NL TL x y ∈ Nsub x NL TL := by
  rw [← rhoM_range hLv hx hρ]
  exact ⟨y, rfl⟩

theorem rhoM_cod_surj :
    Function.Surjective ((rhoM LT NL TL x).codRestrict (Nsub x NL TL) (rhoM_mem hLv hx hρ)) := by
  rintro ⟨n, hn⟩
  rw [← rhoM_range hLv hx hρ] at hn
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hn
  exact ⟨y, Subtype.ext hy⟩

theorem N_fin : Finite (Nsub x NL TL) ∧ Nat.card (Nsub x NL TL) ≤ Nat.card (Mg LT NL TL) :=
  ⟨Finite.of_surjective _ (rhoM_cod_surj hLv hx hρ),
    Nat.card_le_card_of_surjective _ (rhoM_cod_surj hLv hx hρ)⟩

end Codes

theorem covEntry_spec {blk PBT OMT : ℕ → ℕ} {NB ALIVE nf D j e : ℕ}
    (hce : covEntry blk PBT OMT NB ALIVE nf D j e = true) :
    ∃ hh < nf, (dD (fct blk hh) = D ∧ dJ (fct blk hh) = j + 1 ∧
      ALIVE.testBit (dDp (fct blk hh)) = true) ∨
      (dDp (fct blk hh) = D ∧ 0 < dJ (fct blk hh) ∧ ALIVE.testBit (dD (fct blk hh)) = true ∧
        allMemb NB (OMT (dJ (fct blk hh) - 1)) (imgMasks (dP (fct blk hh)) (PBT j)) = true) := by
  unfold covEntry at hce
  rw [andB_iff, letB_eq, brec_eq, Nat.blt_eq] at hce
  obtain ⟨hlt, hce⟩ := hce
  refine ⟨_, hlt, ?_⟩
  split_ifs at hce
  · right
    simp only [andB_iff, Nat.beq_eq, Nat.blt_eq, bitAt_iff, Nat.sub_eq] at hce
    exact hce
  · left
    simp only [andB_iff, Nat.beq_eq, bitAt_iff, Nat.succ_eq_add_one] at hce
    exact hce

def CInv (blk PBT OMT : ℕ → ℕ) (NB NO ALIVE nf X : ℕ) : Prop :=
  X = 0 ∨ ∀ D, D + 1 < X → ALIVE.testBit D = true →
    ∀ j < NO, ∃ e, covEntry blk PBT OMT NB ALIVE nf D j e = true

theorem CInv_succ {blk PBT OMT : ℕ → ℕ} {NB NO ALIVE nf X : ℕ}
    (hX : CInv blk PBT OMT NB NO ALIVE nf X) (hX0 : 0 < X)
    (hlast : ALIVE.testBit (X - 1) = true →
      ∀ j < NO, ∃ e, covEntry blk PBT OMT NB ALIVE nf (X - 1) j e = true) :
    CInv blk PBT OMT NB NO ALIVE nf (X + 1) := by
  right
  intro D hD hal j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hD with hlt | heq
  · rcases hX with h0 | hX
    · omega
    · exact hX D hlt hal j hj
  · have e : D = X - 1 := by omega
    rw [e] at hal ⊢
    exact hlast hal j hj

theorem covChunk_inv {blk PBT OMT : ℕ → ℕ} {NB NO hi ALIVE nf C X : ℕ} (hNO : NO ≤ 64 * hi)
    (hX : CInv blk PBT OMT NB NO ALIVE nf X) :
    CInv blk PBT OMT NB NO ALIVE nf (covChunk blk PBT OMT NB NO hi ALIVE nf C X) := by
  unfold covChunk
  refine rec_inv (P := CInv blk PBT OMT NB NO ALIVE nf) _ (fun _ ih hih J X hX => ?_) _ _ _ hX
  simp only [strictN_eq, brec_eq]
  split_ifs with hb hc hc
  · apply hih
    rw [andB_iff, Nat.blt_eq] at hc
    exact CInv_succ hX hc.1 fun _ j hj => ⟨_, allBelow_spec hc.2 hNO j hj⟩
  · exact hih _ _ (Or.inl rfl)
  · apply hih
    rw [Nat.blt_eq] at hc
    refine CInv_succ hX hc fun hal => ?_
    rw [← bitAt_iff] at hal
    exact absurd hal hb
  · exact hih _ _ (Or.inl rfl)

theorem runCover_inv {blk PBT OMT : ℕ → ℕ} {NB NO hi ALIVE nf : ℕ} (hNO : NO ≤ 64 * hi) :
    ∀ (Cs : List ℕ) (X : ℕ), CInv blk PBT OMT NB NO ALIVE nf X →
      CInv blk PBT OMT NB NO ALIVE nf (runCover blk PBT OMT NB NO hi ALIVE nf Cs X)
  | [], _, hX => hX
  | C :: Cs, X, hX => by
    change CInv blk PBT OMT NB NO ALIVE nf (strictN (covChunk blk PBT OMT NB NO hi ALIVE nf C X)
      (runCover blk PBT OMT NB NO hi ALIVE nf Cs))
    rw [strictN_eq]
    exact runCover_inv hNO Cs _ (covChunk_inv hNO hX)

theorem alive_lt {A ND D : ℕ} (hA : A < 2 ^ ND) (hD : A.testBit D = true) : D < ND := by
  by_contra hc
  have : A < 2 ^ D := lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.testBit_lt_two_pow this] at hD
  exact absurd hD (by decide)

theorem stabVal_spec {blk SE STT : ℕ → ℕ} {nf nN D : ℕ}
    (hv : stabVal blk SE STT nf nN D < failV) :
    0 < stN (STT D) ∧
      (∀ k < glN (stGL (STT D)), glH (stGL (STT D)) k < nf ∧
        dD (fct blk (glH (stGL (STT D)) k)) = D ∧ dJ (fct blk (glH (stGL (STT D)) k)) = 0 ∧
        dDp (fct blk (glH (stGL (STT D)) k)) = D) ∧
      Nat.beq (eCnt (enumRun SE (packGens (fun k => dP (fct blk (glH (stGL (STT D)) k)))
        (glN (stGL (STT D)))) (glN (stGL (STT D))) (stN (STT D)) (stOff (STT D)) (stN (STT D)) 1))
        (Nat.succ (stN (STT D))) = true ∧
      stabVal blk SE STT nf nN D = nN / stN (STT D) := by
  unfold stabVal at hv ⊢
  simp only [strictN_eq, brec_eq] at hv ⊢
  split_ifs at hv ⊢ with hc
  · rw [andB_iff, andB_iff, andB_iff, andB_iff, Nat.blt_eq] at hc
    obtain ⟨h1, -, -, h4, h5⟩ := hc
    refine ⟨h1, fun k hk => ?_, h5, rfl⟩
    unfold gensStab at h4
    have := (allRec_iff _ _).1 h4 k hk
    rw [andB_iff, Nat.blt_eq] at this
    unfold dStab at this
    rw [andB_iff, andB_iff, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  · exact absurd hv (lt_irrefl _)

noncomputable def idxD (blk SE STT : ℕ → ℕ) (nf nN D : ℕ) : ℕ :=
  if D = 0 then 1 else stabVal blk SE STT nf nN D

theorem indexSum_eq {blk SE STT : ℕ → ℕ} {nf nN ND hi ALIVE : ℕ} (hND : ND ≤ 64 * hi) :
    indexSum blk SE STT nf nN ND hi ALIVE =
      ∑ D ∈ (Finset.range ND).filter (fun D => ALIVE.testBit D = true),
        idxD blk SE STT nf nN D := by
  unfold indexSum
  rw [sumBelow_spec _ hND, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D _
  unfold idxD
  rw [brec_eq, brec_eq]
  by_cases ha : ALIVE.testBit D = true
  · rw [ite_eq_left ((bitAt_iff _ _).2 ha), ite_eq_left ha]
    by_cases h0 : D = 0
    · have hb : Nat.beq D 0 = true := by rw [Nat.beq_eq]; exact h0
      rw [ite_eq_left hb, ite_eq_left h0]
    · have hb : ¬Nat.beq D 0 = true := by rw [Nat.beq_eq]; exact h0
      rw [ite_eq_right hb, ite_eq_right h0]
  · have hb : ¬bitAt ALIVE D = true := fun h' => ha ((bitAt_iff _ _).1 h')
    rw [ite_eq_right hb, ite_eq_right ha]
    rfl

section DceOk

variable {blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE : ℕ → ℕ}
  {NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT
    hL hH hO hR hD P : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ} {G : Type*} [Group G]

theorem dceOk_TC (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod) :
    TCHyp LT HT GT PBT NL TL NO NB BB x := fun _ _ hQ hj ha =>
  dceOk_tconj h hN x hrels hρ hT hj hQ.1 hQ.2 (dceOk_tstep h hQ.1 hj ha)

theorem dceOk_letRc (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL
      TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1
      X0 X1 = true) (x : ℕ → G) (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1) :
    ∀ c < NL, c ≠ TL → InM LT NL TL (Nat.land (LT c) m64) ∧
      rc LT NL TL x (Nat.land (LT c) m64) = x c := by
  obtain ⟨hLv, hx⟩ := dceOk_rhoHyps h x hrels
  intro c hc hcT
  obtain ⟨h1, h2⟩ := rc_letter hLv hx hρ hc hcT
  exact ⟨⟨(hLv c hc hcT).1, h1⟩, h2⟩

theorem dceOk_hQuot (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL
      TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1
      X0 X1 = true) {a b : ℕ} (ha : a < NH) (hb : b < NH) : InM LT NL TL (hQuot HT a b) :=
  inM_pmul (inM_pinv (dceOk_hdr_mem h a ha)) (dceOk_hdr_mem h b hb)

theorem dceOk_facts_mean (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM
      NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0
      S1 X0 X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod) {nxf : ℕ → ℕ}
    (hf : ∀ i < nf, FactSem blk LT HT PBT WT NL TL NB BB NH ND NO NW i (nxf i) (nxf (i + 1)))
    {wv : ℕ → G} (hw0 : wv 0 = 1)
    (hwT : ∀ i < nf, nxf (i + 1) = nxf i + 1 →
      wv (dDp (fct blk i)) = wv (dD (fct blk i)) * tv LT HT GT NL TL x (dJ (fct blk i))) :
    ∀ i < nf, dJ (fct blk i) ≤ NO ∧ InM LT NL TL (dP (fct blk i)) ∧
      FM LT HT GT NL TL x wv (fct blk i) := by
  have hTC := dceOk_TC h hN x hrels hρ hT
  obtain ⟨hLv, hx⟩ := dceOk_rhoHyps h x hrels
  have ht : x TL * x TL = 1 := hx TL (dceOk_letters h).1
  have hLet := dceOk_letRc h x hrels hρ
  have hWd := (dceOk_words h x hrels).2
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨hrec, hk⟩ := hf i hi
    obtain ⟨-, -, hJ, hIsP⟩ := recOK_spec hrec
    refine ⟨hJ, ?_⟩
    rcases hk with ⟨e, htr⟩ | ⟨-, d1, d2, d3, a, ha, b, hb, hpe⟩ |
        ⟨-, t, htw, a, ha, b, hb, D0, -, hwalk⟩
    · have hpi := htr.2.2.2
      refine ⟨by rw [hpi]; exact inM_idP, ?_⟩
      unfold FM
      rw [hwT i hi e, hpi, (rc_idP (LT := LT) (NL := NL) (TL := TL) (x := x)).2, mul_one]
      exact RelN.of_eq rfl
    · have hQ := dceOk_hQuot h (LT := LT) ha hb
      refine ⟨by rw [hpe]; exact hQ, ?_⟩
      unfold FM RelN
      rw [d1, d2, d3, hpe, hw0]
      unfold tv
      rw [ite_eq_left rfl]
      simp only [one_mul]
      exact (Nsub x NL TL).inv_mem (rc_mem hLv hx hρ hQ.2)
    · exact walk_mean hTC ht hLet (fun h' hh' => ih h' hh' (by omega)) hJ hIsP
        (dceOk_hQuot h ha hb) (hWd t htw).2.2 hwalk

theorem dceOk_covered (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL
      TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1
      X0 X1 = true) : ∀ D, ALIVE.testBit D = true → D < ND ∧
      ∀ j < NO, ∃ e, covEntry blk PBT OMT NB ALIVE nf D j e = true := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, h12, -, -, -, -, -, -, -, -, -, h22, h23, h24, -⟩ :=
    dceOk_spec h
  rw [Nat.beq_eq] at h22 h23 h24
  have hA := (constOK_spec h1).2.2.2.2.2.1
  have h0 : CInv blk PBT OMT NB NO ALIVE nf X0 := Or.inr fun D hD => absurd hD (by omega)
  have hX := runCover_inv (by simpa using h12) CCs X0 h0
  rw [h23, h24] at hX
  intro D hal
  have hDl := alive_lt hA hal
  refine ⟨hDl, ?_⟩
  rcases hX with h0' | hX
  · exact absurd h0' (Nat.succ_ne_zero _)
  · exact hX D (by omega) hal

theorem dceOk_cover_mean (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM
      NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0
      S1 X0 X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod) {wv : ℕ → G}
    (hFM : ∀ i < nf, dJ (fct blk i) ≤ NO ∧ InM LT NL TL (dP (fct blk i)) ∧
      FM LT HT GT NL TL x wv (fct blk i)) :
    ∀ D, ALIVE.testBit D = true → ∀ j < NO, ∃ D', ALIVE.testBit D' = true ∧
      ∃ a ∈ Nsub x NL TL, ∃ b ∈ Nsub x NL TL, wv D * tj LT HT GT NL TL x j = a * wv D' * b := by
  obtain ⟨hLv, hx⟩ := dceOk_rhoHyps h x hrels
  have ht : x TL * x TL = 1 := hx TL (dceOk_letters h).1
  obtain ⟨-, -, hsys, -⟩ := dceOk_omega h
  intro D hal j hj
  obtain ⟨-, hcov⟩ := dceOk_covered h D hal
  obtain ⟨e, he⟩ := hcov j hj
  obtain ⟨hh, hhn, ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, e4⟩⟩ := covEntry_spec he
  · obtain ⟨-, hπ, hfm⟩ := hFM hh hhn
    unfold FM RelN at hfm
    rw [e1, e2] at hfm
    unfold tv at hfm
    rw [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel] at hfm
    refine ⟨_, e3, _, hfm, _, rc_mem hLv hx hρ hπ.2, ?_⟩
    group
  · obtain ⟨hJ, hπ, hfm⟩ := hFM hh hhn
    obtain ⟨j', hj'⟩ : ∃ j', j' = dJ (fct blk hh) - 1 := ⟨_, rfl⟩
    have hj'O : j' < NO := by omega
    have hJ0 : dJ (fct blk hh) ≠ 0 := by omega
    rw [← hj'] at e4
    have hπΩ := sys_img hπ.1 (hsys j hj).1 (hsys j hj).2 (hsys j' hj'O).2 e4
    obtain ⟨hg, hgM, hgΩ⟩ := dceOk_g h j hj
    have hgi : InM LT NL TL (pinv (hP (HT (GT j)))) := inM_pinv ⟨hg, hgM⟩
    have hπi := inM_pinv hπ
    have hQ := inM_pmul hπi hgi
    have hrcQ : rc LT NL TL x (pmul (pinv (dP (fct blk hh))) (pinv (hP (HT (GT j))))) =
        (rc LT NL TL x (dP (fct blk hh)))⁻¹ * (rc LT NL TL x (hP (HT (GT j))))⁻¹ := by
      rw [(rc_mul (x := x) hπi.1 hgi.1 hπi.2 hgi.2).2, (rc_inv (x := x) hπ.1 hπ.2).2,
        (rc_inv (x := x) hg hgM).2]
    have hQΩ : (perm16 (pmul (pinv (dP (fct blk hh))) (pinv (hP (HT (GT j))))))⁻¹ •
        sysOf NB (OMT j') = sysOf NB (OMT I0) := by
      rw [perm16_pmul hπi.1 hgi.1, perm16_pinv hπ.1, perm16_pinv hg, mul_inv_rev, inv_inv,
        inv_inv, mul_smul, ← hπΩ, smul_inv_smul, ← hgΩ, smul_inv_smul]
    have htc := dceOk_tconj h hN x hrels hρ hT hj'O hQ.1 hQ.2 hQΩ
    rw [hrcQ] at htc
    have htj : tj LT HT GT NL TL x j = rc LT NL TL x (dP (fct blk hh)) *
        tj LT HT GT NL TL x j' * (rc LT NL TL x (dP (fct blk hh)))⁻¹ := by
      rw [← htc]
      unfold tj
      group
    unfold FM RelN at hfm
    rw [e1] at hfm
    unfold tv at hfm
    rw [ite_eq_right hJ0, ← hj'] at hfm
    refine ⟨_, e3, _, (Nsub x NL TL).inv_mem hfm, _,
      (Nsub x NL TL).inv_mem (rc_mem hLv hx hρ hπ.2), ?_⟩
    rw [htj]
    have e5 : ∀ a q b T : G, (b * T * (a * q)⁻¹)⁻¹ * b * q⁻¹ = a * (q * T⁻¹ * q⁻¹) :=
      fun a q b T => by group
    rw [e5, tj_inv ht]

theorem dceOk_orbit_idx (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM
      NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0
      S1 X0 X1 = true) {Q : ℕ} (hQ : InM LT NL TL Q) :
    ∃ j < NO, (perm16 Q)⁻¹ • sysOf NB (OMT j) = sysOf NB (OMT I0) := by
  have hm := MulAction.mem_orbit (sysOf NB (OMT I0)) (⟨perm16 Q, hQ.2⟩ : Mg LT NL TL)
  rw [dceOk_orbit h] at hm
  obtain ⟨j, hj, e⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hm)
  refine ⟨j, Finset.mem_range.1 hj, ?_⟩
  rw [e, Subgroup.smul_def, inv_smul_smul]

theorem dceOk_f3 (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod) {wv : ℕ → G} (hw0 : wv 0 = 1)
    (hcov : ∀ D, ALIVE.testBit D = true → ∀ j < NO, ∃ D', ALIVE.testBit D' = true ∧
      ∃ a ∈ Nsub x NL TL, ∃ b ∈ Nsub x NL TL, wv D * tj LT HT GT NL TL x j = a * wv D' * b) :
    ∀ g ∈ Subgroup.closure (x '' {c | c < NL}), ∃ D, ALIVE.testBit D = true ∧
      ∃ a ∈ Nsub x NL TL, ∃ b ∈ Nsub x NL TL, g = a * wv D * b := by
  obtain ⟨hLv, hx⟩ := dceOk_rhoHyps h x hrels
  have key : ∀ c < NL, ∀ u : G, (∃ D, ALIVE.testBit D = true ∧
      ∃ a ∈ Nsub x NL TL, ∃ b ∈ Nsub x NL TL, u = a * wv D * b) →
      ∃ D, ALIVE.testBit D = true ∧
        ∃ a ∈ Nsub x NL TL, ∃ b ∈ Nsub x NL TL, u * x c = a * wv D * b := by
    intro c hc u ⟨D, hal, a, ha, b, hb, hu⟩
    by_cases hcT : c = TL
    · rw [hcT]
      obtain ⟨Q, hQ, hQb⟩ := N_code hLv hx hρ hb
      obtain ⟨j, hj, hjΩ⟩ := dceOk_orbit_idx h hQ
      have htc := dceOk_tconj h hN x hrels hρ hT hj hQ.1 hQ.2 hjΩ
      obtain ⟨D', hal', a', ha', b', hb', e⟩ := hcov D hal j hj
      refine ⟨D', hal', a * a', (Nsub x NL TL).mul_mem ha ha', b' * b,
        (Nsub x NL TL).mul_mem hb' hb, ?_⟩
      rw [hu, ← hQb]
      have e2 : rc LT NL TL x Q * x TL = tj LT HT GT NL TL x j * rc LT NL TL x Q := by
        rw [← htc]
        group
      have e3 : a * wv D * rc LT NL TL x Q * x TL =
          a * (wv D * tj LT HT GT NL TL x j) * rc LT NL TL x Q := by
        rw [mul_assoc (a * wv D), e2]
        group
      rw [e3, e]
      group
    · refine ⟨D, hal, a, ha, b * x c, (Nsub x NL TL).mul_mem hb
        (Subgroup.subset_closure ⟨c, ⟨hc, hcT⟩, rfl⟩), ?_⟩
      rw [hu]
      group
  intro g hg
  have hmain : ∀ u : G, (∃ D, ALIVE.testBit D = true ∧
      ∃ a ∈ Nsub x NL TL, ∃ b ∈ Nsub x NL TL, u = a * wv D * b) →
      ∃ D, ALIVE.testBit D = true ∧
        ∃ a ∈ Nsub x NL TL, ∃ b ∈ Nsub x NL TL, u * g = a * wv D * b := by
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨c, hc, rfl⟩ := hg
      exact key c hc
    | inv_mem g hg =>
      obtain ⟨c, hc, rfl⟩ := hg
      rw [inv_eq_of_mul_eq_one_right (hx c hc)]
      exact key c hc
    | one =>
      intro u hu
      rwa [mul_one]
    | mul g g' _ _ ih ih' =>
      intro u hu
      rw [← mul_assoc]
      exact ih' _ (ih u hu)
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := constOK_spec (dceOk_spec h).1
  have := hmain 1 ⟨0, h7, 1, (Nsub x NL TL).one_mem, 1, (Nsub x NL TL).one_mem, by
    rw [hw0]
    group⟩
  rwa [one_mul] at this

theorem dceOk_stab_reps (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM
      NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0
      S1 X0 X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    {wv : ℕ → G} (hw0 : wv 0 = 1)
    (hFM : ∀ i < nf, dJ (fct blk i) ≤ NO ∧ InM LT NL TL (dP (fct blk i)) ∧
      FM LT HT GT NL TL x wv (fct blk i)) {D : ℕ}
    (hfail : D ≠ 0 → stabVal blk SE STT nf nN D < failV) :
    ∃ R : Finset G, R.card ≤ idxD blk SE STT nf nN D ∧ (∀ r ∈ R, r ∈ Nsub x NL TL) ∧
      ∀ a ∈ Nsub x NL TL, ∀ b ∈ Nsub x NL TL, ∃ a' ∈ Nsub x NL TL, ∃ r ∈ R,
        a * wv D * b = a' * wv D * r := by
  classical
  unfold idxD
  by_cases hD0 : D = 0
  · subst hD0
    refine ⟨{1}, by simp, fun r hr => ?_, fun a ha b hb => ⟨a * b, (Nsub x NL TL).mul_mem ha hb,
      1, Finset.mem_singleton_self _, ?_⟩⟩
    · rw [Finset.mem_singleton.1 hr]
      exact (Nsub x NL TL).one_mem
    · rw [hw0]
      group
  rw [ite_eq_right hD0]
  obtain ⟨hn, hgens, hE, hval⟩ := stabVal_spec (hfail hD0)
  obtain ⟨hLv, hx⟩ := dceOk_rhoHyps h x hrels
  set GL := stGL (STT D)
  set n := stN (STT D)
  set Gp := packGens (fun k => dP (fct blk (glH GL k))) (glN GL)
  have hgk : ∀ k < glN GL, gk Gp k = dP (fct blk (glH GL k)) ∧
      InM LT NL TL (dP (fct blk (glH GL k))) ∧
      wv D * rc LT NL TL x (dP (fct blk (glH GL k))) * (wv D)⁻¹ ∈ Nsub x NL TL := by
    intro k hk
    obtain ⟨hlt, e1, e2, e3⟩ := hgens k hk
    obtain ⟨-, hπ, hfm⟩ := hFM _ hlt
    refine ⟨?_, hπ, ?_⟩
    · rw [gk_packGens _ hk, land_lit _ 64 m64 rfl, Nat.mod_eq_of_lt hπ.1.1]
    · unfold FM RelN at hfm
      rw [e1, e2, e3] at hfm
      unfold tv at hfm
      rw [ite_eq_left rfl] at hfm
      have e : wv D * rc LT NL TL x (dP (fct blk (glH GL k))) * (wv D)⁻¹ =
          (wv D * 1 * (wv D * rc LT NL TL x (dP (fct blk (glH GL k))))⁻¹)⁻¹ := by
        group
      rw [e]
      exact (Nsub x NL TL).inv_mem hfm
  have hGIsP : ∀ k < glN GL, IsP (gk Gp k) := fun k hk => by
    rw [(hgk k hk).1]
    exact (hgk k hk).2.1.1
  obtain ⟨hE1, hE2, -⟩ := enum_sound hE hGIsP
  have hSM : Tg Gp (glN GL) ≤ Mg LT NL TL := by
    rw [Tg, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [(hgk k hk).1]
    exact (hgk k hk).2.1.2
  have hcard : n ≤ Nat.card (Tg Gp (glN GL)) := by
    let E : Finset (Equiv.Perm (Fin 16)) :=
      (Finset.range n).image fun i => perm16 (eCode SE (stOff (STT D)) i)
    have hEc : E.card = n := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj e
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact hE2 i hi j hj (perm16_inj (hE1 i hi).1 (hE1 j hj).1 e)
    have hsub : (E : Set (Equiv.Perm (Fin 16))) ⊆
        (Tg Gp (glN GL) : Set (Equiv.Perm (Fin 16))) := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hg
      exact (Submonoid.closure_le (S := (Tg Gp (glN GL)).toSubmonoid)).2 Subgroup.subset_closure
        (hE1 i (Finset.mem_range.1 hi)).2
    change n ≤ Nat.card ((Tg Gp (glN GL) : Set (Equiv.Perm (Fin 16))))
    rw [Nat.card_coe_set_eq, ← hEc, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  set SM := (Tg Gp (glN GL)).subgroupOf (Mg LT NL TL)
  have hSMc : Nat.card SM = Nat.card (Tg Gp (glN GL)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  have hidx : SM.index ≤ nN / n := by
    have hc := Subgroup.card_mul_index SM
    rw [hSMc, dceOk_card h hN] at hc
    rw [Nat.le_div_iff_mul_le hn, ← hc]
    exact (Nat.mul_le_mul_left SM.index hcard).trans_eq (Nat.mul_comm _ _)
  have hsurj := rhoM_cod_surj hLv hx hρ
  have hNf : Finite (Nsub x NL TL) := (N_fin hLv hx hρ).1
  have hHidx : (SM.map ((rhoM LT NL TL x).codRestrict (Nsub x NL TL)
      (rhoM_mem hLv hx hρ))).index ≤ SM.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd _ hsurj)
  have key : ∀ g, g ∈ Tg Gp (glN GL) → ∀ hm : g ∈ Mg LT NL TL,
      wv D * rhoM LT NL TL x ⟨g, hm⟩ * (wv D)⁻¹ ∈ Nsub x NL TL := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      intro hm
      have hy : ((⟨_, hm⟩ : Mg LT NL TL) : Equiv.Perm (Fin 16)) =
          perm16 (dP (fct blk (glH GL k))) := congrArg perm16 (hgk k hk).1
      rw [← rc_eq ⟨_, hm⟩ hy]
      exact (hgk k hk).2.2
    | one =>
      intro hm
      have e : (⟨1, hm⟩ : Mg LT NL TL) = 1 := rfl
      rw [e, map_one, mul_one, mul_inv_cancel]
      exact (Nsub x NL TL).one_mem
    | mul g g' hg hg' ih ih' =>
      intro hm
      have e : (⟨g * g', hm⟩ : Mg LT NL TL) = ⟨g, hSM hg⟩ * ⟨g', hSM hg'⟩ := rfl
      have e2 : ∀ a b c : G, a * (b * c) * a⁻¹ = a * b * a⁻¹ * (a * c * a⁻¹) := fun a b c => by
        group
      rw [e, map_mul, e2]
      exact (Nsub x NL TL).mul_mem (ih (hSM hg)) (ih' (hSM hg'))
    | inv g hg ih =>
      intro hm
      have e : (⟨g⁻¹, hm⟩ : Mg LT NL TL) = (⟨g, hSM hg⟩)⁻¹ := rfl
      have e2 : ∀ a b : G, a * b⁻¹ * a⁻¹ = (a * b * a⁻¹)⁻¹ := fun a b => by group
      rw [e, map_inv, e2]
      exact (Nsub x NL TL).inv_mem (ih (hSM hg))
  have hH : ∀ k ∈ SM.map ((rhoM LT NL TL x).codRestrict (Nsub x NL TL) (rhoM_mem hLv hx hρ)),
      wv D * ((k : Nsub x NL TL) : G) * (wv D)⁻¹ ∈ Nsub x NL TL := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hk
    rw [Subgroup.mem_subgroupOf] at hy
    exact key _ hy y.2
  obtain ⟨R, hRc, hRN, hR⟩ := dcoset_reps (Nsub x NL TL) (wv D) _ hH
  exact ⟨R, hval ▸ hRc.trans (hHidx.trans hidx), hRN, hR⟩

theorem dceOk_bound (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod) :
    Finite (Subgroup.closure (x '' {c | c < NL})) ∧
      Nat.card (Subgroup.closure (x '' {c | c < NL})) ≤ nN * SUMIDX := by
  classical
  obtain ⟨hLv, hx⟩ := dceOk_rhoHyps h x hrels
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, h14, -, -, -, -, -, -, -, -, -, -, -, -, h27,
    h28, -⟩ := dceOk_spec h
  rw [Nat.blt_eq] at h27
  rw [Nat.beq_eq] at h28
  have hA := (constOK_spec h1).2.2.2.2.2.1
  obtain ⟨nxf, -, -, hf⟩ := dceOk_facts h
  obtain ⟨wv, hw0, hwT⟩ := exists_tree_w nf (fun i => nxf (i + 1) = nxf i + 1)
    (fun i => dD (fct blk i)) (fun i => dDp (fct blk i))
    (fun i => tv LT HT GT NL TL x (dJ (fct blk i)))
    (fun i hi e => by
      have e' : nxf (i + 1) = nxf i + 1 := e
      have hfi := hf i hi
      rw [e'] at hfi
      have ht := FactSem_tree hfi
      rw [ht.2.1]
      exact ht.2.2.1)
    (fun i hi i' hi' e e' hc => tree_unique hf hi hi' e e' hc)
  have hFM := dceOk_facts_mean h hN x hrels hρ hT hf hw0 hwT
  have hU := dceOk_f3 h hN x hrels hρ hT hw0 (dceOk_cover_mean h hN x hrels hρ hT hFM)
  set A := (Finset.range ND).filter fun D => ALIVE.testBit D = true
  have hsum : ∑ D ∈ A, idxD blk SE STT nf nN D = SUMIDX := by
    rw [← h28, indexSum_eq (by simpa using h14)]
  have hmemA : ∀ D, ALIVE.testBit D = true → D ∈ A := fun D hal =>
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (alive_lt hA hal), hal⟩
  have hfail : ∀ D, ALIVE.testBit D = true → D ≠ 0 → stabVal blk SE STT nf nN D < failV := by
    intro D hal hD0
    have hle := Finset.single_le_sum (f := idxD blk SE STT nf nN) (fun _ _ => Nat.zero_le _)
      (hmemA D hal)
    rw [hsum] at hle
    unfold idxD at hle
    rw [ite_eq_right hD0] at hle
    omega
  have hreps : ∀ D, ∃ R : Finset G, ALIVE.testBit D = true →
      R.card ≤ idxD blk SE STT nf nN D ∧ (∀ r ∈ R, r ∈ Nsub x NL TL) ∧
      ∀ a ∈ Nsub x NL TL, ∀ b ∈ Nsub x NL TL, ∃ a' ∈ Nsub x NL TL, ∃ r ∈ R,
        a * wv D * b = a' * wv D * r := by
    intro D
    by_cases hal : ALIVE.testBit D = true
    · obtain ⟨R, hR⟩ := dceOk_stab_reps h hN x hrels hρ hw0 hFM (hfail D hal)
      exact ⟨R, fun _ => hR⟩
    · exact ⟨∅, fun h' => absurd h' hal⟩
  choose R hR using hreps
  obtain ⟨hNfin, hNc⟩ := N_fin hLv hx hρ
  rw [dceOk_card h hN] at hNc
  obtain ⟨hfin, hcard⟩ := card_cover (Nsub x NL TL) A wv R (Subgroup.closure (x '' {c | c < NL}))
    (fun g hg => by
      obtain ⟨D, hal, a, ha, b, hb, rfl⟩ := hU g hg
      obtain ⟨a', ha', r, hr, e⟩ := (hR D hal).2.2 a ha b hb
      exact ⟨D, hmemA D hal, a', ha', r, hr, e⟩)
  refine ⟨hfin, hcard.trans ?_⟩
  calc ∑ D ∈ A, Nat.card (Nsub x NL TL) * (R D).card
      ≤ ∑ D ∈ A, nN * idxD blk SE STT nf nN D := Finset.sum_le_sum fun D hD =>
        Nat.mul_le_mul hNc (hR D (Finset.mem_filter.1 hD).2).1
    _ = nN * SUMIDX := by rw [← Finset.mul_sum, hsum]

end DceOk

end CFSG.Certificates.Co1D

end
