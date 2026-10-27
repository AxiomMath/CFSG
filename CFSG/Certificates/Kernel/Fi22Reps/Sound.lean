module

public import Certificates.Data.Kernel.Fi22Reps.Check
public import CFSG.Certificates.Kernel.Fi22Cls.Sound
import all CFSG.Certificates.Kernel.Fi22S0.Sound

public section

namespace CFSG.KD.Fi22Reps

open CFSG.KC.Enum CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KC.Fi22Reps CFSG.KD.Fi22S0 CFSG.KD.Fi22Cls
  CFSG.HardMathSupport.Foote.E27 CFSG.KD.SporCov
open CFSG.Sporadic.Fi22 (J a b conjPt idx_eq_iff a_inv conjPt_zero)
open CFSG.Sporadic.Fi22.S0 (nS)
open CFSG.HardMathSupport.Foote.E27.Fi22S0 (gJ)
open CFSG.Sporadic.Th (idx idx_lt idx_mul idx_one idx_inv_idx idx_idx_inv)

theorem bIf_cases {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem bNot {c : Bool} (h : Bool.rec (motive := fun _ => Bool) true false c = true) : c = false := by
  cases c
  · rfl
  · exact absurd h Bool.false_ne_true

theorem nbeq_false {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  cases e : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem xorB_ne {p q : Bool} (h : xorB p q = true) : p ≠ q := by
  revert h
  cases p <;> cases q <;> simp [xorB]

theorem xorB_false {p q : Bool} (h : xorB p q = false) : p = q := by
  revert h
  cases p <;> cases q <;> simp [xorB]


theorem repE_iff {P : ℕ} {g : J} : RepE P g ↔ ∀ x < 3510, ent P x = idx 3510 g x := Iff.rfl

@[expose] noncomputable def letJ (c : ℕ) : J := if c = 0 then a else if c = 1 then b else b⁻¹

theorem letJ_invL (c : ℕ) : letJ (invL c) = (letJ c)⁻¹ := by
  rcases c with _ | _ | c
  · have e : invL 0 = 0 := rfl
    rw [e]
    simp [letJ, a_inv]
  · have e : invL 1 = 2 := rfl
    rw [e]
    simp [letJ]
  · have e : invL (c + 2) = 1 := rfl
    rw [e]
    simp [letJ]

@[expose] noncomputable def wordE : ℕ → ℕ → J
  | 0, _ => 1
  | m + 1, W => letJ (Nat.land W 3) * wordE m (Nat.shiftRight W 2)

theorem wordE_succ (m W : ℕ) :
    wordE (m + 1) W = letJ (Nat.land W 3) * wordE m (Nat.shiftRight W 2) := rfl

theorem wAp_succ (LT : ℕ → ℕ) (m W x : ℕ) :
    wAp LT (m + 1) W x = ent (LT (Nat.land W 3)) (wAp LT m (Nat.shiftRight W 2) x) := by
  change strictN (wAp LT m (Nat.shiftRight W (nat_lit 2)) x)
    (fun y => ent (LT (Nat.land W (nat_lit 3))) y) = _
  rw [strictN_eq]

theorem wInv_succ (LT : ℕ → ℕ) (m W x : ℕ) :
    wInv LT (m + 1) W x = wInv LT m (Nat.shiftRight W 2) (ent (LT (invL (Nat.land W 3))) x) := by
  change strictN (ent (LT (invL (Nat.land W (nat_lit 3)))) x)
    (fun y => wInv LT m (Nat.shiftRight W (nat_lit 2)) y) = _
  rw [strictN_eq]

variable {LT : ℕ → ℕ}

theorem wAp_eq (hL : ∀ c, RepE (LT c) (letJ c)) :
    ∀ m W x, x < 3510 → wAp LT m W x = idx 3510 (wordE m W) x := by
  intro m
  induction m with
  | zero =>
    intro W x _
    change x = idx 3510 (1 : J) x
    rw [idx_one]
  | succ m ih =>
    intro W x hx
    rw [wAp_succ, ih _ x hx, hL _ _ (idx_lt _ hx), wordE_succ, idx_mul]

theorem wInv_eq (hL : ∀ c, RepE (LT c) (letJ c)) :
    ∀ m W x, x < 3510 → wInv LT m W x = idx 3510 (wordE m W)⁻¹ x := by
  intro m
  induction m with
  | zero =>
    intro W x _
    change x = idx 3510 (1 : J)⁻¹ x
    rw [inv_one, idx_one]
  | succ m ih =>
    intro W x hx
    rw [wInv_succ, hL _ _ hx, letJ_invL, ih _ _ (idx_lt _ hx), wordE_succ, mul_inv_rev, idx_mul]

@[expose] noncomputable def entE (e : ℕ) : J :=
  wordE (Nat.land e (nat_lit 31)) (Nat.shiftRight e (nat_lit 5))

theorem dE_eq (hL : ∀ c, RepE (LT c) (letJ c)) (e : ℕ) {p : ℕ} (hp : p < 3510) :
    dE LT e p = idx 3510 (entE e * a * (entE e)⁻¹) p := by
  unfold dE
  simp only [strictN_eq]
  have h0 : RepE (LT 0) a := hL 0
  rw [wInv_eq hL _ _ _ hp, h0 _ (idx_lt _ hp), wAp_eq hL _ _ _ (idx_lt _ (idx_lt _ hp)), idx_mul,
    idx_mul]
  rfl

theorem conjPt_idx {g : J} {v : ℕ} (hv : v < 3510) :
    conjPt (idx 3510 g v) = g * conjPt v * g⁻¹ :=
  ((idx_eq_iff hv (idx_lt g hv)).1 rfl).symm

theorem dE_wd {wd : ℕ → ℕ} (hL : ∀ c, RepE (LT c) (letJ c))
    (hw : ∀ v < 3510, wordC LT wd v = true) {v p : ℕ} (hv : v < 3510) (hp : p < 3510) :
    dE LT (wd v) p = idx 3510 (conjPt v) p := by
  have h := hw v hv
  unfold wordC at h
  simp only [sB_eq, beq_iff] at h
  rw [wAp_eq hL _ _ 0 (by norm_num)] at h
  have e : conjPt v = entE (wd v) * a * (entE (wd v))⁻¹ := by
    rw [← conjPt_zero, ← conjPt_idx (v := 0) (by norm_num)]
    unfold entE
    rw [h]
  rw [dE_eq hL _ hp, e]

theorem idx_conjPt_iff {u w : ℕ} (hw : w < 3510) :
    idx 3510 (conjPt u) w = w ↔ Commute (conjPt u) (conjPt w) := by
  rw [idx_eq_iff hw hw, mul_inv_eq_iff_eq_mul]
  rfl

theorem cmE_iff {wd : ℕ → ℕ} (hL : ∀ c, RepE (LT c) (letJ c))
    (hw : ∀ v < 3510, wordC LT wd v = true) {u w : ℕ} (hu : u < 3510) (hw' : w < 3510) :
    cmE LT (wd u) w = true ↔ Commute (conjPt u) (conjPt w) := by
  unfold cmE
  rw [beq_iff, dE_wd hL hw hu hw', idx_conjPt_iff hw']

theorem rep_path {RX gR pp pj nd : ℕ → ℕ} {s dep : ℕ} {par : Array (ℕ × ℕ)}
    (hg : ∀ j < 3, RepE (gR j) (gJ j))
    (hpar : ∀ i < nS, (par[i]!).1 = pp i ∧ (par[i]!).2 = pj i)
    (hxt : ∀ t < dep, xtC RX gR pp pj nd s (t + 1) = true) (hend : nd dep < nS) :
    ∀ t < dep, RepE (RX (s + t)) (tabElt gJ par (nd (t + 1))) := by
  have hst : ∀ t < dep, pp (nd (t + 1)) = nd t ∧ nd t < nd (t + 1) ∧ pj (nd (t + 1)) < 3 ∧
      (t = 0 → nd t = 0 ∧ RX s = gR (pj (nd (t + 1)))) ∧
      (t ≠ 0 → compOK (RX (s + t)) (gR (pj (nd (t + 1)))) (RX (s + (t - 1))) = true) := by
    intro t ht
    have h := hxt t ht
    unfold xtC at h
    simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h
    have e1 : Nat.sub (t + 1) 1 = t := Nat.add_sub_cancel t 1
    have e2 : Nat.add s (Nat.sub (t + 1) 1) = s + t := by rw [e1]; rfl
    have e3 : Nat.add s (Nat.sub (t + 1) 2) = s + (t - 1) := by
      change s + (t + 1 - 2) = s + (t - 1)
      omega
    rw [e1] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, h3, fun ht0 => ?_, fun ht0 => ?_⟩
    · rcases bIf_cases h4 with ⟨-, h5⟩ | ⟨hc, -⟩
      · simp only [Bool.and_eq_true, beq_iff] at h5
        exact h5
      · exact absurd (by rw [ht0]; rfl) (Bool.eq_false_iff.1 hc)
    · rcases bIf_cases h4 with ⟨hc, -⟩ | ⟨-, h5⟩
      · exact absurd (by have := (beq_iff _ _).1 hc; omega) ht0
      · rw [e3] at h5
        exact h5
  have hmono : ∀ d t, t + d ≤ dep → nd t ≤ nd (t + d) := by
    intro d
    induction d with
    | zero => intro t _; exact le_rfl
    | succ d ih =>
      intro t ht
      exact le_trans (ih t (by omega)) (le_of_lt (hst (t + d) (by omega)).2.1)
  have hlt : ∀ t ≤ dep, nd t < nS := fun t ht =>
    lt_of_le_of_lt (by have := hmono (dep - t) t (by omega); rwa [Nat.add_sub_cancel' ht] at this)
      hend
  intro t
  induction t with
  | zero =>
    intro hd
    obtain ⟨h1, h2, h3, h4, -⟩ := hst 0 hd
    obtain ⟨h0, hR⟩ := h4 rfl
    obtain ⟨e1, e2⟩ := hpar _ (hlt 1 (by omega))
    have hp : (par[nd 1]!).1 < nd 1 := by rw [e1, h1]; exact h2
    rw [Nat.add_zero, hR, tabElt_succ gJ par hp, e1, e2, h1, h0, tabElt_zero, mul_one]
    exact hg _ h3
  | succ t ih =>
    intro hd
    obtain ⟨h1, h2, h3, -, h5⟩ := hst (t + 1) hd
    have hc := h5 (by omega)
    rw [Nat.add_sub_cancel] at hc
    obtain ⟨e1, e2⟩ := hpar _ (hlt (t + 2) (by omega))
    have hp : (par[nd (t + 1 + 1)]!).1 < nd (t + 1 + 1) := by rw [e1, h1]; exact h2
    intro x hx
    have hc' := beq_iff _ _ |>.1 (allBelow_specF hc (by norm_num) x hx)
    rw [hc', tabElt_succ gJ par hp, e1, e2, h1, idx_mul, ih (by omega) x hx,
      hg _ h3 _ (idx_lt _ hx)]

theorem idx_inv_of_fix {g : J} {v : ℕ} (h : idx 3510 g v = v) : idx 3510 g⁻¹ v = v :=
  calc idx 3510 g⁻¹ v = idx 3510 g⁻¹ (idx 3510 g v) := by rw [h]
    _ = v := idx_inv_idx g v

@[expose] def fixP (x : J) (Q : ℕ → Prop) (h : J) : Prop :=
  Commute h x ∧ (∀ v < 3510, idx 3510 x v = v → idx 3510 h v = v) ∧ ∀ v, Q v → idx 3510 h v = v

theorem fixP_mul {x g h : J} {Q : ℕ → Prop} (hg : fixP x Q g) (hh : fixP x Q h) :
    fixP x Q (g * h) := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨h1, h2, h3⟩ := hh
  refine ⟨g1.mul_left h1, fun v hv hx => ?_, fun v hv => ?_⟩
  · rw [idx_mul, h2 v hv hx, g2 v hv hx]
  · rw [idx_mul, h3 v hv, g3 v hv]

theorem fixP_one {x : J} {Q : ℕ → Prop} : fixP x Q 1 :=
  ⟨Commute.one_left x, fun v _ _ => idx_one v, fun v _ => idx_one v⟩

theorem fixP_inv {x h : J} {Q : ℕ → Prop} (hh : fixP x Q h) : fixP x Q h⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := hh
  have e : h⁻¹ * x = x * h⁻¹ := by
    calc h⁻¹ * x = h⁻¹ * (x * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * x) * h⁻¹ := by rw [h1.eq]
      _ = x * h⁻¹ := by group
  exact ⟨e, fun v hv hx => idx_inv_of_fix (h2 v hv hx), fun v hv => idx_inv_of_fix (h3 v hv)⟩

@[expose] def fixG (x : J) (Q : ℕ → Prop) : Subgroup J where
  carrier := {h | fixP x Q h}
  mul_mem' := fun hg hh => fixP_mul hg hh
  one_mem' := fixP_one
  inv_mem' := fun hh => fixP_inv hh

theorem mem_fixG {x h : J} {Q : ℕ → Prop} : h ∈ fixG x Q ↔ Commute h x ∧
    (∀ v < 3510, idx 3510 x v = v → idx 3510 h v = v) ∧ ∀ v, Q v → idx 3510 h v = v := Iff.rfl

theorem card_le_orbit (K K' : Subgroup J) (b : ℕ) (S : Finset ℕ)
    (hS : ∀ h ∈ K, idx 3510 h b ∈ S) (hK' : ∀ h ∈ K, idx 3510 h b = b → h ∈ K') :
    Nat.card K ≤ S.card * Nat.card K' := by
  classical
  have := CFSG.HardMathSupport.Foote.E27.Fi22S0.finite_J
  have := Fintype.ofFinite J
  rw [natCard_eq_filter K, natCard_eq_filter K']
  set U := Finset.univ.filter (· ∈ K)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun h => idx 3510 h b) (t := S)
    (fun h hh => hS h (Finset.mem_filter.1 hh).2)]
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hne : (U.filter fun h => idx 3510 h b = y).Nonempty
  · obtain ⟨g0, hg0⟩ := hne
    obtain ⟨hg0U, hg0y⟩ := Finset.mem_filter.1 hg0
    have hg0K : g0 ∈ K := (Finset.mem_filter.1 hg0U).2
    refine Finset.card_le_card_of_injOn (fun h => g0⁻¹ * h) ?_ ?_
    · intro h hh
      obtain ⟨hU, hy⟩ := Finset.mem_filter.1 hh
      have hK : h ∈ K := (Finset.mem_filter.1 hU).2
      have hm : g0⁻¹ * h ∈ K := K.mul_mem (K.inv_mem hg0K) hK
      have hb : idx 3510 (g0⁻¹ * h) b = b := by
        rw [idx_mul, hy, ← hg0y, idx_inv_idx]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hK' _ hm hb⟩
    · intro g _ h _ e
      exact mul_left_cancel e
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty]
    exact Nat.zero_le _

variable {wd : ℕ → ℕ} {X : ℕ} {x : J}

@[expose] def preQ (P : ℕ → ℕ) (n : ℕ) (v : ℕ) : Prop := ∃ j < n, v = ptE (P j)

theorem phi_cases {P nL : ℕ → ℕ} {L m : ℕ} (h : phiC LT wd X P nL L m = true) :
    ptE (P m) < 3510 ∧ (ent X (ptE (P m)) = ptE (P m) ∨ (∃ u < L, nL u = m) ∨
      (∃ u < m, ∃ w < m, ptE (P m) = dE LT (wd (ptE (P u))) (ptE (P w))) ∨
      (∃ u < m, ptE (P m) = ent X (ptE (P u)))) := by
  unfold phiC at h
  simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rcases bIf_cases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
  · exact Or.inl ((beq_iff _ _).1 h3)
  rcases bIf_cases h3 with ⟨-, h4⟩ | ⟨-, h4⟩
  · simp only [Bool.and_eq_true, blt_iff, beq_iff] at h4
    exact Or.inr (Or.inl ⟨_, h4.1, h4.2⟩)
  rcases bIf_cases h4 with ⟨-, h5⟩ | ⟨-, h5⟩
  · simp only [Bool.and_eq_true, blt_iff, beq_iff] at h5
    exact Or.inr (Or.inr (Or.inl ⟨_, h5.1, _, h5.2.1, h5.2.2⟩))
  · simp only [Bool.and_eq_true, blt_iff, beq_iff] at h5
    exact Or.inr (Or.inr (Or.inr ⟨_, h5.1, h5.2⟩))

theorem phi_tag0 {P nL : ℕ → ℕ} {L m : ℕ} (h : phiC LT wd X P nL L m = true)
    (ht : Nat.land (Nat.shiftRight (P m) 12) 3 = 0) : ent X (ptE (P m)) = ptE (P m) := by
  unfold phiC at h
  simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h
  rcases bIf_cases h.2 with ⟨-, h3⟩ | ⟨hc, -⟩
  · exact (beq_iff _ _).1 h3
  · exact absurd ht (Nat.ne_of_beq_eq_false hc)

theorem closure_fix {P nL : ℕ → ℕ} {L nP : ℕ} (hL : ∀ c, RepE (LT c) (letJ c))
    (hw : ∀ v < 3510, wordC LT wd v = true) (hX : RepE X x)
    (hphi : ∀ m < nP, phiC LT wd X P nL L m = true) {Q : ℕ → Prop} {h : J} (hh : h ∈ fixG x Q)
    {m : ℕ} (hlev : ∀ u < L, nL u ≤ m → idx 3510 h (ptE (P (nL u))) = ptE (P (nL u))) :
    ∀ j ≤ m, j < nP → idx 3510 h (ptE (P j)) = ptE (P j) := by
  obtain ⟨h1, h2, -⟩ := mem_fixG.1 hh
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjm hjn
    obtain ⟨hp, hc⟩ := phi_cases (hphi j hjn)
    rcases hc with c | ⟨u, hu, e⟩ | ⟨u, hu, w, hw', e⟩ | ⟨u, hu, e⟩
    · rw [hX _ hp] at c
      exact h2 _ hp c
    · rw [← e]
      exact hlev u hu (by omega)
    · have hpu := (phi_cases (hphi u (by omega))).1
      have hpw := (phi_cases (hphi w (by omega))).1
      have fu := ih u hu (by omega) (by omega)
      have fw := ih w hw' (by omega) (by omega)
      rw [e, dE_wd hL hw hpu hpw]
      have hc : h * conjPt (ptE (P u)) = conjPt (ptE (P u)) * h := by
        have := conjPt_idx (g := h) hpu
        rw [fu] at this
        calc h * conjPt (ptE (P u)) = h * conjPt (ptE (P u)) * h⁻¹ * h := by group
          _ = conjPt (ptE (P u)) * h := by rw [← this]
      rw [← idx_mul, hc, idx_mul, fw]
    · have hpu := (phi_cases (hphi u (by omega))).1
      have fu := ih u hu (by omega) (by omega)
      rw [e, hX _ hpu, ← idx_mul, h1.eq, idx_mul, fu]

theorem lev_cases {P cd cl cb : ℕ → ℕ} {n s f1 f2 w : ℕ}
    (h : levC LT wd X P cd cl cb n s f1 f2 w = true) :
    (∃ v < s, cl v = w) ∨ (∃ v < n, ptE (P v) = w ∧ w ≠ ptE (P n)) ∨
      (∃ v < n, cmE LT (wd (ptE (P v))) w ≠ Nat.beq (cb v) 1) ∨
      cmE LT (wd w) (ent X w) ≠ Nat.beq f1 1 ∨
      (f2 = 1 ∧ ∃ v < 3510, dE LT (wd w) (ent X v) = v) := by
  unfold levC at h
  simp only [sB_eq, bRec_and] at h
  rcases bIf_cases h with ⟨-, h0⟩ | ⟨-, h0⟩
  · simp only [Bool.and_eq_true, blt_iff, beq_iff] at h0
    exact Or.inl ⟨_, h0.1, h0.2⟩
  rcases bIf_cases h0 with ⟨-, h1⟩ | ⟨-, h1⟩
  · simp only [Bool.and_eq_true, blt_iff, beq_iff] at h1
    obtain ⟨c1, c2, c3⟩ := h1
    exact Or.inr (Or.inl ⟨_, c1, c2, Nat.ne_of_beq_eq_false (bNot c3)⟩)
  rcases bIf_cases h1 with ⟨-, h2⟩ | ⟨-, h2⟩
  · simp only [Bool.and_eq_true, blt_iff] at h2
    exact Or.inr (Or.inr (Or.inl ⟨_, h2.1, xorB_ne h2.2⟩))
  rcases bIf_cases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl (xorB_ne h3))))
  · simp only [Bool.and_eq_true, blt_iff, beq_iff] at h3
    obtain ⟨-, c1, c2, c3⟩ := h3
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c1, _, c2, c3⟩)))

theorem comm_idx_iff (h : J) {u v : ℕ} (hu : u < 3510) (hv : v < 3510) :
    Commute (conjPt (idx 3510 h u)) (conjPt (idx 3510 h v)) ↔ Commute (conjPt u) (conjPt v) := by
  rw [conjPt_idx hu, conjPt_idx hv]
  have e1 : h * conjPt u * h⁻¹ * (h * conjPt v * h⁻¹) = h * (conjPt u * conjPt v) * h⁻¹ := by
    group
  have e2 : h * conjPt v * h⁻¹ * (h * conjPt u * h⁻¹) = h * (conjPt v * conjPt u) * h⁻¹ := by
    group
  unfold Commute SemiconjBy
  rw [e1, e2]
  exact ⟨fun e => mul_left_cancel (mul_right_cancel e), fun e => by rw [e]⟩

theorem cell_mem {P cd cl cb : ℕ → ℕ} {n s f1 f2 : ℕ} (hL : ∀ c, RepE (LT c) (letJ c))
    (hw : ∀ v < 3510, wordC LT wd v = true) (hX : RepE X x)
    (hPl : ∀ m ≤ n, ptE (P m) < 3510)
    (hlev : ∀ w < 3510, levC LT wd X P cd cl cb n s f1 f2 w = true)
    (hlevB : ∀ m < n + 1, levB LT wd X P cb n f1 m = true)
    (hscan : ∀ p < 3510, scanC LT wd X P n f2 p = true) {h : J} (hh : h ∈ fixG x (preQ P n)) :
    idx 3510 h (ptE (P n)) ∈ (Finset.range s).image cl := by
  obtain ⟨h1, -, h3⟩ := mem_fixG.1 hh
  have hbl : ptE (P n) < 3510 := hPl n le_rfl
  have hwl : idx 3510 h (ptE (P n)) < 3510 := idx_lt _ hbl
  have hB : ∀ m < n + 1,
      (m = 0 → cmE LT (wd (ptE (P n))) (ent X (ptE (P n))) = Nat.beq f1 1) ∧
      (m < n → cmE LT (wd (ptE (P m))) (ptE (P n)) = Nat.beq (cb m) 1) := by
    intro m hm
    have h0 := hlevB m hm
    unfold levB at h0
    simp only [sB_eq, bRec_and, Bool.and_eq_true] at h0
    obtain ⟨h01, h02⟩ := h0
    refine ⟨fun hm0 => ?_, fun hmn => ?_⟩
    · rcases bIf_cases h01 with ⟨-, h5⟩ | ⟨hc, -⟩
      · exact xorB_false (bNot h5)
      · exact absurd ((beq_iff _ _).2 hm0) (by rw [hc]; exact Bool.false_ne_true)
    · rcases bIf_cases h02 with ⟨-, h5⟩ | ⟨hc, -⟩
      · exact xorB_false (bNot h5)
      · exact absurd ((blt_iff _ _).2 hmn) (by rw [hc]; exact Bool.false_ne_true)
  rcases lev_cases (hlev _ hwl) with ⟨v, hv, e⟩ | ⟨v, hv, e, hne⟩ | ⟨v, hv, hne⟩ | hne |
      ⟨hf2, v, hv, e⟩
  · exact Finset.mem_image.2 ⟨v, Finset.mem_range.2 hv, e⟩
  · exfalso
    have hfix := h3 _ ⟨v, hv, rfl⟩
    apply hne
    have e' : idx 3510 h (ptE (P v)) = idx 3510 h (ptE (P n)) := by rw [hfix, e]
    have := congrArg (idx 3510 h⁻¹) e'
    rw [idx_inv_idx, idx_inv_idx] at this
    rw [← e, this]
  · exfalso
    have hpv : ptE (P v) < 3510 := hPl v (by omega)
    apply hne
    rw [← (hB v (by omega)).2 hv]
    have hfix := h3 _ ⟨v, hv, rfl⟩
    have e3 := comm_idx_iff h hpv hbl
    rw [hfix] at e3
    rw [Bool.eq_iff_iff, cmE_iff hL hw hpv hwl, cmE_iff hL hw hpv hbl, e3]
  · exfalso
    apply hne
    rw [← (hB 0 (by omega)).1 rfl]
    have hxw : ent X (idx 3510 h (ptE (P n))) = idx 3510 h (ent X (ptE (P n))) := by
      rw [hX _ hwl, hX _ hbl, ← idx_mul, ← idx_mul, h1.eq]
    have hxb : ent X (ptE (P n)) < 3510 := by rw [hX _ hbl]; exact idx_lt _ hbl
    rw [hxw, Bool.eq_iff_iff, cmE_iff hL hw hwl (idx_lt _ hxb), cmE_iff hL hw hbl hxb,
      comm_idx_iff h hbl hxb]
  · exfalso
    have hp : idx 3510 h⁻¹ v < 3510 := idx_lt _ hv
    have hs := hscan (idx 3510 h⁻¹ v) hp
    unfold scanC at hs
    rcases bIf_cases hs with ⟨-, h5⟩ | ⟨hc, -⟩
    · have h6 := Nat.ne_of_beq_eq_false (bNot h5)
      rw [hX _ hp, dE_wd hL hw hbl (idx_lt _ hp)] at h6
      rw [hX _ hv, dE_wd hL hw hwl (idx_lt _ hv), conjPt_idx hbl] at e
      have hx' : h * x * h⁻¹ = x := by rw [h1.eq, mul_inv_cancel_right]
      have ey : h * (conjPt (ptE (P n)) * x) * h⁻¹ = h * conjPt (ptE (P n)) * h⁻¹ * x := by
        calc h * (conjPt (ptE (P n)) * x) * h⁻¹
            = h * conjPt (ptE (P n)) * h⁻¹ * (h * x * h⁻¹) := by group
          _ = h * conjPt (ptE (P n)) * h⁻¹ * x := by rw [hx']
      have e1 : idx 3510 (h * (conjPt (ptE (P n)) * x) * h⁻¹) v = v := by
        rw [ey, idx_mul]
        exact e
      have e2 := congrArg (idx 3510 h⁻¹) e1
      rw [idx_mul, idx_mul, idx_inv_idx, idx_mul] at e2
      exact h6 e2
    · exact absurd ((beq_iff _ _).2 hf2) (by rw [hc]; exact Bool.false_ne_true)

theorem card_fixG_le {P nL s f1 f2 : ℕ → ℕ} {cd cl cb : ℕ → ℕ → ℕ} {L nP : ℕ} {bpos : ℕ → ℕ}
    (hL : ∀ c, RepE (LT c) (letJ c)) (hw : ∀ v < 3510, wordC LT wd v = true) (hX : RepE X x)
    (hphi : ∀ m < nP, phiC LT wd X P nL L m = true)
    (hpre : ∀ j < nL 0, ent X (ptE (P j)) = ptE (P j)) (hL0 : 0 < L)
    (hinc : ∀ u, u + 1 < L → nL u < nL (u + 1)) (hlast : nL (L - 1) < nP)
    (hbase : ∀ t < 5, bpos t < nP ∧ ptE (P (bpos t)) = bp t)
    (hlev : ∀ u < L, ∀ w < 3510, levC LT wd X P (cd u) (cl u) (cb u) (nL u) (s u) (f1 u) (f2 u) w =
      true)
    (hlevB : ∀ u < L, ∀ m < nL u + 1, levB LT wd X P (cb u) (nL u) (f1 u) m = true)
    (hscan : ∀ u < L, ∀ p < 3510, scanC LT wd X P (nL u) (f2 u) p = true) :
    Nat.card (fixG x fun _ => False) ≤ ∏ u ∈ Finset.range L, s u := by
  have := CFSG.HardMathSupport.Foote.E27.Fi22S0.finite_J
  have hmono : ∀ u u', u < u' → u' < L → nL u < nL u' := by
    intro u u' huu' hu'
    induction u' with
    | zero => omega
    | succ u' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 huu' with h' | rfl
      · exact lt_trans (ih h' (by omega)) (hinc u' hu')
      · exact hinc u hu'
  have hle : ∀ u u', u ≤ u' → u' < L → nL u ≤ nL u' := fun u u' h1 h2 => by
    rcases Nat.lt_or_ge u u' with h' | h'
    · exact le_of_lt (hmono _ _ h' h2)
    · rw [show u = u' by omega]
  have hnP : ∀ u < L, nL u < nP := fun u hu => lt_of_le_of_lt (hle u (L - 1) (by omega) (by omega))
    hlast
  have hPl : ∀ m < nP, ptE (P m) < 3510 := fun m hm => (phi_cases (hphi m hm)).1
  obtain ⟨pos, hpl, hpg⟩ : ∃ pos : ℕ → ℕ, (∀ u < L, pos u = nL u) ∧ (∀ u, L ≤ u → pos u = nP) :=
    ⟨fun u => if u < L then nL u else nP, fun u hu => if_pos hu, fun u hu => if_neg (by omega)⟩
  have hcell : ∀ u < L, ∀ h ∈ fixG x (preQ P (nL u)),
      idx 3510 h (ptE (P (nL u))) ∈ (Finset.range (s u)).image (cl u) := fun u hu h hh =>
    cell_mem hL hw hX (fun m hm => hPl m (by have := hnP u hu; omega)) (hlev u hu) (hlevB u hu)
      (hscan u hu) hh
  have hstep : ∀ u < L, ∀ h ∈ fixG x (preQ P (nL u)),
      idx 3510 h (ptE (P (nL u))) = ptE (P (nL u)) → h ∈ fixG x (preQ P (pos (u + 1))) := by
    intro u hu h hh hb
    obtain ⟨h1, h2, h3⟩ := mem_fixG.1 hh
    have hfix : ∀ j ≤ nL u, idx 3510 h (ptE (P j)) = ptE (P j) := by
      intro j hj
      rcases Nat.lt_or_ge j (nL u) with h' | h'
      · exact h3 _ ⟨j, h', rfl⟩
      · rw [show j = nL u by omega]; exact hb
    refine mem_fixG.2 ⟨h1, h2, ?_⟩
    rintro v ⟨j, hj, rfl⟩
    have hjP : j < nP := by
      by_cases h' : u + 1 < L
      · rw [hpl _ h'] at hj
        exact lt_trans hj (hnP _ h')
      · rwa [hpg _ (by omega)] at hj
    refine closure_fix (m := j) hL hw hX hphi hh (fun u' hu' hle' => hfix _ ?_) j le_rfl hjP
    rcases Nat.lt_or_ge u u' with h' | h'
    · exfalso
      have hu1 : u + 1 < L := by omega
      rw [hpl _ hu1] at hj
      have := hle (u + 1) u' (by omega) hu'
      omega
    · exact hle u' u h' hu
  have key : ∀ d u, u + d = L → Nat.card (fixG x (preQ P (pos u))) ≤
      ∏ t ∈ Finset.Ico u L, s t := by
    intro d
    induction d with
    | zero =>
      intro u hu
      rw [hpg u (by omega), show u = L by omega, Finset.Ico_self, Finset.prod_empty]
      have hbot : fixG x (preQ P nP) = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro h hh
        obtain ⟨-, -, h3⟩ := mem_fixG.1 hh
        refine sep_bp h fun t ht => ?_
        obtain ⟨hb1, hb2⟩ := hbase t ht
        rw [← hb2]
        exact h3 _ ⟨_, hb1, rfl⟩
      rw [hbot, Subgroup.card_bot]
    | succ d ih =>
      intro u hu
      have hu' : u < L := by omega
      rw [hpl u hu', Finset.prod_eq_prod_Ico_succ_bot hu']
      have h1 := card_le_orbit (fixG x (preQ P (nL u))) (fixG x (preQ P (pos (u + 1))))
        (ptE (P (nL u))) ((Finset.range (s u)).image (cl u)) (hcell u hu') (hstep u hu')
      have h2 : ((Finset.range (s u)).image (cl u)).card ≤ s u :=
        le_trans Finset.card_image_le (by rw [Finset.card_range])
      exact le_trans h1 (Nat.mul_le_mul h2 (ih (u + 1) (by omega)))
  have hstart : fixG x (fun _ => False) ≤ fixG x (preQ P (pos 0)) := by
    intro h hh
    obtain ⟨h1, h2, -⟩ := mem_fixG.1 hh
    refine mem_fixG.2 ⟨h1, h2, ?_⟩
    rintro v ⟨j, hj, rfl⟩
    rw [hpl 0 hL0] at hj
    have hjP : j < nP := lt_trans hj (hnP 0 hL0)
    have := hpre j hj
    rw [hX _ (hPl j hjP)] at this
    exact h2 _ (hPl j hjP) this
  have := key L 0 (by omega)
  rw [Finset.range_eq_Ico]
  exact le_trans (Subgroup.card_le_of_le hstart) this

theorem fix_pos {P fp : ℕ → ℕ} {nF : ℕ} (hX : RepE X x)
    (hfix : ∀ w < 3510, fixC X P fp nF w = true) {w : ℕ} (hw : w < 3510)
    (hxw : idx 3510 x w = w) : fp w < nF ∧ ptE (P (fp w)) = w := by
  have h := hfix w hw
  unfold fixC at h
  rcases bIf_cases h with ⟨-, h5⟩ | ⟨hc, -⟩
  · simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h5
    exact h5
  · rw [hX _ hw, hxw, Nat.beq_refl] at hc
    exact absurd hc (by decide)

theorem fpf_of {P fp : ℕ → ℕ} (hX : RepE X x) (hfix : ∀ w < 3510, fixC X P fp 0 w = true)
    {w : ℕ} (hw : w < 3510) : idx 3510 x w ≠ w := fun hxw =>
  absurd (fix_pos hX hfix hw hxw).1 (Nat.not_lt_zero _)

theorem sep_of {P fp sw : ℕ → ℕ} {nF : ℕ} (hL : ∀ c, RepE (LT c) (letJ c))
    (hw : ∀ v < 3510, wordC LT wd v = true) (hX : RepE X x)
    (hfix : ∀ w < 3510, fixC X P fp nF w = true) (hsep : ∀ m < nF, sepC LT wd P sw nF m = true)
    (hPl : ∀ m < nF, ptE (P m) < 3510)
    (hPx : ∀ m < nF, idx 3510 x (ptE (P m)) = ptE (P m)) {i j : ℕ} (hi : i < 3510) (hj : j < 3510)
    (hxi : idx 3510 x i = i) (hxj : idx 3510 x j = j) (hij : i ≠ j)
    (hc : Commute (conjPt i) (conjPt j)) :
    ∃ e < 3510, idx 3510 x e = e ∧ Commute (conjPt e) (conjPt j) ∧ ¬Commute (conjPt e) (conjPt i) := by
  obtain ⟨hmi, ei⟩ := fix_pos hX hfix hi hxi
  obtain ⟨hmj, ej⟩ := fix_pos hX hfix hj hxj
  have hrow : ∀ m1 < nF, ∀ m2 < nF, m1 < m2 → Commute (conjPt (ptE (P m1))) (conjPt (ptE (P m2))) →
      ptE (P m1) ≠ ptE (P m2) →
      (∃ e1 < nF, Commute (conjPt (ptE (P e1))) (conjPt (ptE (P m2))) ∧
        ¬Commute (conjPt (ptE (P e1))) (conjPt (ptE (P m1)))) ∧
      (∃ e2 < nF, Commute (conjPt (ptE (P e2))) (conjPt (ptE (P m1))) ∧
        ¬Commute (conjPt (ptE (P e2))) (conjPt (ptE (P m2)))) := by
    intro m1 h1 m2 h2 h12 hcm hne
    have hs := hsep m1 h1
    unfold sepC at hs
    simp only [sB_eq] at hs
    have h := CFSG.KS.allN_spec hs m2 h2
    rcases bIf_cases h with ⟨-, h3⟩ | ⟨hb, -⟩
    swap
    · exact absurd ((blt_iff _ _).2 h12) (by rw [hb]; exact Bool.false_ne_true)
    rcases bIf_cases h3 with ⟨hb, -⟩ | ⟨-, h4⟩
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
    rcases bIf_cases h4 with ⟨-, h5⟩ | ⟨hb, -⟩
    swap
    · rw [(cmE_iff hL hw (hPl m1 h1) (hPl m2 h2)).2 hcm] at hb
      exact absurd hb (by decide)
    simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h5
    obtain ⟨he1, he2, c1, c2, c3, c4⟩ := h5
    have q1 := (cmE_iff hL hw (hPl _ he1) (hPl m2 h2)).1 c1
    have q3 := (cmE_iff hL hw (hPl _ he2) (hPl m1 h1)).1 c3
    refine ⟨⟨_, he1, q1, fun hq => ?_⟩, ⟨_, he2, q3, fun hq => ?_⟩⟩
    · rw [(cmE_iff hL hw (hPl _ he1) (hPl m1 h1)).2 hq] at c2
      exact absurd c2 Bool.false_ne_true
    · rw [(cmE_iff hL hw (hPl _ he2) (hPl m2 h2)).2 hq] at c4
      exact absurd c4 Bool.false_ne_true
  rcases lt_trichotomy (fp i) (fp j) with hlt | heq | hgt
  · obtain ⟨⟨e1, he1, q1, q2⟩, -⟩ := hrow _ hmi _ hmj hlt (by rw [ei, ej]; exact hc)
      (by rw [ei, ej]; exact hij)
    rw [ej] at q1
    rw [ei] at q2
    exact ⟨_, hPl _ he1, hPx _ he1, q1, q2⟩
  · exact absurd (by rw [← ei, ← ej, heq]) hij
  · obtain ⟨-, ⟨e2, he2, q1, q2⟩⟩ := hrow _ hmj _ hmi hgt (by rw [ei, ej]; exact hc.symm)
      (by rw [ei, ej]; exact hij.symm)
    rw [ej] at q1
    rw [ei] at q2
    exact ⟨_, hPl _ he2, hPx _ he2, q1, q2⟩

theorem ord4_of {Lw w4 : ℕ → ℕ} {lJ : ℕ → J} {len k0 : ℕ} (hLw : ∀ z < 32, RepE (Lw z) (lJ z))
    (hk0 : k0 = pk5 bp) (hX : RepE X x) (h : ordC Lw w4 len X k0 = true) :
    ∃ t : J, orderOf t = 4 ∧ t * x = x * t := by
  rw [← keyOf_one] at hk0
  subst hk0
  unfold ordC at h
  simp only [sB_eq, bRec_and, Bool.and_eq_true] at h
  obtain ⟨hl, h2, h4, hc⟩ := h
  have hw : ∀ t, 0 ≤ t → t < 0 + len → RepE (Lw (w4 t)) (lJ (w4 t)) := fun t _ ht =>
    hLw _ ((blt_iff _ _).1 (CFSG.KS.allN_spec hl t (by omega)))
  have k1 : ∀ g : J, wordK Lw w4 len 0 (keyOf g) = keyOf (wordJ lJ w4 0 len * g) :=
    wordK_keyOf len 0 hw
  simp only [k1, mul_one, mapK_keyOf hX] at h2 h4 hc
  set t := wordJ lJ w4 0 len
  have hxt := eq_of_keyOf ((beq_iff _ _).1 hc)
  have h4' := eq_of_keyOf ((beq_iff _ _).1 h4)
  have h2' : t * t ≠ 1 := fun e => by
    have := bNot h2
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨t, ?_, hxt.symm⟩
  have hp2 : ¬t ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact h2'
  have hp4 : t ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one, mul_assoc,
      mul_assoc]
    exact h4'
  rw [orderOf_eq_prime_pow hp2 hp4]
  norm_num

end CFSG.KD.Fi22Reps

end
