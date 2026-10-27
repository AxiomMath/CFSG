module

public import CFSG.Certificates.Kernel.J4.MLevelRun
import Mathlib.Tactic.Group

public section

namespace CFSG.KJ4.MLevel

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KC.Loop
open CFSG.Certificates.DceWord (lvE wv)
open CFSG.Certificates.J4Words (jv invJ jv_inv)
open CFSG.Certificates.J4KShape (rv)
open scoped Matrix

set_option exponentiation.threshold 400

section Traces

variable (d : MD) {LET : ℕ} {G : Type} [Group G] (φ : Nhat LET →* G) (x y t : G)

@[expose] def Traced (i : ℕ) : Prop := wv (fv x y t) (wW (d.TW i)) (wN (d.TW i)) = 1

@[expose] def TInv (u : ℕ) : Prop := cIdx u < 2147483648 → ∀ i < cIdx u, i < 89 → Traced d x y t i

@[expose] def TOInv (w : ℕ → G) (s : St4) : Prop :=
  s.2.2.1 = 0 ∨ ∃ R i, R / 65536 % 4294967296 = d.NF ∧ R / 281474976710656 % 4294967296 = i ∧
    s.1 / 65536 = R ∧
    (i < 2147483648 → (∀ i' < i, i' < 89 → Traced d x y t i') ∧
      (i < 89 → wW (d.TW i) < 256 ^ wN (d.TW i) ∧
        (s.2.2.1 = 0 ∨ TGood d φ x y t w R (wW (d.TW i)) (wN (d.TW i)) s)))

@[expose] def PInvT (w : ℕ → G) (q : ℕ × St4) : Prop :=
  (q.1 % 2 = 0 → TInv d x y t (q.1 / 2)) ∧ (q.1 % 2 = 1 → TOInv d φ x y t w q.2)

variable {d φ x y t}

theorem tinv_fail : TInv d x y t FAIL := by
  intro h
  rw [cIdx_FAIL] at h
  omega

theorem mStep_even_T {k : KD} {c p m : ℕ} {s : St4} {r : ℕ × St4} (hm : m % 2 = 0)
    (hr : mStep d k true c p (m, s) = r) : r = (1, stTr d.TW d.NF (m / 2)) ∨ r = mFail := by
  unfold mStep at hr
  have hr := bsel_of_true (by rw [land1, hm]; rfl) hr
  have hr := bsel_of_true rfl hr
  rcases bsel_eq hr with hr | hr
  · exact Or.inl (by rw [← hr, shr1])
  · exact Or.inr hr.symm

theorem mStep_odd_T {k : KD} {c p m : ℕ} {s : St4} {r : ℕ × St4} (hm : m % 2 = 1)
    (hr : mStep d k true c p (m, s) = r) :
    (∃ s', IsStep d k.TH s s' ∧ r = (1, s')) ∨ r = (2 * trEnd s, bad4) ∨ r = mFail := by
  unfold mStep at hr
  have hr := bsel_of_false (by rw [land1, hm]; rfl) hr
  rcases bsel_eq hr with hr | hr
  · exact Or.inl ⟨_, ⟨_, 0, 0, 0, 0, 0, Nat.zero_le 1, Or.inl rfl⟩, hr.symm⟩
  rcases bsel_eq hr with hr | hr
  · exact Or.inl ⟨_, ⟨0, _, _, 0, 0, 0, land_p1 p, Or.inr (Or.inl rfl)⟩, hr.symm⟩
  rcases bsel_eq hr with hr | hr
  · exact Or.inl ⟨_, ⟨0, _, _, 0, 0, 0, land_p1 p, Or.inr (Or.inr (Or.inl rfl))⟩, hr.symm⟩
  rcases bsel_eq hr with hr | hr
  · exact Or.inl ⟨_, ⟨0, _, _, _, _, 0, land_p1 p, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩, hr.symm⟩
  rcases bsel_eq hr with hr | hr
  · exact Or.inl ⟨_, ⟨0, _, _, _, _, _, land_p1 p, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩,
      hr.symm⟩
  rcases bsel_eq hr with hr | hr
  · exact Or.inr (Or.inl (by rw [← hr]; rfl))
  · have hr := bsel_of_false rfl hr
    exact Or.inr (Or.inr hr.symm)

variable {TH : ℕ} {w : ℕ → G}

theorem pinvT_counter {u : ℕ} (hu : TInv d x y t u) : PInvT d φ x y t w (2 * u, bad4) :=
  ⟨fun _ => by rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact hu, fun h => by
    change 2 * u % 2 = 1 at h
    omega⟩

theorem pinvT_fail : PInvT d φ x y t w mFail := pinvT_counter tinv_fail

theorem endMT_inv {q : ℕ × St4} (hq : PInvT d φ x y t w q) : TInv d x y t (endM q) := by
  obtain ⟨m, s⟩ := q
  generalize hr : endM (m, s) = r
  unfold endM at hr
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hr := bsel_of_true (by rw [land1, hm]; rfl) hr
    rw [← hr, shr1]
    exact hq.1 hm
  · have hr := bsel_of_false (by rw [land1, hm]; rfl) hr
    rw [← hr]
    exact tinv_fail

theorem toinv_start (hnd0 : 0 < d.ND) (hnf : d.NF < 1048576)
    (hw0 : w 0 = 1) (htw : ∀ i < 89, wW (d.TW i) < 256 ^ wN (d.TW i)) {u : ℕ}
    (hu : TInv d x y t u) : TOInv d φ x y t w (stTr d.TW d.NF u) := by
  generalize hr : stTr d.TW d.NF u = r
  unfold stTr at hr
  simp only [strictT_eq] at hr
  rw [← hr]
  have hNF : d.NF < 4294967296 := by omega
  refine Or.inr ⟨hdr 0 d.NF (cIdx u) ident12, cIdx u, hdr_K (by norm_num) hNF,
    hdr_nd (by norm_num) hNF (cIdx_lt u), ?_, fun hi => ⟨hu hi, fun hi89 => ⟨htw _ hi89, ?_⟩⟩⟩
  · change mkD 0 d.NF (cIdx u) ident12 / 65536 = _
    rw [mkD_eq (by norm_num) hNF (cIdx_lt u)]
    omega
  · refine Or.inr ⟨0, 0, ident12, ident12, ?_, hnd0, Nat.zero_le _, InN_one, InN_one, ?_⟩
    · rw [mkD_eq (by norm_num) hNF (cIdx_lt u), wInit_or1 (htw _ hi89)]
    · unfold Q
      rw [ev_one, hw0, wv_zero]
      group

theorem toinv_step (E : Env d φ x y t TH)
    (hw : ∀ g < d.NF, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) {s s' : St4}
    (hs : TOInv d φ x y t w s) (hst : IsStep d TH s s') : TOInv d φ x y t w s' := by
  obtain ⟨d0, p0, n0, c0⟩ := s
  have hP := isStep_pres hst
  rcases hs with h0 | ⟨R, i, h2, h3, h5, hsem⟩
  · exact Or.inl (hP.1 h0)
  rcases hP.2 with h | hR
  · exact Or.inl h
  refine Or.inr ⟨R, i, h2, h3, hR.trans h5, fun hi => ?_⟩
  obtain ⟨hprev, hcur⟩ := hsem hi
  refine ⟨hprev, fun hi89 => ?_⟩
  obtain ⟨hW, hg⟩ := hcur hi89
  refine ⟨hW, ?_⟩
  rcases hg with h0 | ⟨D, i', p, nn, he, hD, hi', hp, hn, hq⟩
  · exact Or.inl (hP.1 h0)
  rw [he] at hst
  exact tgood_of_next hp hn hq
    (isStep_next E hst h2 hw (fun h => absurd h one_ne_zero) hW hD hi' le_rfl)

theorem tinv_end (hw0 : w 0 = 1) {s : St4} (hs : TOInv d φ x y t w s) : TInv d x y t (trEnd s) := by
  obtain ⟨d0, p0, n0, c0⟩ := s
  generalize hr : trEnd (d0, p0, n0, c0) = r
  unfold trEnd at hr
  rcases brecN hr.symm with h | ⟨hc, h⟩
  · rw [h]
    exact tinv_fail
  rw [h]
  obtain ⟨hc1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨hc2, hc3⟩ := andB_eq_true.1 hc
  have e2 := beq_eq_true.1 hc2
  rcases hs with h0 | ⟨R, i, h2, h3, h5, hsem⟩
  · change n0 = 0 at h0
    rw [h0, mul12_zero] at e2
    exact absurd e2.symm ident12_ne_zero
  have hdN : dNd d0 = i := by rw [dNd_gen, h5, h3]
  rw [hdN]
  have hi32 : i < 4294967296 := by omega
  intro hc
  rw [cIdx_eq] at hc ⊢
  rcases Nat.lt_or_ge (i + 1) 4294967296 with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hc ⊢
    obtain ⟨hprev, hcur⟩ := hsem (by omega)
    intro i' hi' hi'89
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
    · exact hprev i' hi' hi'89
    obtain ⟨-, hg⟩ := hcur hi'89
    rcases hg with h0 | ⟨D, i'', p, nn, he, hD, hi'', hp, hn, hq⟩
    · change n0 = 0 at h0
      rw [h0, mul12_zero] at e2
      exact absurd e2.symm ident12_ne_zero
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    have hD' : D < 65536 := by omega
    rw [dD_eq R hD'] at hc1
    have eD := beq_eq_true.1 hc1
    obtain ⟨rfl, -⟩ := cur_end (le_refl 1) hi'' (beq_eq_true.1 hc3)
    subst eD
    have e := ev_mul φ hn hp
    rw [e2, ev_one] at e
    unfold Q at hq
    rw [hw0, mul_one, ← e, one_mul] at hq
    exact inv_eq_one.1 hq
  · have e : (i + 1) % 4294967296 = 0 := by omega
    rw [e]
    exact fun i' hi' => absurd hi' (Nat.not_lt_zero _)

theorem pinvT_step {k : KD} (E : Env d φ x y t k.TH) (hnd0 : 0 < d.ND) (hnf : d.NF < 1048576)
    (hw : ∀ g < d.NF, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) (hw0 : w 0 = 1)
    (htw : ∀ i < 89, wW (d.TW i) < 256 ^ wN (d.TW i)) (c p : ℕ) {q : ℕ × St4}
    (hq : PInvT d φ x y t w q) : PInvT d φ x y t w (mStep d k true c p q) := by
  obtain ⟨m, s⟩ := q
  generalize hr : mStep d k true c p (m, s) = r
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hu := hq.1 hm
    rcases mStep_even_T hm hr with rfl | rfl
    · exact ⟨fun h => absurd h (by norm_num), fun _ => toinv_start hnd0 hnf hw0 htw hu⟩
    · exact pinvT_fail
  · have hs := hq.2 hm
    rcases mStep_odd_T hm hr with ⟨s', hst, rfl⟩ | rfl | rfl
    · exact ⟨fun h => absurd h (by norm_num), fun _ => toinv_step E hw hs hst⟩
    · exact pinvT_counter (tinv_end hw0 hs)
    · exact pinvT_fail

theorem traces_run {k : KD} (E : Env d φ x y t k.TH) (hnd0 : 0 < d.ND) (hnf : d.NF < 1048576)
    (hw : ∀ g < d.NF, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) (hw0 : w 0 = 1)
    (htw : ∀ i < 89, wW (d.TW i) < 256 ^ wN (d.TW i)) {MT : List ℕ}
    (h : runT d k MT 0 = 89) : ∀ i < 89, Traced d x y t i := by
  have hI := runT_inv d k (TInv d x y t) (fun C u hu => chunk_inv d k true (PInvT d φ x y t w)
    (TInv d x y t) (fun c p _ hq => pinvT_step E hnd0 hnf hw hw0 htw c p hq)
    (fun _ hq => endMT_inv hq) (pinvT_counter hu)) MT 0 (fun _ i hi => by
      rw [cIdx_eq] at hi
      omega)
  rw [h] at hI
  have e : cIdx 89 = 89 := by rw [cIdx_eq]
  intro i hi
  exact hI (by rw [e]; norm_num) i (by rw [e]; exact hi) hi

end Traces

theorem allIn_spec {b : ℕ} {f : ℕ → Bool} (h : allIn 0 b f = true) {i : ℕ} (hi : i < b) :
    f i = true := by
  refine CFSG.Certificates.J4KShape.rngAll_spec _ h i (Nat.zero_le _) hi ?_
  change i < 0 + 64 * (Nat.shiftRight (b - 0) 6 + 1)
  rw [shr]
  have : (b - 0) / 2 ^ 6 = b / 64 := by norm_num
  omega

theorem chkOmF_eq' (TH O H h : ℕ) : chkOmF TH O H h = chkOm TH O H h := by
  cases O <;> cases H <;> rfl

theorem land_36 (X : ℕ) : Nat.land X 68719476735 = X % 2 ^ 36 := land_pow X 36

theorem shl1 (k : ℕ) : Nat.shiftLeft 1 k = 2 ^ k := by rw [shl, Nat.one_mul]

theorem oBase_eq (O : ℕ) : oBase O = O % 2 ^ 340 := by
  unfold oBase
  rw [shl1]
  exact land_pow O 340

theorem oP_eq (X : ℕ) : oP X = X / 2 ^ 16 % 2 ^ 36 := by
  unfold oP
  rw [land_36, shr]

theorem oP_oBase (O : ℕ) : oP (oBase O) = oP O := by
  have e : (2 : ℕ) ^ 340 = 2 ^ 16 * 2 ^ 324 := by rw [← pow_add]
  rw [oP_eq, oP_eq, oBase_eq, e, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num))]

theorem mSetup_parts {d : MD} {k : KD} (h : mSetup d k = true) :
    (∀ i < d.nH, hOK d.HT k.LET 4 0 0 i = true) ∧ (∀ j < d.NOM, omAtm d.HT d.OT k.TH j = true) ∧
    (∀ e < d.nSG, segAt d.SG k.LET e = true) ∧ (∀ w < d.nW, wordAt k.RT d.WT k.INV w = true) ∧
    d.ZW = zWord k.INV ∧ (∀ i < 89, linkAt k.RZT d.TW k.INV d.ZW i = true) ∧ 0 < d.ND ∧
    d.ND < 65535 ∧ d.NF < 1048576 := by
  obtain ⟨h1, h⟩ := andB_eq_true.1 h
  obtain ⟨h2, h⟩ := andB_eq_true.1 h
  obtain ⟨h3, h⟩ := andB_eq_true.1 h
  obtain ⟨h4, h⟩ := andB_eq_true.1 h
  obtain ⟨h5, h⟩ := andB_eq_true.1 h
  obtain ⟨h6, h⟩ := andB_eq_true.1 h
  obtain ⟨h7, h⟩ := andB_eq_true.1 h
  obtain ⟨h8, h9⟩ := andB_eq_true.1 h
  exact ⟨fun i hi => allIn_spec h1 hi, fun j hj => allIn_spec h2 hj, fun e he => allIn_spec h3 he,
    fun w hw => allIn_spec h4 hw, beq_eq_true.1 h5, fun i hi => allIn_spec h6 hi, blt_eq_true.1 h7,
    blt_eq_true.1 h8, blt_eq_true.1 h9⟩

theorem kSetup_more {k : KD} (h : kSetup k = true) :
    k.INV = invJ ∧ ptOK k.TH = true ∧ k.RZT 88 = psiWord k.INV k.PAW k.PBW := by
  obtain ⟨h1, h⟩ := andB_eq_true.1 h
  obtain ⟨h2, h⟩ := andB_eq_true.1 h
  iterate 12 obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨h15, -⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 h1, h2, beq_eq_true.1 h15⟩

theorem kRange_lets {k : KD} (h : kRange k = true) :
    ∀ r < 12, letsBelow (wW (k.RT r)) (wN (k.RT r)) 5 = true := by
  iterate 5 obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨h6, -⟩ := andB_eq_true.1 h
  exact fun r hr => allIn_spec h6 hr

section Env

variable {d : MD} {k : KD} {LET : ℕ} {G : Type} [Group G] {φ : Nhat LET →* G} {x y t : G}

theorem hdr_mem (hx : chkInv (letMat LET 0) (letMat LET 1) = true)
    (hy : chkInv (letMat LET 2) (letMat LET 3) = true)
    (hφx : ∀ g : Nhat LET, (g : GLm) = xh LET → φ g = x)
    (hφy : ∀ g : Nhat LET, (g : GLm) = yh LET → φ g = y)
    (hH : ∀ i < d.nH, hOK d.HT LET 4 0 0 i = true) :
    ∀ i < d.nH, InN LET (hMat (d.HT i)) ∧ InN LET (hInv (d.HT i)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hk := hH i hi
    unfold hOK at hk
    rw [letB_eq] at hk
    obtain ⟨hinv, hk⟩ := andB_eq_true.1 hk
    have hM : InN LET (hMat (d.HT i)) := by
      rcases brec_true hk with ⟨-, hk⟩ | ⟨-, hk⟩
      · rw [beq_eq_true.1 hk]
        exact InN_one
      rcases brec_true hk with ⟨-, hk⟩ | ⟨-, hk⟩
      · obtain ⟨h1, h2⟩ := andB_eq_true.1 hk
        obtain ⟨g, hg, -⟩ := letter_mem (1 : G) hx hy hφx hφy (blt_eq_true.1 h1)
        exact ⟨g, by rw [hg, beq_eq_true.1 h2]⟩
      rcases brec_true hk with ⟨-, hk⟩ | ⟨-, hk⟩
      · obtain ⟨h1, hk⟩ := andB_eq_true.1 hk
        obtain ⟨h2, h3⟩ := andB_eq_true.1 hk
        have e1 := blt_eq_true.1 h1
        have e2 := blt_eq_true.1 h2
        rw [beq_eq_true.1 h3, mulF_eq]
        exact InN_mul (ih _ e1 (by omega)).1 (ih _ e2 (by omega)).1
      rcases brec_true hk with ⟨-, hk⟩ | ⟨-, hk⟩
      · obtain ⟨h1, h2⟩ := andB_eq_true.1 hk
        have e1 := blt_eq_true.1 h1
        rw [mulF_eq] at h2
        exact InN_inv' (ih _ e1 (by omega)).1 (beq_eq_true.1 h2)
      · obtain ⟨-, hk⟩ := andB_eq_true.1 hk
        obtain ⟨h1, h2⟩ := andB_eq_true.1 hk
        have := blt_eq_true.1 h1
        rcases orB_eq_true.1 h2 with h2 | h2 <;> rw [beq_eq_true.1 h2] at this <;> omega
    rw [mulF_eq] at hinv
    exact ⟨hM, InN_inv hM (beq_eq_true.1 hinv)⟩

theorem om_mem {TH : ℕ} (hT : ptOK TH = true) (hdr : ∀ i < d.nH, InN LET (hMat (d.HT i)))
    (hHT0 : ∀ a, d.nH ≤ a → d.HT a = 0) (hO : ∀ j < d.NOM, omAtm d.HT d.OT TH j = true) :
    ∀ j < d.NOM, oJ (d.OT j) ≠ 0 → InN LET (gj d j) ∧ ptOK (oP (d.OT j)) = true ∧
      (fun v => v ᵥ* toMat (gj d j)) '' ptVecs TH = ptVecs (oP (d.OT j)) := by
  intro j hj hJ
  have h := hO j hj
  change orB _ _ = true at h
  rcases orB_eq_true.1 h with h | h
  · rw [beq_eq_true.1 h] at hJ
    exact absurd (by decide) hJ
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  rw [chkOmF_eq'] at h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hP, h⟩ := andB_eq_true.1 h
  obtain ⟨hpt, h⟩ := andB_eq_true.1 h
  obtain ⟨hinv, hG⟩ := andB_eq_true.1 h
  have eG := beq_eq_true.1 hG
  have hmap := chkPt_image hT hP hpt
  rw [oP_oBase] at hP hmap
  refine ⟨?_, hP, hmap⟩
  unfold gj
  rcases Nat.lt_or_ge (oH (d.OT j)) d.nH with ho | ho
  · rw [eG]
    exact hdr _ ho
  · have e := beq_eq_true.1 hinv
    rw [eG, hHT0 _ ho, hMat_zero, mul12_zero] at e
    exact absurd e.symm ident12_ne_zero

theorem seg_mem (hx : chkInv (letMat LET 0) (letMat LET 1) = true)
    (hy : chkInv (letMat LET 2) (letMat LET 3) = true)
    (hφx : ∀ g : Nhat LET, (g : GLm) = xh LET → φ g = x)
    (hφy : ∀ g : Nhat LET, (g : GLm) = yh LET → φ g = y)
    (hSG : ∀ e < d.nSG, segAt d.SG LET e = true) (hSG0 : ∀ e, d.nSG ≤ e → d.SG e = 0) (e : ℕ) :
    sgN (d.SG e) = 0 ∨ ((∀ q < sgN (d.SG e), wLet (sgW (d.SG e)) q < 4) ∧
      InN LET (sgM (d.SG e)) ∧ ev φ (sgM (d.SG e)) = wv (fv x y t) (sgW (d.SG e)) (sgN (d.SG e))) := by
  rcases Nat.lt_or_ge e d.nSG with he | he
  · have h := hSG e he
    change andB _ _ = true at h
    obtain ⟨-, h⟩ := andB_eq_true.1 h
    obtain ⟨-, h⟩ := andB_eq_true.1 h
    obtain ⟨hl, hev⟩ := andB_eq_true.1 h
    have hl' := CFSG.Certificates.J4KShape.letsBelow_spec _ hl
    exact Or.inr ⟨hl', eval_mem t hx hy hφx hφy hl' hev⟩
  · left
    rw [hSG0 e he]
    decide

theorem words_mem (ht : t * t = 1) (hI : k.INV = invJ)
    (hrel : ∀ r, wW (k.RT r) < 256 ^ wN (k.RT r) ∧ wv (jv x y t 1) (wW (k.RT r)) (wN (k.RT r)) = 1)
    (hW : ∀ w < d.nW, wordAt k.RT d.WT k.INV w = true) (hWT0 : ∀ w, d.nW ≤ w → d.WT w = 0) (w : ℕ) :
    wW (d.WT w) < 256 ^ wN (d.WT w) ∧ wv (fv x y t) (wW (d.WT w)) (wN (d.WT w)) = 1 := by
  rcases Nat.lt_or_ge w d.nW with hw | hw
  · have h := hW w hw
    unfold wordAt wordOK at h
    rw [letB_eq] at h
    obtain ⟨hf, hc⟩ := andB_eq_true.1 h
    refine ⟨CFSG.Certificates.J4KShape.wFits_spec hf, ?_⟩
    rw [hI] at hc
    exact CFSG.Certificates.J4Words.chkWord_val (jv x y t 1) (hrel _).1 (hrel _).2
      (fun q _ _ => (jv_inv x y t 1 ht _).2) hc
  · rw [hWT0 w hw]
    have e : wN 0 = 0 := by decide
    refine ⟨by decide, ?_⟩
    rw [e, wv_zero]

theorem wv_lvE_of {f : ℕ → G} {W n : ℕ} (h : ∀ q < n, wLet W q < 5) : wv (lvE f) W n = wv f W n := by
  unfold wv
  congr 1
  refine List.map_congr_left fun q hq => ?_
  have := h q (List.mem_range.1 hq)
  have hne : CFSG.Certificates.DceLoop.byteG W q ≠ 255 := by
    change wLet W q ≠ 255
    omega
  simp [lvE, hne]

theorem relAll_of (hS : kSetup k = true) (hRg : kRange k = true)
    (hRT0 : ∀ r, 12 ≤ r → k.RT r = 0) (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) (r : ℕ) :
    wW (k.RT r) < 256 ^ wN (k.RT r) ∧ wv (jv x y t 1) (wW (k.RT r)) (wN (k.RT r)) = 1 := by
  rcases Nat.lt_or_ge r 12 with hr | hr
  · obtain ⟨-, -, -, -, -, hrel, -⟩ := kSetup_parts hS
    have h := hrel r hr
    change andB _ _ = true at h
    obtain ⟨hf, -⟩ := andB_eq_true.1 h
    refine ⟨CFSG.Certificates.J4KShape.wFits_spec hf, ?_⟩
    rw [← wv_lvE_of (CFSG.Certificates.J4KShape.letsBelow_spec _ (kRange_lets hRg r hr))]
    exact hR r hr
  · rw [hRT0 r hr]
    have e : wN 0 = 0 := by decide
    refine ⟨by decide, ?_⟩
    rw [e, wv_zero]

theorem env_of (hS : kSetup k = true) (hM : mSetup d k = true)
    (hHT0 : ∀ a, d.nH ≤ a → d.HT a = 0) (hSG0 : ∀ e, d.nSG ≤ e → d.SG e = 0)
    {φ : Nhat k.LET →* G}
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hStab : ∀ g : Nhat k.LET, (fun v => v ᵥ* ((g : GLm) : Mat12)) '' ptVecs k.TH = ptVecs k.TH →
      φ g * t = t * φ g) : Env d φ x y t k.TH := by
  obtain ⟨-, hx, hy, -, -, -, -⟩ := kSetup_parts hS
  obtain ⟨-, hT, -⟩ := kSetup_more hS
  obtain ⟨hH, hO, hSG, -, -, -, -, hND, -⟩ := mSetup_parts hM
  have hdr := hdr_mem hx hy hφx hφy hH
  exact { nd := hND, th := hT, ht := ht
          stab := fun m ⟨g, hg⟩ hmap => by
            rw [← hg] at hmap
            rw [ev_eq φ g hg]
            exact hStab g hmap
          hdr := fun i hi => (hdr i hi).1
          hdr0 := hHT0
          om := om_mem hT (fun i hi => (hdr i hi).1) hHT0 hO
          seg := seg_mem hx hy hφx hφy hSG hSG0 }

theorem env2_of (hS : kSetup k = true) (hM : mSetup d k = true) {φ : Nhat k.LET →* G}
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hrel : ∀ r, wW (k.RT r) < 256 ^ wN (k.RT r) ∧ wv (jv x y t 1) (wW (k.RT r)) (wN (k.RT r)) = 1)
    (hWT0 : ∀ w, d.nW ≤ w → d.WT w = 0) : Env2 d k.LET x y t := by
  obtain ⟨-, hx, hy, -, -, -, -⟩ := kSetup_parts hS
  obtain ⟨hI, -, -⟩ := kSetup_more hS
  obtain ⟨hH, -, -, hW, -, -, hnd0, -, hnf⟩ := mSetup_parts hM
  have hdr := hdr_mem hx hy hφx hφy hH
  exact { hdrI := fun i hi => (hdr i hi).2, words := words_mem ht hI hrel hW hWT0, nd0 := hnd0,
          nf := hnf }

end Env

theorem zw_fit : wW (zWord invJ) < 256 ^ wN (zWord invJ) := by decide +kernel

theorem zw_lets : ∀ q < wN (zWord invJ), wLet (wW (zWord invJ)) q < 5 := by decide +kernel

@[expose] noncomputable def zv {G : Type} [Group G] (x y t : G) : G :=
  wv (fv x y t) (wW (zWord invJ)) (wN (zWord invJ))

section Main

variable {G : Type} [Group G]

theorem zsub_eq (x y t Z : G) : CFSG.Certificates.J4Words.zsub (jv x y t 1) Z Z⁻¹ = jv x y t Z := by
  funext c
  by_cases h5 : c = 5
  · subst h5
    simp [CFSG.Certificates.J4Words.zsub, jv]
  by_cases h6 : c = 6
  · subst h6
    simp [CFSG.Certificates.J4Words.zsub, jv]
  simp [CFSG.Certificates.J4Words.zsub, jv, h5, h6]

theorem mlevel_sound {k : KD} {d : MD} {MW MT : List ℕ} (hS : kSetup k = true)
    (hRg : kRange k = true) (hM : mSetup d k = true)
    (hMW : runM d k MW (mkC 0 1) = mkC d.NF d.ND) (hMT : runT d k MT 0 = 89)
    (hHT0 : ∀ a, d.nH ≤ a → d.HT a = 0) (hSG0 : ∀ e, d.nSG ≤ e → d.SG e = 0)
    (hWT0 : ∀ w, d.nW ≤ w → d.WT w = 0) (hRT0 : ∀ r, 12 ≤ r → k.RT r = 0)
    (φ : Nhat k.LET →* G) (x y t : G)
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1)
    (hStab : ∀ g : Nhat k.LET, (fun v => v ᵥ* ((g : GLm) : Mat12)) '' ptVecs k.TH = ptVecs k.TH →
      φ g * t = t * φ g) :
    ∀ r < 89, rv (jv x y t (zv x y t)) (k.RZT r) = 1 := by
  have hrel := relAll_of hS hRg hRT0 hR
  have E := env_of (d := d) hS hM hHT0 hSG0 hφx hφy ht hStab
  have E2 := env2_of (d := d) hS hM hφx hφy ht hrel hWT0
  obtain ⟨hI, -, -⟩ := kSetup_more hS
  obtain ⟨-, -, -, -, hZW, hL, -⟩ := mSetup_parts hM
  have htw : ∀ i < 89, wW (d.TW i) < 256 ^ wN (d.TW i) := fun i hi => by
    have h := hL i hi
    unfold linkAt at h
    rw [letB_eq, letB_eq] at h
    exact CFSG.Certificates.J4KShape.wFits_spec (andB_eq_true.1 h).1
  obtain ⟨w, hw0, hw⟩ := facts_hold (facts_run E E2 hMW)
  have hT := traces_run E E2.nd0 E2.nf hw hw0 htw hMT
  intro r hr
  have h := hL r hr
  unfold linkAt at h
  rw [letB_eq, letB_eq] at h
  obtain ⟨-, -, hc⟩ := (andB_eq_true.1 h).imp_right andB_eq_true.1
  rw [hZW, hI] at hc
  have key := CFSG.Certificates.J4Words.chkSubstRed_val (jv x y t 1)
    (fun c _ => (jv_inv x y t 1 ht c).2) zw_fit (CFSG.Certificates.J4Words.wInv_lt _ _ _) hc
  have hZi : wv (lvE (jv x y t 1)) (wInv invJ (wW (zWord invJ)) (wN (zWord invJ))) (wN (zWord invJ)) =
      (wv (lvE (jv x y t 1)) (wW (zWord invJ)) (wN (zWord invJ)))⁻¹ :=
    CFSG.Certificates.J4Words.wv_wInv _ invJ _ _ fun q hq => by
      have h5 := zw_lets q hq
      obtain ⟨hl, hv⟩ := jv_inv x y t 1 ht (wLet (wW (zWord invJ)) q)
      have hne1 : lInv invJ (wLet (wW (zWord invJ)) q) ≠ 255 := by omega
      have hne2 : wLet (wW (zWord invJ)) q ≠ 255 := by omega
      simp only [lvE, hne1, hne2, ↓reduceIte]
      exact hv
  have hgoal : rv (jv x y t (zv x y t)) (k.RZT r) =
      wv (lvE (CFSG.Certificates.J4Words.zsub (jv x y t 1)
        (wv (lvE (jv x y t 1)) (wW (zWord invJ)) (wN (zWord invJ)))
        (wv (lvE (jv x y t 1)) (wInv invJ (wW (zWord invJ)) (wN (zWord invJ))) (wN (zWord invJ)))))
        (wW (k.RZT r)) (wN (k.RZT r)) := by
    rw [hZi, zsub_eq]
    rfl
  exact hgoal.trans (key.trans (hT r hr))

theorem mlevel_psi {k : KD} {d : MD} {MW MT : List ℕ} (hS : kSetup k = true)
    (hRg : kRange k = true) (hM : mSetup d k = true)
    (hMW : runM d k MW (mkC 0 1) = mkC d.NF d.ND) (hMT : runT d k MT 0 = 89)
    (hHT0 : ∀ a, d.nH ≤ a → d.HT a = 0) (hSG0 : ∀ e, d.nSG ≤ e → d.SG e = 0)
    (hWT0 : ∀ w, d.nW ≤ w → d.WT w = 0) (hRT0 : ∀ r, 12 ≤ r → k.RT r = 0)
    (φ : Nhat k.LET →* G) (x y t : G)
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1)
    (hStab : ∀ g : Nhat k.LET, (fun v => v ᵥ* ((g : GLm) : Mat12)) '' ptVecs k.TH = ptVecs k.TH →
      φ g * t = t * φ g) :
    rv (jv x y t (zv x y t)) (psiWord invJ k.PAW k.PBW) = 1 := by
  have h := mlevel_sound hS hRg hM hMW hMT hHT0 hSG0 hWT0 hRT0 φ x y t hφx hφy ht hR hStab 88
    (by norm_num)
  obtain ⟨hI, -, h88⟩ := kSetup_more hS
  rwa [h88, hI] at h

theorem psi_decode (x y t z : G) (ht : t * t = 1) {PA PB : ℕ} (hA : wW PA < 256 ^ wN PA) (hBe : ∀ q < wN PB, wLet (wW PB) q ≠ 255)
    (hn : wN PA + wN PB + 2 < 65536) (h : rv (jv x y t z) (psiWord invJ PA PB) = 1) :
    t * rv (jv x y t z) PA * t = rv (jv x y t z) PB := by
  set f := jv x y t z
  set Wd := CFSG.KJ4.wCat (CFSG.KJ4.wCat (CFSG.KJ4.wCat 4 1 (wW PA)) (wN PA + 1) 4) (wN PA + 2)
    (CFSG.KJ4.wInv invJ (wW PB) (wN PB)) with hWd
  have hP : psiWord invJ PA PB = (wN PA + wN PB + 2) + 4294967296 * Wd := by
    change Nat.lor (wN PA + wN PB + 2) (Nat.shiftLeft Wd 32) = _
    rw [lor_add (k := 32) (by norm_num; omega) (by rw [shl]; simp), shl]
    ring
  have hN : wN (psiWord invJ PA PB) = wN PA + wN PB + 2 := by
    change Nat.land _ 65535 = _
    rw [land65535, hP]
    omega
  have hWw : wW (psiWord invJ PA PB) = Wd := by
    change Nat.shiftRight _ 32 = _
    rw [shr, hP]
    omega
  have hT1 : (4 : ℕ) < 256 ^ 1 := by norm_num
  have a1 := CFSG.Certificates.J4Words.wCat_lt' hT1 hA (by omega : 1 + wN PA = wN PA + 1)
  have a2 := CFSG.Certificates.J4Words.wCat_lt' a1 hT1 (by omega : wN PA + 1 + 1 = wN PA + 2)
  have hinv : ∀ q < wN PB, lvE f (lInv invJ (wLet (wW PB) q)) = (lvE f (wLet (wW PB) q))⁻¹ := by
    intro q hq
    obtain ⟨hl, hv⟩ := jv_inv x y t z ht (wLet (wW PB) q)
    have hne1 : lInv invJ (wLet (wW PB) q) ≠ 255 := by omega
    simp only [lvE, hne1, hBe q hq, ↓reduceIte]
    exact hv
  change wv (lvE f) (wW (psiWord invJ PA PB)) (wN (psiWord invJ PA PB)) = 1 at h
  rw [hN, hWw, hWd, CFSG.Certificates.J4Words.wv_wCat' (lvE f) a2
      (CFSG.Certificates.J4Words.wInv_lt invJ _ _) (by omega : wN PA + 2 + wN PB = wN PA + wN PB + 2),
    CFSG.Certificates.J4Words.wv_wCat' (lvE f) a1 hT1 (by omega : wN PA + 1 + 1 = wN PA + 2),
    CFSG.Certificates.J4Words.wv_wCat' (lvE f) hT1 hA (by omega : 1 + wN PA = wN PA + 1),
    CFSG.Certificates.J4Words.wv_one _ (by norm_num : (4 : ℕ) < 256),
    CFSG.Certificates.J4Words.wv_wInv (lvE f) invJ _ _ hinv] at h
  have h4 : lvE f 4 = t := by simp [f, lvE, jv]
  rw [h4] at h
  exact mul_inv_eq_one.1 h

theorem zv_mem (x y t : G) : zv x y t ∈ Subgroup.closure ({x, y, t} : Set G) := by
  have hx : x ∈ Subgroup.closure ({x, y, t} : Set G) := Subgroup.subset_closure (by simp)
  have hy : y ∈ Subgroup.closure ({x, y, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({x, y, t} : Set G) := Subgroup.subset_closure (by simp)
  have hl : ∀ c, fv x y t c ∈ Subgroup.closure ({x, y, t} : Set G) := by
    intro c
    unfold fv lvE jv
    split_ifs <;> first
      | exact Subgroup.one_mem _
      | exact hx
      | exact Subgroup.inv_mem _ hx
      | exact hy
      | exact Subgroup.inv_mem _ hy
      | exact ht
      | exact Subgroup.inv_mem _ (Subgroup.one_mem _)
  unfold zv wv
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hg
  exact hl _

end Main

@[expose] def gen2 {H : Type*} (a b : H) (n : ℕ) : H := if n = 0 then a else b

@[expose] def RN (RT : ℕ → ℕ) : Set (FreeGroup ℕ) :=
  {g | ∃ r < 12, tfree (wW (RT r)) (wN (RT r)) ∧
    g = rv (jv (FreeGroup.of 0) (FreeGroup.of 1) 1 1) (RT r)}

theorem lift_RN {RT : ℕ → ℕ} {H : Type*} [Group H] (g : ℕ → H) :
    (∀ r ∈ RN RT, FreeGroup.lift g r = 1) ↔ relN RT (g 0) (g 1) := by
  constructor
  · intro h r hr ht
    have := h _ ⟨r, hr, ht, rfl⟩
    rwa [lift_rv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, map_one] at this
  · rintro h r ⟨r', hr, ht, rfl⟩
    rw [lift_rv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, map_one]
    exact h r' hr ht

theorem image_01 {H : Type*} (g : ℕ → H) : g '' {0, 1} = {g 0, g 1} := by
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem exists_phiN {k : KD} (hS : kSetup k = true) (hC : kChains k = true)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN)
    {G : Type} [Group G] (x y : G) (hxy : relN k.RT x y) :
    ∃ φ : Nhat k.LET →* G, (∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x) ∧
      (∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) ∧ φ.range = Subgroup.closure {x, y} := by
  classical
  have hLS : gen2 (xh k.LET) (yh k.LET) '' {0, 1} = {xh k.LET, yh k.LET} := by
    rw [image_01]
    simp [gen2]
  obtain ⟨φ, hφ, -, -⟩ := CFSG.Certificates.DceTw.lift_hom (RN k.RT) {0, 1} k.BN
    (fun H _ g hg => by
      rw [image_01]
      exact hN H _ _ ((lift_RN g).1 hg))
    (gen2 (xh k.LET) (yh k.LET))
    ((lift_RN _).2 (by simpa [gen2] using model_relN hS))
    (by rw [hLS]; exact bn_le_card_nhat hS hC)
    (gen2 x y) ((lift_RN _).2 (by simpa [gen2] using hxy))
  have e : Nhat k.LET = Subgroup.closure (gen2 (xh k.LET) (yh k.LET) '' {0, 1}) := by
    rw [hLS]
  set φN : Nhat k.LET →* G := φ.comp (MulEquiv.subgroupCongr e).toMonoidHom with hφN
  have key : ∀ c ∈ ({0, 1} : Set ℕ), ∀ g : Nhat k.LET,
      (g : GLm) = gen2 (xh k.LET) (yh k.LET) c → φN g = gen2 x y c := by
    intro c hc g hg
    rw [← hφ c hc, hφN, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    exact Subtype.ext hg
  have kx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φN g = x := fun g hg =>
    key 0 (by simp) g (by simpa [gen2] using hg)
  have ky : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φN g = y := fun g hg =>
    key 1 (by simp) g (by simpa [gen2] using hg)
  refine ⟨φN, kx, ky, range_of_gen φN ?_⟩
  ext u
  constructor
  · rintro ⟨g, hg, rfl⟩
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [kx g hg]; simp
    · rw [ky g hg]; simp
  · rintro (rfl | rfl)
    · exact ⟨⟨xh k.LET, Subgroup.subset_closure (by simp)⟩, by simp, kx _ rfl⟩
    · exact ⟨⟨yh k.LET, Subgroup.subset_closure (by simp)⟩, by simp, ky _ rfl⟩

end CFSG.KJ4.MLevel

end
