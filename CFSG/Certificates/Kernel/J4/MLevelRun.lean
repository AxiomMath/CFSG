module

public import CFSG.Certificates.Kernel.J4.MLevelStep
import Mathlib.Tactic.Group

public section

namespace CFSG.KJ4.MLevel

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KC.Loop
open CFSG.Certificates.DceWord (lvE wv)

theorem bsel_eq {α : Type} {b : Bool} {t e r : α} (h : bsel b t e = r) : t = r ∨ e = r := by
  cases b
  · exact Or.inr h
  · exact Or.inl h

theorem bsel_of_true {α : Type} {b : Bool} {t e r : α} (hb : b = true) (h : bsel b t e = r) :
    t = r := by
  subst hb
  exact h

theorem bsel_of_false {α : Type} {b : Bool} {t e r : α} (hb : b = false) (h : bsel b t e = r) :
    e = r := by
  subst hb
  exact h

theorem forceM_eq {α : Type} (q : ℕ × St4) (f : ℕ × St4 → α) : forceM q f = f q := by
  obtain ⟨m, d, p, n, c⟩ := q
  simp only [forceM, strictT_eq]

theorem land_p1 (p : ℕ) : Nat.land p 1 ≤ 1 := by
  rw [land1]
  omega

theorem shr1 (m : ℕ) : Nat.shiftRight m 1 = m / 2 := by
  rw [shr, pow_one]

@[expose] def IsStep (d : MD) (TH : ℕ) (s s' : St4) : Prop :=
  ∃ e S g h PP RR, S ≤ 1 ∧ (s' = mNs d.SG e s ∨ s' = mEfs d.FT S g s ∨ s' = mEbs d.FT S g s ∨
    s' = mTfs d.FT d.OT TH S g h PP s ∨ s' = mTbs d.FT d.OT TH S g h PP RR s)

theorem isStep_pres {d : MD} {TH d0 p0 n0 c0 : ℕ} {s' : St4} (h : IsStep d TH (d0, p0, n0, c0) s') :
    Pres d0 n0 s' := by
  obtain ⟨e, S, g, h, PP, RR, -, rfl | rfl | rfl | rfl | rfl⟩ := h
  · exact pres_Ns _ _ _ _ _ _
  · exact pres_Ef _ _ _ _ _ _ _
  · exact pres_Eb _ _ _ _ _ _ _
  · exact pres_Tf _ _ _ _ _ _ _ _ _ _ _
  · exact pres_Tb _ _ _ _ _ _ _ _ _ _ _ _

section Walk

variable {d : MD} {LET TH : ℕ} {G : Type} [Group G] {φ : Nhat LET →* G} {x y t : G}

theorem isStep_next (E : Env d φ x y t TH) {w : ℕ → G} {R W n K D p nn i f : ℕ} {s' : St4}
    (hst : IsStep d TH (D + 65536 * R, p, nn, cur W n i f) s')
    (hRK : R / 65536 % 4294967296 = K)
    (hFB : ∀ g < K, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) (hK : f = 0 → RecV d (d.FT K))
    (hW : W < 256 ^ n) (hD : D < d.ND) (hi : i ≤ n) (hf : f ≤ 1) :
    Next d φ x y t w R W n K D p nn i f s' := by
  have hD' : D < 65536 := by have := E.nd; omega
  obtain ⟨e, S, g, h, PP, RR, hS, rfl | rfl | rfl | rfl | rfl⟩ := hst
  · exact next_Ns E hW hD hi hf
  · exact next_Ef hRK hFB hK hW hD' hi hf hS
  · exact next_Eb hRK hFB hK hW hD' hi hf hS
  · exact next_Tf E hRK hFB hK hW hD' hi hf hS
  · exact next_Tb E hRK hFB hK hW hD' hi hf hS

variable (d φ x y t)

@[expose] def WGood (w : ℕ → G) (R W n K D0 P0 : ℕ) (s : St4) : Prop :=
  ∃ D i f p nn, s = (D + 65536 * R, p, nn, cur W n i f) ∧ D < d.ND ∧ i ≤ n ∧ f ≤ 1 ∧
    (f = 0 → InN LET p ∧ InN LET nn ∧ Q φ x y t w W D p nn i = w D0 * ev φ P0) ∧
    (f = 1 → (InN LET p ↔ InN LET (fPi (d.FT K))) ∧ (InN LET nn ↔ InN LET (fNs (d.FT K))) ∧
      (InN LET (fPi (d.FT K)) → InN LET (fNs (d.FT K)) →
        (Q φ x y t w W D p nn i = w D0 * ev φ P0 ↔ MEq d φ t w (d.FT K))))

@[expose] def TGood (w : ℕ → G) (R W n : ℕ) (s : St4) : Prop :=
  ∃ D i p nn, s = (D + 65536 * R, p, nn, cur W n i 1) ∧ D < d.ND ∧ i ≤ n ∧ InN LET p ∧
    InN LET nn ∧ Q φ x y t w W D p nn i = 1

variable {d φ x y t}

theorem good_of_next {w : ℕ → G} {R W n K D0 P0 D p nn i f : ℕ} {s' : St4} (hf : f ≤ 1)
    (h0 : f = 0 → InN LET p ∧ InN LET nn ∧ Q φ x y t w W D p nn i = w D0 * ev φ P0)
    (h1 : f = 1 → (InN LET p ↔ InN LET (fPi (d.FT K))) ∧ (InN LET nn ↔ InN LET (fNs (d.FT K))) ∧
      (InN LET (fPi (d.FT K)) → InN LET (fNs (d.FT K)) →
        (Q φ x y t w W D p nn i = w D0 * ev φ P0 ↔ MEq d φ t w (d.FT K))))
    (hN : Next d φ x y t w R W n K D p nn i f s') :
    s'.2.2.1 = 0 ∨ WGood d φ x y t w R W n K D0 P0 s' := by
  rcases hN with h | ⟨D', p', nn', i', rfl, hD', hi', hp', hn', hQ⟩ |
    ⟨rfl, D', p', nn', i', rfl, hD', hi', hself⟩
  · exact Or.inl h
  · refine Or.inr ⟨D', i', f, p', nn', rfl, hD', hi', hf, fun hf0 => ?_, fun hf1 => ?_⟩
    · obtain ⟨hp, hn, hq⟩ := h0 hf0
      exact ⟨hp'.2 hp, hn'.2 hn, (hQ hp hn).trans hq⟩
    · obtain ⟨hpi, hni, hm⟩ := h1 hf1
      refine ⟨hp'.trans hpi, hn'.trans hni, fun hπ hnK => ?_⟩
      rw [hQ (hpi.2 hπ) (hni.2 hnK)]
      exact hm hπ hnK
  · obtain ⟨hp, hn, hq⟩ := h0 rfl
    obtain ⟨hpi, hni, hm⟩ := hself hp hn
    refine Or.inr ⟨D', i', 1, p', nn', rfl, hD', hi', le_rfl, fun h => absurd h one_ne_zero,
      fun _ => ⟨hpi, hni, fun hπ hnK => ?_⟩⟩
    rw [← hq]
    exact hm hπ hnK

theorem tgood_of_next {w : ℕ → G} {R W n K D p nn i : ℕ} {s' : St4} (hp : InN LET p)
    (hn : InN LET nn) (hq : Q φ x y t w W D p nn i = 1)
    (hN : Next d φ x y t w R W n K D p nn i 1 s') : s'.2.2.1 = 0 ∨ TGood d φ x y t w R W n s' := by
  rcases hN with h | ⟨D', p', nn', i', rfl, hD', hi', hp', hn', hQ⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨D', i', p', nn', rfl, hD', hi', hp'.2 hp, hn'.2 hn, (hQ hp hn).trans hq⟩
  · exact absurd h one_ne_zero

end Walk

structure Env2 (d : MD) (LET : ℕ) {G : Type} [Group G] (x y t : G) : Prop where
  hdrI : ∀ h < d.nH, InN LET (hInv (d.HT h))
  words : ∀ w, wW (d.WT w) < 256 ^ wN (d.WT w) ∧ wv (fv x y t) (wW (d.WT w)) (wN (d.WT w)) = 1
  nd0 : 0 < d.ND
  nf : d.NF < 1048576

section Facts

variable (d : MD) {LET : ℕ} {G : Type} [Group G] (φ : Nhat LET →* G) (x y t : G)

@[expose] def FactRaw (g nd nd' : ℕ) : Prop :=
  RecV d (d.FT g) ∧
  ((nd' = nd + 1 ∧ 0 < fJ (d.FT g) ∧ fDp (d.FT g) = nd ∧ fD (d.FT g) < nd ∧
      fPi (d.FT g) = ident12 ∧ fNs (d.FT g) = ident12) ∨
    (nd' = nd ∧ fD (d.FT g) = 0 ∧ fJ (d.FT g) = 0 ∧ fDp (d.FT g) = 0 ∧ InN LET (fPi (d.FT g)) ∧
      fNs (d.FT g) = fPiI (d.FT g)) ∨
    (nd' = nd ∧ ∀ w : ℕ → G, (∀ g' < g, RecV d (d.FT g') ∧ MF d φ t w (d.FT g')) →
      MF d φ t w (d.FT g)))

@[expose] def Valid (K nd : ℕ) : Prop :=
  ∃ nxf : ℕ → ℕ, nxf K = nd ∧ ∀ g < K, FactRaw d φ t g (nxf g) (nxf (g + 1))

@[expose] def CInv (u : ℕ) : Prop := cIdx u < 2147483648 → Valid d φ t (cIdx u) (cNd u)

@[expose] def OInv (s : St4) : Prop :=
  s.2.2.1 = 0 ∨ ∃ R W n K nd D0 P0, R % 65536 = D0 ∧ R / 65536 % 4294967296 = K ∧
    R / 281474976710656 % 4294967296 = nd ∧ R / 1208925819614629174706176 = P0 ∧
    s.1 / 65536 = R ∧
    (K < 2147483648 → Valid d φ t K nd ∧ RecV d (d.FT K) ∧ InN LET P0 ∧ W < 256 ^ n ∧
      wv (fv x y t) W n = 1 ∧
      ∀ w : ℕ → G, (∀ g < K, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) →
        s.2.2.1 = 0 ∨ WGood d φ x y t w R W n K D0 P0 s)

@[expose] def PInv (q : ℕ × St4) : Prop :=
  (q.1 % 2 = 0 → CInv d φ t (q.1 / 2)) ∧ (q.1 % 2 = 1 → OInv d φ x y t q.2)

variable {d φ x y t} {TH : ℕ}

theorem cinv_fail : CInv d φ t FAIL := by
  intro h
  rw [cIdx_FAIL] at h
  omega

theorem valid_zero (nd : ℕ) : Valid d φ t 0 nd :=
  ⟨fun _ => nd, rfl, fun g hg => absurd hg (Nat.not_lt_zero g)⟩

theorem valid_succ {k nd nd' : ℕ} (hV : Valid d φ t k nd) (hF : FactRaw d φ t k nd nd') :
    Valid d φ t (k + 1) nd' := by
  classical
  obtain ⟨nxf, hk, hf⟩ := hV
  refine ⟨fun g => if g ≤ k then nxf g else nd', by simp, fun g hg => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | rfl
  · have h1 : g ≤ k := by omega
    have h2 : g + 1 ≤ k := by omega
    simp only [h1, h2, ↓reduceIte]
    exact hf g hg
  · simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self]
    rw [hk]
    exact hF

theorem cinv_succ {k nd nd' : ℕ} (hk : k < 4294967296) (hnd' : nd' < 4294967296)
    (h : k < 2147483648 → Valid d φ t k nd ∧ FactRaw d φ t k nd nd') :
    CInv d φ t (mkC (k + 1) nd') := by
  intro hc
  rcases cIdx_mkC_succ (nd := nd') hk with ⟨hlt, e⟩ | e
  · rw [e, cNd_mkC hlt hnd']
    rw [e] at hc
    obtain ⟨hV, hF⟩ := h (by omega)
    exact valid_succ hV hF
  · rw [e]
    exact valid_zero _

theorem recOKm_spec {F k ND NOM : ℕ} (h : recOKm F k ND NOM = true) :
    fD F < ND ∧ fDp F < ND ∧ fJ F ≤ NOM ∧ mul12 (fPi F) (fPiI F) = ident12 ∧
      mul12 (fNs F) (fNIs F) = ident12 := by
  obtain ⟨h1, h2⟩ := andB_eq_true.1 h
  obtain ⟨-, h1⟩ := andB_eq_true.1 h1
  obtain ⟨h3, h1⟩ := andB_eq_true.1 h1
  obtain ⟨h4, h1⟩ := andB_eq_true.1 h1
  obtain ⟨h5, h6⟩ := andB_eq_true.1 h1
  rw [mulF_eq] at h6 h2
  exact ⟨blt_eq_true.1 h3, blt_eq_true.1 h4, Nat.le_of_ble_eq_true h5, beq_eq_true.1 h6,
    beq_eq_true.1 h2⟩

theorem hMat_zero : hMat 0 = 0 := by decide

theorem hInv_zero : hInv 0 = 0 := by decide

theorem mul12_zero_right (X : ℕ) : mul12 X 0 = 0 :=
  eq_of_toMat_eq (mul12_lt X 0) (by norm_num) (by rw [toMat_mul12, toMat_zero, mul_zero])

theorem cinv_tree {u : ℕ} (hu : CInv d φ t u) : CInv d φ t (jTree d.FT true d.ND d.NOM u) := by
  generalize hr : jTree d.FT true d.ND d.NOM u = r
  unfold jTree at hr
  simp only [strictN_eq] at hr
  rcases brecN hr.symm with h | ⟨hc, h⟩
  · rw [h]
    exact cinv_fail
  rw [h]
  obtain ⟨h1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h3, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h4, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h5, h6⟩ := andB_eq_true.1 hc
  have h1' : recOKm (d.FT (cIdx u)) (cIdx u) d.ND d.NOM = true := h1
  have h6' : Nat.beq (fNs (d.FT (cIdx u))) ident12 = true := h6
  have e3 := beq_eq_true.1 h3
  refine cinv_succ (cIdx_lt u) (by have := fDp_lt (d.FT (cIdx u)); omega) fun hk =>
    ⟨hu hk, recOKm_spec h1', Or.inl ⟨rfl, blt_eq_true.1 h2, e3, blt_eq_true.1 h4,
      beq_eq_true.1 h5, beq_eq_true.1 h6'⟩⟩

theorem cinv_ax {u a b : ℕ} (E2 : Env2 d LET x y t) (E : Env d φ x y t TH) (hu : CInv d φ t u) :
    CInv d φ t (jAx d.FT d.HT true d.ND d.NOM a b u) := by
  generalize hr : jAx d.FT d.HT true d.ND d.NOM a b u = r
  unfold jAx at hr
  simp only [strictN_eq] at hr
  rcases brecN hr.symm with h | ⟨hc, h⟩
  · rw [h]
    exact cinv_fail
  rw [h]
  obtain ⟨h1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h3, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h4, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h5, h6⟩ := andB_eq_true.1 hc
  have h1' : recOKm (d.FT (cIdx u)) (cIdx u) d.ND d.NOM = true := h1
  have h6' : Nat.beq (fNs (d.FT (cIdx u))) (fPiI (d.FT (cIdx u))) = true := h6
  have hrec := recOKm_spec h1'
  have e5 := beq_eq_true.1 h5
  rw [mulF_eq] at e5
  have hπ : InN LET (fPi (d.FT (cIdx u))) := by
    rcases Nat.lt_or_ge a d.nH with ha | ha
    · rcases Nat.lt_or_ge b d.nH with hb | hb
      · rw [e5]
        exact InN_mul (E2.hdrI a ha) (E.hdr b hb)
      · have := hrec.2.2.2.1
        rw [e5, E.hdr0 b hb, hMat_zero, mul12_zero_right, mul12_zero] at this
        exact absurd this.symm ident12_ne_zero
    · have := hrec.2.2.2.1
      rw [e5, E.hdr0 a ha, hInv_zero, mul12_zero, mul12_zero] at this
      exact absurd this.symm ident12_ne_zero
  refine cinv_succ (cIdx_lt u) (cNd_lt u) fun hk =>
    ⟨hu hk, hrec, Or.inr (Or.inl ⟨rfl, beq_eq_true.1 h2, beq_eq_true.1 h3, beq_eq_true.1 h4, hπ,
      beq_eq_true.1 h6'⟩)⟩

theorem oinv_start {u a b D0 w0 : ℕ} (E2 : Env2 d LET x y t) (E : Env d φ x y t TH)
    (hu : CInv d φ t u) : OInv d φ x y t (stSm d.FT d.HT d.WT d.ND d.NOM a b D0 w0 u) := by
  generalize hr : stSm d.FT d.HT d.WT d.ND d.NOM a b D0 w0 u = r
  unfold stSm at hr
  simp only [strictT_eq] at hr
  rcases brec4 hr.symm with h | ⟨hc, h⟩
  · rw [h]
    exact Or.inl rfl
  rw [h]
  obtain ⟨h1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h2, h3⟩ := andB_eq_true.1 hc
  obtain ⟨ha, hb⟩ := andB_eq_true.1 h1
  have hD0 := blt_eq_true.1 h2
  have hrec := recOKm_spec h3
  have ha' : a < d.nH := by
    by_contra hc
    have := blt_eq_true.1 ha
    rw [E.hdr0 a (by omega)] at this
    omega
  have hb' : b < d.nH := by
    by_contra hc
    have := blt_eq_true.1 hb
    rw [E.hdr0 b (by omega)] at this
    omega
  have hP0 : InN LET (mulF (hInv (d.HT a)) (hMat (d.HT b))) := by
    rw [mulF_eq]
    exact InN_mul (E2.hdrI a ha') (E.hdr b hb')
  have hD0' : D0 < 65536 := by have := E.nd; omega
  obtain ⟨hW, hW1⟩ := E2.words w0
  refine Or.inr ⟨hdr D0 (cIdx u) (cNd u) (mulF (hInv (d.HT a)) (hMat (d.HT b))),
    wW (d.WT w0), wN (d.WT w0), cIdx u, cNd u, D0, mulF (hInv (d.HT a)) (hMat (d.HT b)),
    hdr_D0 hD0', hdr_K hD0' (cIdx_lt u), hdr_nd hD0' (cIdx_lt u) (cNd_lt u),
    hdr_P0 hD0' (cIdx_lt u) (cNd_lt u), ?_, fun hk => ⟨hu hk, hrec, hP0, hW, hW1, fun w _ => ?_⟩⟩
  · change mkD D0 (cIdx u) (cNd u) _ / 65536 = _
    rw [mkD_eq hD0' (cIdx_lt u) (cNd_lt u)]
    omega
  · refine Or.inr ⟨D0, 0, 0, _, ident12, ?_, hD0, Nat.zero_le _, Nat.zero_le _,
      fun _ => ⟨hP0, InN_one, ?_⟩, fun h => absurd h zero_ne_one⟩
    · rw [mkD_eq hD0' (cIdx_lt u) (cNd_lt u), wInit_cur hW]
    · unfold Q
      rw [ev_one, wv_zero]
      group

theorem oinv_step (E : Env d φ x y t TH) {s s' : St4} (hs : OInv d φ x y t s)
    (hst : IsStep d TH s s') : OInv d φ x y t s' := by
  obtain ⟨d0, p0, n0, c0⟩ := s
  have hP := isStep_pres hst
  rcases hs with h0 | ⟨R, W, n, K, nd, D0, P0, h1, h2, h3, h4, h5, hsem⟩
  · exact Or.inl (hP.1 h0)
  rcases hP.2 with h | hR
  · exact Or.inl h
  refine Or.inr ⟨R, W, n, K, nd, D0, P0, h1, h2, h3, h4, hR.trans h5, fun hK => ?_⟩
  obtain ⟨hV, hrec, hP0, hW, hW1, hall⟩ := hsem hK
  refine ⟨hV, hrec, hP0, hW, hW1, fun w hw => ?_⟩
  rcases hall w hw with h0 | ⟨D, i, f, p, nn, he, hD, hi, hf, hg0, hg1⟩
  · exact Or.inl (hP.1 h0)
  rw [he] at hst
  exact good_of_next hf hg0 hg1 (isStep_next E hst h2 hw (fun _ => hrec) hW hD hi hf)

theorem cinv_end {s : St4} (hs : OInv d φ x y t s) : CInv d φ t (mEndJ s) := by
  obtain ⟨d0, p0, n0, c0⟩ := s
  generalize hr : mEndJ (d0, p0, n0, c0) = r
  unfold mEndJ at hr
  rcases brecN hr.symm with h | ⟨hc, h⟩
  · rw [h]
    exact cinv_fail
  rw [h]
  obtain ⟨hc1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨hc2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨hc3, hc4⟩ := andB_eq_true.1 hc
  have en := beq_eq_true.1 hc3
  rcases hs with h0 | ⟨R, W, n, K, nd, D0, P0, h1, h2, h3, h4, h5, hsem⟩
  · exact absurd ((beq_eq_true.1 hc3).symm.trans h0) ident12_ne_zero
  have hdK : dK d0 = K := by rw [dK_gen, h5, h2]
  have hdN : dNd d0 = nd := by rw [dNd_gen, h5, h3]
  rw [hdK, hdN]
  refine cinv_succ (nd := nd) (by omega) (by omega) fun hK => ?_
  obtain ⟨hV, hrec, hP0, -, hW1, hall⟩ := hsem hK
  refine ⟨hV, hrec, Or.inr (Or.inr ⟨rfl, fun w hw => ?_⟩)⟩
  rcases hall w hw with h0 | ⟨D, i, f, p, nn, he, hD, hi, hf, -, hg1⟩
  · exact absurd (en.symm.trans h0) ident12_ne_zero
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  have hD' : D < 65536 := by omega
  rw [dD_eq R hD', dD0_eq R hD', h1] at hc1
  rw [dP0_eq R hD', h4] at hc2
  have eD := beq_eq_true.1 hc1
  have eP := beq_eq_true.1 hc2
  obtain ⟨rfl, rfl⟩ := cur_end hf hi (beq_eq_true.1 hc4)
  subst eD eP en
  obtain ⟨hpi, hni, hm⟩ := hg1 rfl
  have hπ := hpi.1 hP0
  have hnK := hni.1 InN_one
  refine ⟨hπ, hnK, (hm hπ hnK).1 ?_⟩
  unfold Q
  rw [ev_one, hW1]
  group

end Facts

theorem rec_inv {β : Type} (P : β → Prop) (step : ℕ → (ℕ → β → β) → ℕ → β → β)
    (hstep : ∀ n (ih : ℕ → β → β), (∀ r q, P q → P (ih r q)) → ∀ r q, P q → P (step n ih r q)) :
    ∀ N r q, P q → P (Nat.rec (motive := fun _ => ℕ → β → β) (fun _ q => q) step N r q)
  | 0, _, _, h => h
  | N + 1, r, q, h => hstep N _ (rec_inv P step hstep N) r q h

theorem chunk_inv (d : MD) (k : KD) (tr : Bool) (P : ℕ × St4 → Prop) (I : ℕ → Prop)
    (hstep : ∀ c p q, P q → P (mStep d k tr c p q)) (hend : ∀ q, P q → I (endM q)) {C u : ℕ}
    (h0 : P (2 * u, bad4)) : I (chunkM d k tr C u) := by
  unfold chunkM
  refine hend _ (rec_inv P _ (fun n ih hih r q hq => ?_) _ _ _ h0)
  simp only [strictT_eq, forceM_eq]
  exact hih _ _ (hstep _ _ _ hq)

theorem runM_inv (d : MD) (k : KD) (I : ℕ → Prop) (hc : ∀ C u, I u → I (chunkM d k false C u)) :
    ∀ l u, I u → I (runM d k l u)
  | [], _, h => h
  | C :: l, u, h => by
    change I (strictN (chunkM d k false C u) (runM d k l))
    rw [strictN_eq]
    exact runM_inv d k I hc l _ (hc C u h)

theorem runT_inv (d : MD) (k : KD) (I : ℕ → Prop) (hc : ∀ C u, I u → I (chunkM d k true C u)) :
    ∀ l u, I u → I (runT d k l u)
  | [], _, h => h
  | C :: l, u, h => by
    change I (strictN (chunkM d k true C u) (runT d k l))
    rw [strictN_eq]
    exact runT_inv d k I hc l _ (hc C u h)

theorem mStep_even_F {d : MD} {k : KD} {c p m : ℕ} {s : St4} {r : ℕ × St4} (hm : m % 2 = 0)
    (hr : mStep d k false c p (m, s) = r) :
    (∃ a b D0 w0, r = (1, stSm d.FT d.HT d.WT d.ND d.NOM a b D0 w0 (m / 2))) ∨
      r = (2 * jTree d.FT true d.ND d.NOM (m / 2), bad4) ∨
      (∃ a b, r = (2 * jAx d.FT d.HT true d.ND d.NOM a b (m / 2), bad4)) ∨ r = mFail := by
  unfold mStep at hr
  have hr := bsel_of_true (by rw [land1, hm]; rfl) hr
  have hr := bsel_of_false rfl hr
  rcases bsel_eq hr with hr | hr
  · exact Or.inl ⟨_, _, _, _, by rw [← hr, shr1]⟩
  rcases bsel_eq hr with hr | hr
  · exact Or.inr (Or.inl (by rw [← hr, shr1]; rfl))
  rcases bsel_eq hr with hr | hr
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, by rw [← hr, shr1]; rfl⟩))
  · exact Or.inr (Or.inr (Or.inr hr.symm))

theorem mStep_odd_F {d : MD} {k : KD} {c p m : ℕ} {s : St4} {r : ℕ × St4} (hm : m % 2 = 1)
    (hr : mStep d k false c p (m, s) = r) :
    (∃ s', IsStep d k.TH s s' ∧ r = (1, s')) ∨ r = (2 * mEndJ s, bad4) ∨ r = mFail := by
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
  have hr := bsel_of_false rfl hr
  rcases bsel_eq hr with hr | hr
  · exact Or.inr (Or.inl (by rw [← hr]; rfl))
  · exact Or.inr (Or.inr hr.symm)

section FactRun

variable {d : MD} {k : KD} {LET : ℕ} {G : Type} [Group G] {φ : Nhat LET →* G} {x y t : G}

theorem pinv_counter {u : ℕ} (hu : CInv d φ t u) : PInv d φ x y t (2 * u, bad4) :=
  ⟨fun _ => by rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact hu, fun h => by
    change 2 * u % 2 = 1 at h
    omega⟩

theorem pinv_fail : PInv d φ x y t mFail := pinv_counter cinv_fail

theorem endM_inv {q : ℕ × St4} (hq : PInv d φ x y t q) : CInv d φ t (endM q) := by
  obtain ⟨m, s⟩ := q
  generalize hr : endM (m, s) = r
  unfold endM at hr
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hr := bsel_of_true (by rw [land1, hm]; rfl) hr
    rw [← hr, shr1]
    exact hq.1 hm
  · have hr := bsel_of_false (by rw [land1, hm]; rfl) hr
    rw [← hr]
    exact cinv_fail

theorem pinv_step (E : Env d φ x y t k.TH) (E2 : Env2 d LET x y t) (c p : ℕ) {q : ℕ × St4}
    (hq : PInv d φ x y t q) : PInv d φ x y t (mStep d k false c p q) := by
  obtain ⟨m, s⟩ := q
  generalize hr : mStep d k false c p (m, s) = r
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hu := hq.1 hm
    rcases mStep_even_F hm hr with ⟨a, b, D0, w0, rfl⟩ | rfl | ⟨a, b, rfl⟩ | rfl
    · exact ⟨fun h => absurd h (by norm_num), fun _ => oinv_start E2 E hu⟩
    · exact pinv_counter (cinv_tree hu)
    · exact pinv_counter (cinv_ax E2 E hu)
    · exact pinv_fail
  · have hs := hq.2 hm
    rcases mStep_odd_F hm hr with ⟨s', hst, rfl⟩ | rfl | rfl
    · exact ⟨fun h => absurd h (by norm_num), fun _ => oinv_step E hs hst⟩
    · exact pinv_counter (cinv_end hs)
    · exact pinv_fail

theorem facts_run (E : Env d φ x y t k.TH) (E2 : Env2 d LET x y t) {MW : List ℕ}
    (h : runM d k MW (mkC 0 1) = mkC d.NF d.ND) : Valid d φ t d.NF d.ND := by
  have hNF : d.NF < 4294967296 := by have := E2.nf; omega
  have hND : d.ND < 4294967296 := by have := E.nd; omega
  have hI := runM_inv d k (CInv d φ t) (fun C u hu => chunk_inv d k false (PInv d φ x y t)
    (CInv d φ t) (fun c p _ hq => pinv_step E E2 c p hq) (fun _ hq => endM_inv hq)
    (pinv_counter hu)) MW (mkC 0 1) (fun _ => by rw [cIdx_mkC _ (by norm_num)]; exact valid_zero _)
  rw [h] at hI
  have := hI (by rw [cIdx_mkC _ hNF]; have := E2.nf; omega)
  rwa [cIdx_mkC _ hNF, cNd_mkC hNF hND] at this

theorem tree_w (nf : ℕ) (T : ℕ → Prop) (p c : ℕ → ℕ) (g : ℕ → G)
    (hpc : ∀ i < nf, T i → p i < c i)
    (hinj : ∀ i < nf, ∀ i' < nf, T i → T i' → c i = c i' → i = i') :
    ∃ w : ℕ → G, w 0 = 1 ∧ ∀ i < nf, T i → w (c i) = w (p i) * g i := by
  classical
  have key : ∀ B, ∃ w : ℕ → G, w 0 = 1 ∧
      ∀ i < nf, T i → c i < B → w (c i) = w (p i) * g i := by
    intro B
    induction B with
    | zero => exact ⟨fun _ => 1, rfl, fun i _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ B ih =>
      obtain ⟨w, hw0, hw⟩ := ih
      refine ⟨fun D => if D = B then
          (if hB : ∃ i, i < nf ∧ T i ∧ c i = B then w (p hB.choose) * g hB.choose else w B)
        else w D, ?_, ?_⟩
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
  obtain ⟨w, hw0, hw⟩ := key ((Finset.range nf).sup c + 1)
  exact ⟨w, hw0, fun i hi hTi =>
    hw i hi hTi (Nat.lt_succ_of_le (Finset.le_sup (f := c) (Finset.mem_range.2 hi)))⟩

theorem facts_hold {NF nd : ℕ} (hV : Valid d φ t NF nd) :
    ∃ w : ℕ → G, w 0 = 1 ∧ ∀ g < NF, RecV d (d.FT g) ∧ MF d φ t w (d.FT g) := by
  obtain ⟨nxf, -, hf⟩ := hV
  have mono1 : ∀ g < NF, nxf g ≤ nxf (g + 1) := fun g hg => by
    rcases (hf g hg).2 with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> omega
  have mono : ∀ a b, a ≤ b → b ≤ NF → nxf a ≤ nxf b := by
    intro a b hab hb
    induction b with
    | zero => rw [Nat.le_zero.1 hab]
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hab) with h1 | h1
      · exact Nat.le_trans (ih (by omega) (by omega)) (mono1 b (by omega))
      · rw [h1]
  have tr : ∀ g < NF, nxf (g + 1) = nxf g + 1 → fDp (d.FT g) = nxf g ∧ fD (d.FT g) < nxf g := by
    intro g hg hT
    rcases (hf g hg).2 with ⟨-, -, h1, h2, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact ⟨h1, h2⟩
    · omega
    · omega
  have hinj : ∀ i < NF, ∀ i' < NF, nxf (i + 1) = nxf i + 1 → nxf (i' + 1) = nxf i' + 1 →
      fDp (d.FT i) = fDp (d.FT i') → i = i' := by
    intro i hi i' hi' ht ht' e
    rw [(tr i hi ht).1, (tr i' hi' ht').1] at e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := mono (i + 1) i' (by omega) (by omega)
      omega
    · have := mono (i' + 1) i (by omega) (by omega)
      omega
  obtain ⟨w, hw0, hw⟩ := tree_w NF (fun g => nxf (g + 1) = nxf g + 1) (fun g => fD (d.FT g))
    (fun g => fDp (d.FT g)) (fun g => tv d φ t (fJ (d.FT g)))
    (fun g hg hT => lt_of_lt_of_eq (tr g hg hT).2 (tr g hg hT).1.symm) hinj
  refine ⟨w, hw0, fun g => ?_⟩
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    obtain ⟨hrec, ⟨e1, -, -, -, hπ, hn⟩ | ⟨-, hD, hJ, hDp, hπ, hn⟩ | ⟨-, hW⟩⟩ := hf g hg
    · refine ⟨hrec, by rw [hπ]; exact InN_one, by rw [hn]; exact InN_one, ?_⟩
      unfold MEq
      rw [hπ, hn, ev_one, one_mul, mul_one]
      exact (hw g hg e1).symm
    · have hnI : InN LET (fNs (d.FT g)) := by
        rw [hn]
        exact InN_inv hπ hrec.2.2.2.1
      refine ⟨hrec, hπ, hnI, ?_⟩
      unfold MEq
      rw [hD, hJ, hDp, tv_zero, hw0, hn, ev_inv φ hπ hrec.2.2.2.1]
      group
    · exact ⟨hrec, hW w fun g' hg' => ih g' hg' (by omega)⟩

end FactRun

end CFSG.KJ4.MLevel

end
