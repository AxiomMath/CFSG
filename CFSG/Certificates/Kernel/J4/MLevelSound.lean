module

public import CFSG.Certificates.Kernel.J4.ModelsSound
public import CFSG.Certificates.Kernel.J4.MLevelBits
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KJ4.MLevel

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models
open CFSG.Certificates.DceWord (lvE wv)
open CFSG.Certificates.J4Words (jv invJ jv_inv)
open CFSG.Certificates.J4KShape (rv)
open scoped Matrix

set_option exponentiation.threshold 300

theorem brec_true {a b c : Bool} (h : Bool.rec (motive := fun _ => Bool) a b c = true) :
    (c = true ∧ b = true) ∨ (c = false ∧ a = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem brec4 {X Y : St4} {b : Bool} (h : Y = Bool.rec (motive := fun _ => St4) bad4 X b) :
    Y = bad4 ∨ (b = true ∧ Y = X) := by
  cases b
  · exact Or.inl h
  · exact Or.inr ⟨rfl, h⟩

theorem brecN {X Y : ℕ} {b : Bool} (h : Y = Bool.rec (motive := fun _ => ℕ) FAIL X b) :
    Y = FAIL ∨ (b = true ∧ Y = X) := by
  cases b
  · exact Or.inl h
  · exact Or.inr ⟨rfl, h⟩

theorem strictT_eq {α : Type} (y : ℕ) (k : ℕ → α) : strictT y k = k y := by
  cases y <;> rfl

theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem refS_spec {K S g c : ℕ} (h : refS K S g c = true) :
    (S ≠ 1 ∧ g < K) ∨ (S = 1 ∧ g = K ∧ Nat.land c 1 = 0) := by
  rcases brec_true h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨h3, h4⟩ := andB_eq_true.1 h2
    exact Or.inr ⟨beq_eq_true.1 h1, beq_eq_true.1 h3, beq_eq_true.1 h4⟩
  · exact Or.inl ⟨Nat.ne_of_beq_eq_false h1, blt_eq_true.1 h2⟩

theorem mul12_zero (X : ℕ) : mul12 0 X = 0 :=
  eq_of_toMat_eq (mul12_lt 0 X) (by norm_num) (by rw [toMat_mul12, toMat_zero, zero_mul])

theorem ident12_ne_zero : ident12 ≠ 0 := by decide

theorem lor_zero' (f : ℕ) : Nat.lor f 0 = f := Nat.or_zero f

theorem fD_lt (F : ℕ) : fD F < 65536 := by
  change Nat.land _ 65535 < 65536
  rw [land65535]
  omega

theorem fDp_lt (F : ℕ) : fDp F < 65536 := by
  change Nat.land _ 65535 < 65536
  rw [land65535]
  omega

theorem setD_gen (d : ℕ) {D' : ℕ} (hD' : D' < 65536) : setD d D' / 65536 = d / 65536 := by
  have e : d = d % 65536 + 65536 * (d / 65536) := by omega
  rw [e, setD_eq _ (Nat.mod_lt _ (by norm_num)) hD']
  omega

theorem dK_gen (d : ℕ) : dK d = d / 65536 / 65536 % 4294967296 := by
  have e : d = d % 65536 + 65536 * (d / 65536) := by omega
  rw [e, dK_eq _ (Nat.mod_lt _ (by norm_num))]
  omega

theorem dNd_gen (d : ℕ) : dNd d = d / 65536 / 281474976710656 % 4294967296 := by
  have e : d = d % 65536 + 65536 * (d / 65536) := by omega
  rw [e, dNd_eq _ (Nat.mod_lt _ (by norm_num))]
  omega

section Memb

variable {LET : ℕ}

@[expose] def InN (LET m : ℕ) : Prop := ∃ g : Nhat LET, ((g : GLm) : Mat12) = toMat m

theorem InN_one : InN LET ident12 := ⟨1, by rw [toMat_ident12]; rfl⟩

theorem InN_mul {a b : ℕ} (ha : InN LET a) (hb : InN LET b) : InN LET (mul12 a b) := by
  obtain ⟨g, hg⟩ := ha
  obtain ⟨h, hh⟩ := hb
  exact ⟨g * h, by rw [toMat_mul12, ← hg, ← hh]; rfl⟩

theorem InN_mul_left {a x : ℕ} (ha : InN LET a) : InN LET (mul12 a x) ↔ InN LET x := by
  refine ⟨fun hx => ?_, InN_mul ha⟩
  obtain ⟨g, hg⟩ := ha
  obtain ⟨h, hh⟩ := hx
  refine ⟨g⁻¹ * h, ?_⟩
  rw [toMat_mul12, ← hg] at hh
  change (((g : GLm)⁻¹ : GLm) : Mat12) * ((h : GLm) : Mat12) = _
  rw [hh, ← mul_assoc, Units.inv_mul, one_mul]

theorem InN_mul_right {a x : ℕ} (ha : InN LET a) : InN LET (mul12 x a) ↔ InN LET x := by
  refine ⟨fun hx => ?_, fun hx => InN_mul hx ha⟩
  obtain ⟨g, hg⟩ := ha
  obtain ⟨h, hh⟩ := hx
  refine ⟨h * g⁻¹, ?_⟩
  rw [toMat_mul12, ← hg] at hh
  change ((h : GLm) : Mat12) * (((g : GLm)⁻¹ : GLm) : Mat12) = _
  rw [hh, mul_assoc, Units.mul_inv, mul_one]

theorem InN_inv {a b : ℕ} (ha : InN LET a) (h : mul12 a b = ident12) : InN LET b :=
  (InN_mul_left ha).1 (h ▸ InN_one)

theorem InN_inv' {a b : ℕ} (hb : InN LET b) (h : mul12 a b = ident12) : InN LET a :=
  (InN_mul_right hb).1 (h ▸ InN_one)

theorem InN_inv_iff {a b : ℕ} (h : mul12 a b = ident12) : InN LET a ↔ InN LET b :=
  ⟨fun ha => InN_inv ha h, fun hb => InN_inv' hb h⟩

variable {G : Type} [Group G] (φ : Nhat LET →* G)

open Classical in
@[expose] noncomputable def ev (m : ℕ) : G := if h : InN LET m then φ h.choose else 1

theorem ev_eq {m : ℕ} (g : Nhat LET) (hg : ((g : GLm) : Mat12) = toMat m) : ev φ m = φ g := by
  have h : InN LET m := ⟨g, hg⟩
  rw [ev, dite_eq_left h]
  congr 1
  exact Subtype.ext (Units.ext (h.choose_spec.trans hg.symm))

theorem ev_one : ev φ ident12 = 1 := by
  rw [ev_eq φ 1 (by rw [toMat_ident12]; rfl), map_one]

theorem ev_mul {a b : ℕ} (ha : InN LET a) (hb : InN LET b) :
    ev φ (mul12 a b) = ev φ a * ev φ b := by
  obtain ⟨g, hg⟩ := ha
  obtain ⟨h, hh⟩ := hb
  rw [ev_eq φ g hg, ev_eq φ h hh, ev_eq φ (g * h) (by rw [toMat_mul12, ← hg, ← hh]; rfl), map_mul]

theorem ev_inv {a b : ℕ} (ha : InN LET a) (h : mul12 a b = ident12) : ev φ b = (ev φ a)⁻¹ := by
  have e := ev_mul φ ha (InN_inv ha h)
  rw [h, ev_one] at e
  exact eq_inv_of_mul_eq_one_right e.symm

variable (x y t : G)

@[expose] noncomputable def fv (c : ℕ) : G := lvE (jv x y t 1) c

theorem fv_eps : fv x y t 255 = 1 := by simp [fv, lvE]

theorem fv_t : fv x y t 4 = t := by simp [fv, lvE, jv]

theorem wv_zero (f : ℕ → G) (W : ℕ) : wv f W 0 = 1 := by simp [wv]

theorem wv_succ' (f : ℕ → G) (W n : ℕ) : wv f W (n + 1) = wv f W n * f (wLet W n) :=
  CFSG.Certificates.DceWord.wv_succ f W n

theorem wv_seg (f : ℕ → G) {W u i m : ℕ} (h : ∀ q < m, wLet W (i + q) = wLet u q) :
    wv f W (i + m) = wv f W i * wv f u m := by
  rw [CFSG.Certificates.DceWord.wv_split]
  congr 1
  unfold wv
  congr 1
  refine List.map_congr_left fun q hq => ?_
  exact congrArg f (h q (List.mem_range.1 hq))

variable {φ x y}

theorem letter_mem (hx : chkInv (letMat LET 0) (letMat LET 1) = true)
    (hy : chkInv (letMat LET 2) (letMat LET 3) = true)
    (hφx : ∀ g : Nhat LET, (g : GLm) = xh LET → φ g = x)
    (hφy : ∀ g : Nhat LET, (g : GLm) = yh LET → φ g = y) {c : ℕ} (hc : c < 4) :
    ∃ g : Nhat LET, ((g : GLm) : Mat12) = toMat (letMat LET c) ∧ φ g = fv x y t c := by
  have mx : xh LET ∈ Nhat LET := Subgroup.subset_closure (by simp)
  have my : yh LET ∈ Nhat LET := Subgroup.subset_closure (by simp)
  interval_cases c
  · exact ⟨⟨xh LET, mx⟩, val_lu hx, by rw [hφx _ rfl]; simp [fv, lvE, jv]⟩
  · refine ⟨⟨xh LET, mx⟩⁻¹, val_inv_lu hx, ?_⟩
    rw [map_inv, hφx _ rfl]
    simp [fv, lvE, jv]
  · exact ⟨⟨yh LET, my⟩, val_lu hy, by rw [hφy _ rfl]; simp [fv, lvE, jv]⟩
  · refine ⟨⟨yh LET, my⟩⁻¹, val_inv_lu hy, ?_⟩
    rw [map_inv, hφy _ rfl]
    simp [fv, lvE, jv]

theorem eval_mem (hx : chkInv (letMat LET 0) (letMat LET 1) = true)
    (hy : chkInv (letMat LET 2) (letMat LET 3) = true)
    (hφx : ∀ g : Nhat LET, (g : GLm) = xh LET → φ g = x)
    (hφy : ∀ g : Nhat LET, (g : GLm) = yh LET → φ g = y) {w n M : ℕ}
    (hl : ∀ q < n, wLet w q < 4) (h : chkEval LET w n M = true) :
    InN LET M ∧ ev φ M = wv (fv x y t) w n := by
  have key : ∀ m ≤ n, ∃ g : Nhat LET,
      ((g : GLm) : Mat12) = wordVal (fun c => toMat (letMat LET c)) w m ∧ φ g = wv (fv x y t) w m := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨1, rfl, by rw [map_one, wv_zero]⟩
    | succ m ih =>
      intro hm
      obtain ⟨g, hg, hφg⟩ := ih (by omega)
      obtain ⟨g', hg', hφg'⟩ := letter_mem t hx hy hφx hφy (hl m (by omega))
      refine ⟨g * g', ?_, ?_⟩
      · rw [wordVal_succ, ← hg, ← hg']
        rfl
      · rw [map_mul, hφg, hφg', wv_succ']
  obtain ⟨g, hg, hφg⟩ := key n le_rfl
  have hM : ((g : GLm) : Mat12) = toMat M := by rw [hg, chkEval_sound h]
  exact ⟨⟨g, hM⟩, by rw [ev_eq φ g hM, hφg]⟩

end Memb

theorem pt_comp {TH P g p h : ℕ} (hT : ptOK TH = true) (hP : ptOK P = true)
    (hg : (fun v => v ᵥ* toMat g) '' ptVecs TH = ptVecs P) (hp : S.chkPtF P p TH h = true) :
    (fun v => v ᵥ* toMat (mul12 g p)) '' ptVecs TH = ptVecs TH := by
  rw [chkPtF_eq] at hp
  rw [toMat_mul12, image_vecMul_mul, hg, chkPt_image hP hT hp]

section Facts

variable (d : MD) {LET : ℕ} {G : Type} [Group G] (φ : Nhat LET →* G) (x y t : G)

@[expose] noncomputable def gj (j : ℕ) : ℕ := oG (oBase (d.OT j))

@[expose] noncomputable def tv (J : ℕ) : G :=
  if J = 0 then 1 else (ev φ (gj d (J - 1)))⁻¹ * t * ev φ (gj d (J - 1))

@[expose] def MEq (w : ℕ → G) (F : ℕ) : Prop :=
  w (fD F) * tv d φ t (fJ F) = ev φ (fNs F) * w (fDp F) * ev φ (fPi F)

@[expose] def MF (w : ℕ → G) (F : ℕ) : Prop := InN LET (fPi F) ∧ InN LET (fNs F) ∧ MEq d φ t w F

@[expose] def RecV (F : ℕ) : Prop :=
  fD F < d.ND ∧ fDp F < d.ND ∧ fJ F ≤ d.NOM ∧ mul12 (fPi F) (fPiI F) = ident12 ∧
    mul12 (fNs F) (fNIs F) = ident12

@[expose] noncomputable def Q (w : ℕ → G) (W D p nn i : ℕ) : G :=
  ev φ nn * w D * ev φ p * (wv (fv x y t) W i)⁻¹

structure Env (TH : ℕ) : Prop where
  nd : d.ND < 65535
  th : ptOK TH = true
  ht : t * t = 1
  stab : ∀ m, InN LET m → (fun v => v ᵥ* toMat m) '' ptVecs TH = ptVecs TH →
    ev φ m * t = t * ev φ m
  hdr : ∀ h < d.nH, InN LET (hMat (d.HT h))
  hdr0 : ∀ h, d.nH ≤ h → d.HT h = 0
  om : ∀ j < d.NOM, oJ (d.OT j) ≠ 0 → InN LET (gj d j) ∧ ptOK (oP (d.OT j)) = true ∧
    (fun v => v ᵥ* toMat (gj d j)) '' ptVecs TH = ptVecs (oP (d.OT j))
  seg : ∀ e, sgN (d.SG e) = 0 ∨ ((∀ q < sgN (d.SG e), wLet (sgW (d.SG e)) q < 4) ∧
    InN LET (sgM (d.SG e)) ∧ ev φ (sgM (d.SG e)) = wv (fv x y t) (sgW (d.SG e)) (sgN (d.SG e)))

@[expose] def Next (w : ℕ → G) (R W n K D p nn i f : ℕ) (s' : St4) : Prop :=
  s'.2.2.1 = 0 ∨
  (∃ D' p' nn' i', s' = (D' + 65536 * R, p', nn', cur W n i' f) ∧ D' < d.ND ∧ i' ≤ n ∧
    (InN LET p' ↔ InN LET p) ∧ (InN LET nn' ↔ InN LET nn) ∧
    (InN LET p → InN LET nn → Q φ x y t w W D' p' nn' i' = Q φ x y t w W D p nn i)) ∨
  (f = 0 ∧ ∃ D' p' nn' i', s' = (D' + 65536 * R, p', nn', cur W n i' 1) ∧ D' < d.ND ∧ i' ≤ n ∧
    (InN LET p → InN LET nn → (InN LET p' ↔ InN LET (fPi (d.FT K))) ∧
      (InN LET nn' ↔ InN LET (fNs (d.FT K))) ∧
      (InN LET (fPi (d.FT K)) → InN LET (fNs (d.FT K)) →
        (Q φ x y t w W D' p' nn' i' = Q φ x y t w W D p nn i ↔ MEq d φ t w (d.FT K)))))

end Facts

section Core

variable {d : MD} {LET : ℕ} {G : Type} [Group G] {φ : Nhat LET →* G} {x y t : G}

theorem sandwich {a b X Y : G} : a * X * b = a * Y * b ↔ X = Y := by
  rw [mul_left_inj, mul_right_inj]

theorem tv_zero : tv d φ t 0 = 1 := by simp [tv]

theorem recV_inv {F : ℕ} (h : RecV d F) (hπ : InN LET (fPi F)) (hn : InN LET (fNs F)) :
    InN LET (fPiI F) ∧ InN LET (fNIs F) ∧ ev φ (fPiI F) = (ev φ (fPi F))⁻¹ ∧
      ev φ (fNIs F) = (ev φ (fNs F))⁻¹ :=
  ⟨InN_inv hπ h.2.2.2.1, InN_inv hn h.2.2.2.2, ev_inv φ hπ h.2.2.2.1, ev_inv φ hn h.2.2.2.2⟩

theorem core_Ef {w : ℕ → G} {W F p nn i : ℕ} (hp : InN LET p) (hn : InN LET nn)
    (hπ : InN LET (fPi F)) (hnF : InN LET (fNs F)) (hJ : fJ F = 0) (hl : fv x y t (wLet W i) = 1) :
    Q φ x y t w W (fDp F) (mul12 (fPi F) p) (mul12 nn (fNs F)) (i + 1) =
      Q φ x y t w W (fD F) p nn i ↔ MEq d φ t w F := by
  have e1 : Q φ x y t w W (fDp F) (mul12 (fPi F) p) (mul12 nn (fNs F)) (i + 1) =
      ev φ nn * (ev φ (fNs F) * w (fDp F) * ev φ (fPi F)) * (ev φ p * (wv (fv x y t) W i)⁻¹) := by
    unfold Q
    rw [ev_mul φ hπ hp, ev_mul φ hn hnF, wv_succ', hl]
    group
  have e2 : Q φ x y t w W (fD F) p nn i =
      ev φ nn * (w (fD F) * tv d φ t (fJ F)) * (ev φ p * (wv (fv x y t) W i)⁻¹) := by
    unfold Q
    rw [hJ, tv_zero]
    group
  rw [e1, e2, sandwich, MEq, eq_comm]

theorem core_Eb {w : ℕ → G} {W F p nn i : ℕ} (hp : InN LET p) (hn : InN LET nn) (hF : RecV d F)
    (hπ : InN LET (fPi F)) (hnF : InN LET (fNs F)) (hJ : fJ F = 0) (hl : fv x y t (wLet W i) = 1) :
    Q φ x y t w W (fD F) (mul12 (fPiI F) p) (mul12 nn (fNIs F)) (i + 1) =
      Q φ x y t w W (fDp F) p nn i ↔ MEq d φ t w F := by
  obtain ⟨hπi, hni, eπ, en⟩ := recV_inv (φ := φ) hF hπ hnF
  have e1 : Q φ x y t w W (fD F) (mul12 (fPiI F) p) (mul12 nn (fNIs F)) (i + 1) =
      ev φ nn * ((ev φ (fNs F))⁻¹ * (w (fD F) * tv d φ t (fJ F)) * (ev φ (fPi F))⁻¹) *
        (ev φ p * (wv (fv x y t) W i)⁻¹) := by
    unfold Q
    rw [ev_mul φ hπi hp, ev_mul φ hn hni, eπ, en, wv_succ', hl, hJ, tv_zero]
    group
  have e2 : Q φ x y t w W (fDp F) p nn i =
      ev φ nn * ((ev φ (fNs F))⁻¹ * (ev φ (fNs F) * w (fDp F) * ev φ (fPi F)) * (ev φ (fPi F))⁻¹) *
        (ev φ p * (wv (fv x y t) W i)⁻¹) := by
    unfold Q
    group
  rw [e1, e2, sandwich, sandwich, MEq]

theorem core_Tf {w : ℕ → G} {W F p nn i : ℕ} (hp : InN LET p) (hn : InN LET nn)
    (hπ : InN LET (fPi F)) (hnF : InN LET (fNs F)) (hl : fv x y t (wLet W i) = t)
    (htc : ev φ p * t * (ev φ p)⁻¹ = tv d φ t (fJ F)) :
    Q φ x y t w W (fDp F) (mul12 (fPi F) p) (mul12 nn (fNs F)) (i + 1) =
      Q φ x y t w W (fD F) p nn i ↔ MEq d φ t w F := by
  have e1 : Q φ x y t w W (fDp F) (mul12 (fPi F) p) (mul12 nn (fNs F)) (i + 1) =
      ev φ nn * (ev φ (fNs F) * w (fDp F) * ev φ (fPi F)) * (ev φ p * t⁻¹ * (wv (fv x y t) W i)⁻¹) := by
    unfold Q
    rw [ev_mul φ hπ hp, ev_mul φ hn hnF, wv_succ', hl]
    group
  have e2 : Q φ x y t w W (fD F) p nn i =
      ev φ nn * (w (fD F) * tv d φ t (fJ F)) * (ev φ p * t⁻¹ * (wv (fv x y t) W i)⁻¹) := by
    rw [← htc]
    unfold Q
    group
  rw [e1, e2, sandwich, MEq, eq_comm]

theorem core_Tb {w : ℕ → G} {W F p nn i : ℕ} (ht : t * t = 1) (hp : InN LET p) (hn : InN LET nn)
    (hF : RecV d F) (hπ : InN LET (fPi F)) (hnF : InN LET (fNs F)) (hl : fv x y t (wLet W i) = t)
    (htc : ev φ (mul12 (fPiI F) p) * t * (ev φ (mul12 (fPiI F) p))⁻¹ = tv d φ t (fJ F)) :
    Q φ x y t w W (fD F) (mul12 (fPiI F) p) (mul12 nn (fNIs F)) (i + 1) =
      Q φ x y t w W (fDp F) p nn i ↔ MEq d φ t w F := by
  obtain ⟨hπi, hni, eπ, en⟩ := recV_inv (φ := φ) hF hπ hnF
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have eR : ev φ (mul12 (fPiI F) p) = (ev φ (fPi F))⁻¹ * ev φ p := by rw [ev_mul φ hπi hp, eπ]
  rw [eR] at htc
  have e1 : Q φ x y t w W (fD F) (mul12 (fPiI F) p) (mul12 nn (fNIs F)) (i + 1) =
      ev φ nn * ((ev φ (fNs F))⁻¹ * (w (fD F) * tv d φ t (fJ F)) * (ev φ (fPi F))⁻¹) *
        (ev φ p * (wv (fv x y t) W i)⁻¹) := by
    rw [← htc]
    unfold Q
    rw [eR, ev_mul φ hn hni, en, wv_succ', hl, mul_inv_rev, hti]
    group
  have e2 : Q φ x y t w W (fDp F) p nn i =
      ev φ nn * ((ev φ (fNs F))⁻¹ * (ev φ (fNs F) * w (fDp F) * ev φ (fPi F)) * (ev φ (fPi F))⁻¹) *
        (ev φ p * (wv (fv x y t) W i)⁻¹) := by
    unfold Q
    group
  rw [e1, e2, sandwich, sandwich, MEq]

theorem tconj {TH : ℕ} (E : Env d φ x y t TH) {F p h : ℕ} (hJ0 : 0 < fJ F) (hJ : fJ F ≤ d.NOM)
    (hO : oJ (d.OT (fJ F - 1)) = fJ F) (hp : InN LET p)
    (hpt : S.chkPtF (oP (d.OT (fJ F - 1))) p TH h = true) :
    ev φ p * t * (ev φ p)⁻¹ = tv d φ t (fJ F) := by
  obtain ⟨hg, hP, hmap⟩ := E.om (fJ F - 1) (by omega) (by omega)
  have hs := E.stab _ (InN_mul hg hp) (pt_comp E.th hP hmap hpt)
  rw [ev_mul φ hg hp] at hs
  have hne : fJ F ≠ 0 := by omega
  rw [tv, ite_eq_right hne]
  calc ev φ p * t * (ev φ p)⁻¹
      = (ev φ (gj d (fJ F - 1)))⁻¹ * (ev φ (gj d (fJ F - 1)) * ev φ p * t) * (ev φ p)⁻¹ := by group
    _ = (ev φ (gj d (fJ F - 1)))⁻¹ * (t * (ev φ (gj d (fJ F - 1)) * ev φ p)) * (ev φ p)⁻¹ := by rw [hs]
    _ = _ := by group

end Core

end CFSG.KJ4.MLevel

end
