module

public import CFSG.Certificates.Kernel.TwistDce3.Words
public import CFSG.Certificates.Kernel.TwistDce2.Walk

public section

namespace CFSG.Certificates.TwDce3.Walk

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
open CFSG.KC.TwDce3 CFSG.KC.YModel CFSG.Certificates.CosetEnumeration
open CFSG.Certificates.TwDce.Words hiding evP_eq isOne_spec wsMk_spec wsFail_lt dN1_lt dN2_lt
open CFSG.Certificates.TwDce.Core hiding wsBad_fail
open CFSG.Certificates.TwDce2.Words hiding evP_eq isOne_spec
open CFSG.Certificates.TwDce2.Walk hiding val_one2 val_eq_of_isOne2 step_core2 tStep_spec
  posStep_mk posStep_fail foldl_fail posStep_spec walk_list wR2 walkRun_eq walk_core walkOK_spec
open CFSG.Certificates.TwDce3.Words

variable {G : Type*} [Group G]

theorem evalWord_twist {x : ℕ → G} {s : G} {NT M : ℕ}
    (hs : ∀ c < NT, thL M c < 12 ∧ x c * s = s * x (thL M c)) :
    ∀ l : List ℕ, (∀ c ∈ l, c < NT) → evalWord x l * s = s * evalWord x (l.map (thL M))
  | [], _ => by simp
  | c :: l, hl => by
    rw [List.map_cons, evalWord_cons, evalWord_cons, mul_assoc,
      evalWord_twist hs l fun d hd => hl d (List.mem_cons_of_mem _ hd), ← mul_assoc,
      (hs c (hl c List.mem_cons_self)).2, mul_assoc]

theorem GD.th {x : ℕ → G} {s : G} {NT M B tw : ℕ}
    (hs : ∀ c < NT, thL M c < 12 ∧ x c * s = s * x (thL M c)) (hok : wOK tw = true)
    (hlt : ∀ c ∈ lst tw, c < NT) (hl : wLen tw < B) :
    GD B (wTh M tw) ∧ val x tw * s = s * val x (wTh M tw) := by
  obtain ⟨h1, h2, h3⟩ := wTh_spec M tw
  refine ⟨⟨h2, fun c hc => ?_, by rw [h1]; exact hl⟩, ?_⟩
  · rw [h3, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact (hs d (hlt d hd)).1
  · unfold val
    rw [h3]
    exact evalWord_twist hs _ hlt

section Step

variable {PB : ℕ} {F RD RW RA : ℕ → ℕ} {INVM BS NB NT PSF PSB : ℕ} {H : Subgroup G} {x : ℕ → G}
  {t : G}

theorem val_one3
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {w : ℕ} (hw : ∀ c ∈ lst w, c < 12) (h : isOne PB F BS NB w = true) : val x w = 1 :=
  hone _ hw (isOne_spec h)

theorem val_eq_of_isOne3 (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {A B v w : ℕ} (hv : GD A v) (hw : GD B w) (hAB : A + B ≤ 2 ^ 32)
    (h : isOne PB F BS NB (wCat (wInv INVM v) w) = true) : val x v = val x w := by
  obtain ⟨g, e⟩ := GD.cat (hv.inv hinv).1 hw hAB
  have := val_one3 hone g.lt h
  rw [val_cat e, (hv.inv hinv).2] at this
  exact inv_mul_eq_one.mp this

variable (PB F INVM BS NB H x) in
theorem step_core3 (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {s : G} {M n n' w w' tw Sw a : ℕ}
    (hfact : CE H (X n * val x w * s) (X n' * val x w'))
    (hs : ∀ c < NT, thL M c < 12 ∧ x c * s = s * x (thL M c)) (hNT : NT ≤ 12)
    (hw : GD (2 ^ 16) w) (hw' : GD (2 ^ 16) w') (hT : wBelow NT tw = true)
    (htl : wLen tw < 2 ^ 16)
    (hS : GD (2 ^ 24) Sw) (hSc : X n * val x Sw * (X n)⁻¹ ∈ H) (ha : GD (2 ^ 30) a)
    (h1 : isOne PB F BS NB (wCat (wInv INVM tw) (wCat (wInv INVM w) (wCat (wInv INVM Sw) a))) =
      true) :
    CE H (X n * val x a * s) (X n' * val x (wCat w' (wTh M tw))) ∧
      GD (2 ^ 17) (wCat w' (wTh M tw)) := by
  obtain ⟨hTok, hTlt⟩ := wBelow_spec hT
  have gt : GD (2 ^ 16) tw := ⟨hTok, fun c hc => by have := hTlt c hc; omega, htl⟩
  obtain ⟨gth, hth⟩ := GD.th (x := x) (s := s) hs hTok hTlt htl
  obtain ⟨c1, e1⟩ := (hS.inv hinv).1.cat ha (by norm_num)
  obtain ⟨c2, e2⟩ := (hw.inv hinv).1.cat c1 (by norm_num)
  obtain ⟨c3, e3⟩ := (gt.inv hinv).1.cat c2 (by norm_num)
  obtain ⟨c4, e4⟩ := hw'.cat gth (by norm_num)
  refine ⟨?_, c4.mono (by norm_num)⟩
  have hv := val_one3 hone c3.lt h1
  rw [val_cat e3, val_cat e2, val_cat e1, (gt.inv hinv).2, (hw.inv hinv).2, (hS.inv hinv).2] at hv
  have ea : val x a = val x Sw * val x w * val x tw := by
    have := congrArg (fun z => val x Sw * (val x w * (val x tw * z))) hv
    simp only [mul_one] at this
    rw [mul_assoc, ← this]
    group
  rw [val_cat e4, ea]
  have e5 : X n * (val x Sw * val x w * val x tw) * s =
      (X n * val x Sw * (X n)⁻¹) * (X n * val x w * s * val x (wTh M tw)) := by
    rw [show X n * val x w * s * val x (wTh M tw) = X n * val x w * (s * val x (wTh M tw)) by
      group, ← hth]
    group
  rw [e5, ← mul_assoc (X n')]
  exact (CE.of_left hSc _).trans (hfact.mul_right _)

variable (PB F INVM BS NB NT PSF PSB RD RW RA H x t) in
theorem tStep_spec (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hNT : NT ≤ 12)
    (hTf : ∀ c < NT, thL PSF c < 12 ∧ x c * t = t * x (thL PSF c))
    (hTb : ∀ c < NT, thL PSB c < 12 ∧ x c * t⁻¹ = t⁻¹ * x (thL PSB c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r k a J : ℕ} (fwd : Bool) (hH : Hist2 RD RW RA H x t X r) (ha : GD (2 ^ 30) a)
    (hf : wsFail (tStep PB F INVM BS NB NT PSF PSB RD RW RA r k a J fwd).1 = 0) :
    CE H (X k * val x a * (if fwd = true then t else t⁻¹))
      (X (wsK (tStep PB F INVM BS NB NT PSF PSB RD RW RA r k a J fwd).1) *
        val x (tStep PB F INVM BS NB NT PSF PSB RD RW RA r k a J fwd).2) ∧
    GD (2 ^ 17) (tStep PB F INVM BS NB NT PSF PSB RD RW RA r k a J fwd).2 := by
  have hm : fld J 20 255 < 256 := fld_lt_succ _ _ _
  have hpath : ∀ m L, m < 256 → 0 < pathW INVM RD RW k m L r →
      GD (2 ^ 24) (pathW INVM RD RW k m L r - 1) ∧
        X k * val x (pathW INVM RD RW k m L r - 1) * (X k)⁻¹ ∈ H := by
    intro m L hm hS
    rw [pathW_eq2] at hS ⊢
    have hb : 1 + m * 2 ^ 16 ≤ 2 ^ 24 := by
      have : m * 2 ^ 16 ≤ 255 * 2 ^ 16 := Nat.mul_le_mul_right _ (by omega)
      norm_num at this ⊢; omega
    obtain ⟨h1, h2⟩ := path_spec2 hinv hH m L 1 1 Nat.one_pos GD.zero (by omega)
      (by
        change X k * val x 0 * (X k)⁻¹ ∈ H
        rw [val_zero, mul_one, mul_inv_cancel]
        exact H.one_mem)
      hS
    exact ⟨h1.mono hb, h2⟩
  cases fwd
  all_goals
    unfold tStep at hf ⊢
    simp only [sW_eq, brec_eq, ↓reduceIte, Bool.false_eq_true] at hf ⊢
    split_ifs at hf ⊢ with hc
    swap
    · exact absurd hf (by rw [wsBad_fail]; norm_num)
    simp only [kandB_iff] at hc
    obtain ⟨hfr, hfa, hk, hS, hT', h1⟩ := hc
    have hR := hH _ (Nat.blt_eq.mp hfr)
    have hfa' : dKind (RD (hNat J 20)) < 3 := Nat.blt_eq.mp hfa
    have hk' := Nat.eq_of_beq_eq_true hk
    obtain ⟨hSg, hSc⟩ := hpath _ _ hm (Nat.blt_eq.mp hS)
    rw [(wsMk_spec (by first | exact dN1_lt _ | exact dN2_lt _) (by norm_num) _).1]
    subst hk'
  · exact step_core3 PB F INVM BS NB H x hinv hone (ce_flip_t (hR.fact hfa')) hTb hNT hR.ra hR.rw
      hT' (hWord_spec _).1 hSg hSc ha h1
  · exact step_core3 PB F INVM BS NB H x hinv hone (hR.fact hfa') hTf hNT hR.rw hR.ra hT'
      (hWord_spec _).1 hSg hSc ha h1

end Step

section Walk

variable {PB : ℕ} {F RD RW RA WD : ℕ → ℕ} {INVM BS NB NT PSF PSB : ℕ} {H : Subgroup G}
  {x : ℕ → G} {t : G}

theorem posStep_mk (r w pos : ℕ) (back : Bool) (s a : ℕ) :
    posStep PB F INVM BS NB NT PSF PSB RD RW RA r w pos back (s, a) =
      if Nat.beq (wsFail s) 1 = true then wsBad a
      else if Nat.blt (wAt w pos) 12 = true then
        (s, wCat a (wOne (if back = true then ivL INVM (wAt w pos) else wAt w pos)))
      else if Nat.beq (wAt w pos) 14 = true then eStep INVM RD RW r (wsK s) a (wsJ s) back
      else tStep PB F INVM BS NB NT PSF PSB RD RW RA r (wsK s) a (wsJ s)
        (if back = true then Nat.beq (wAt w pos) 13 else Nat.beq (wAt w pos) 12) := by
  simp only [posStep, sW_eq, brec_eq]

theorem posStep_fail (r w pos : ℕ) (back : Bool) {st : WS} (h : wsFail st.1 = 1) :
    wsFail (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w pos back st).1 = 1 := by
  obtain ⟨s, a⟩ := st
  rw [posStep_mk, if_pos (by simpa using h)]
  exact wsBad_fail a

theorem foldl_fail (r w : ℕ) (back : Bool) (ps : List ℕ) : ∀ {st : WS}, wsFail st.1 = 1 →
    wsFail (ps.foldl (fun st p => posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st)
      st).1 = 1 := by
  induction ps with
  | nil => exact fun h => h
  | cons p ps ih => exact fun h => ih (posStep_fail r w p back h)

variable (PB F INVM BS NB NT PSF PSB RD RW RA H x t) in
theorem posStep_spec (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hNT : NT ≤ 12)
    (hTf : ∀ c < NT, thL PSF c < 12 ∧ x c * t = t * x (thL PSF c))
    (hTb : ∀ c < NT, thL PSB c < 12 ∧ x c * t⁻¹ = t⁻¹ * x (thL PSB c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (v : ℕ → G) (hv : ∀ c < 12, v c = x c) (hv12 : v 12 = t) (hv13 : v 13 = t⁻¹)
    (hv14 : v 14 = 1)
    {X : ℕ → G} {r w pos B : ℕ} (back : Bool) (hH : Hist2 RD RW RA H x t X r)
    (hc : wAt w pos < 15) {st : WS}
    (hB1 : 2 ^ 17 ≤ B) (hB2 : B + 2 ^ 16 ≤ 2 ^ 30) (ha : GD B st.2)
    (hf : wsFail (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w pos back st).1 = 0) :
    CE H (X (wsK st.1) * val x st.2 * pval v w back pos)
      (X (wsK (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w pos back st).1) *
        val x (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w pos back st).2) ∧
    GD (B + 2 ^ 16) (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w pos back st).2 := by
  obtain ⟨s, a⟩ := st
  dsimp only at ha ⊢
  rw [posStep_mk] at hf ⊢
  unfold pval
  by_cases h1 : Nat.beq (wsFail s) 1 = true
  · rw [if_pos h1] at hf
    exact absurd hf (by rw [wsBad_fail]; norm_num)
  rw [if_neg h1] at hf ⊢
  by_cases h12 : Nat.blt (wAt w pos) 12 = true
  · rw [if_pos h12] at hf ⊢
    have hc12 : wAt w pos < 12 := Nat.blt_eq.mp h12
    have hd : (if back = true then ivL INVM (wAt w pos) else wAt w pos) < 12 := by
      split_ifs
      · exact (hinv _ hc12).1
      · exact hc12
    obtain ⟨o1, o2, o3⟩ := wOne_spec (c := if back = true then ivL INVM (wAt w pos) else wAt w pos)
      (by omega)
    have hO : GD 2 (wOne (if back = true then ivL INVM (wAt w pos) else wAt w pos)) :=
      ⟨o2, by rw [o3]; simpa using hd, by omega⟩
    obtain ⟨g, e⟩ := ha.cat hO (by omega)
    refine ⟨CE.of_eq ?_, g.mono (by omega)⟩
    dsimp only
    rw [val_cat e, mul_assoc]
    congr 2
    rw [show val x (wOne (if back = true then ivL INVM (wAt w pos) else wAt w pos)) =
        x (if back = true then ivL INVM (wAt w pos) else wAt w pos) by
      rw [val, o3]; simp [evalWord]]
    cases back <;> simp [hv _ hc12, (hinv _ hc12).2]
  · rw [if_neg h12] at hf ⊢
    have hc12 : 12 ≤ wAt w pos := by
      have : ¬ wAt w pos < 12 := fun h => h12 (Nat.blt_eq.mpr h)
      omega
    by_cases h14 : Nat.beq (wAt w pos) 14 = true
    · rw [if_pos h14] at hf ⊢
      obtain ⟨hce, hgd⟩ := eStep_spec RD RW RA INVM H x t hinv back hH ha (by omega) hf
      refine ⟨?_, hgd.mono (by omega)⟩
      rw [Nat.eq_of_beq_eq_true h14, hv14, inv_one, ite_self, mul_one]
      exact hce
    · rw [if_neg h14] at hf ⊢
      have hc14 : wAt w pos ≠ 14 := fun h => h14 (by rw [h]; rfl)
      obtain ⟨hce, hgd⟩ := tStep_spec PB F RD RW RA INVM BS NB NT PSF PSB H x t hinv hNT hTf hTb
        hone _ hH (ha.mono (by omega)) hf
      refine ⟨?_, hgd.mono (by omega)⟩
      convert hce using 2
      obtain hc' | hc' : wAt w pos = 12 ∨ wAt w pos = 13 := by omega
      all_goals rw [hc']
      all_goals cases back
      all_goals simp [hv12, hv13]

variable (PB F INVM BS NB NT PSF PSB RD RW RA H x t) in
theorem walk_list (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hNT : NT ≤ 12)
    (hTf : ∀ c < NT, thL PSF c < 12 ∧ x c * t = t * x (thL PSF c))
    (hTb : ∀ c < NT, thL PSB c < 12 ∧ x c * t⁻¹ = t⁻¹ * x (thL PSB c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (v : ℕ → G) (hv : ∀ c < 12, v c = x c) (hv12 : v 12 = t) (hv13 : v 13 = t⁻¹)
    (hv14 : v 14 = 1)
    {X : ℕ → G} {r w : ℕ} (back : Bool) (hH : Hist2 RD RW RA H x t X r) (ps : List ℕ)
    (hps : ∀ p ∈ ps, wAt w p < 15) :
    ∀ (st : WS) (B : ℕ), 131072 ≤ B → B + 65536 * ps.length ≤ 1073741824 → GD B st.2 →
    wsFail (ps.foldl (fun st p => posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st)
      st).1 = 0 →
    CE H (X (wsK st.1) * val x st.2 * (ps.map (pval v w back)).prod)
      (X (wsK (ps.foldl (fun st p => posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st)
        st).1) *
        val x (ps.foldl (fun st p => posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st)
          st).2) ∧
    GD (B + 65536 * ps.length)
      (ps.foldl (fun st p => posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st) st).2 := by
  induction ps with
  | nil =>
    intro st B _ _ ha _
    exact ⟨CE.of_eq (by simp), by simpa using ha⟩
  | cons p ps ih =>
    intro st B hB1 hB2 ha hf
    simp only [List.foldl_cons, List.length_cons, List.map_cons, List.prod_cons] at hf hB2 ⊢
    have hB4 : B + 65536 + 65536 * ps.length ≤ 1073741824 :=
      le_of_eq_of_le (by ring) hB2
    have hB3 : B + 65536 ≤ 1073741824 := le_trans (Nat.le_add_right _ _) hB4
    have hf1 : wsFail (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st).1 = 0 := by
      have := wsFail_lt (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st).1
      by_contra hne
      have h1 := foldl_fail (PB := PB) (F := F) (INVM := INVM) (BS := BS) (NB := NB) (NT := NT)
        (PSF := PSF) (PSB := PSB) (RD := RD) (RW := RW) (RA := RA) r w back ps
        (st := posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st) (by omega)
      omega
    obtain ⟨c1, g1⟩ := posStep_spec PB F RD RW RA INVM BS NB NT PSF PSB H x t hinv hNT hTf hTb
      hone v hv hv12 hv13 hv14 back hH (hps p List.mem_cons_self) (le_trans (by norm_num) hB1)
      (le_trans (by norm_num) hB3) ha hf1
    obtain ⟨c2, g2⟩ := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _ (B + 65536)
      (Nat.le_add_right_of_le hB1) hB4 (g1.mono (le_of_eq (by norm_num))) hf
    refine ⟨?_, by
      rw [show B + 65536 * (ps.length + 1) = B + 65536 + 65536 * ps.length by ring]; exact g2⟩
    rw [← mul_assoc]
    exact (c1.mul_right _).trans c2

@[expose] noncomputable def wR3 (r w a n : ℕ) (back : Bool) (j : ℕ) : WS → WS :=
  Nat.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun j ih st => Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW x (fun x' =>
        ih (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w
          (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n (nat_lit 1)) j))
            (Nat.sub a (Nat.sub (Nat.sub n (nat_lit 1)) j)) back) back
          (Prod.mk s' x'))))) st)
    j

theorem walkRun_eq (r w a n : ℕ) (back : Bool) (st : WS) :
    walkRun PB F INVM BS NB NT PSF PSB RD RW RA r w a n back st =
      ((List.range' 0 n).map (fun o => if back = true then a - o else a + o)).foldl
        (fun st p => posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st) st := by
  have key : ∀ j, j ≤ n → ∀ st : WS,
      wR3 (PB := PB) (F := F) (INVM := INVM) (BS := BS) (NB := NB) (NT := NT) (PSF := PSF)
        (PSB := PSB) (RD := RD) (RW := RW) (RA := RA) r w a n back j st =
      ((List.range' (n - j) j).map (fun o => if back = true then a - o else a + o)).foldl
        (fun st p => posStep PB F INVM BS NB NT PSF PSB RD RW RA r w p back st) st := by
    intro j
    induction j with
    | zero => intro _ st; rfl
    | succ j ih =>
      intro hj st
      obtain ⟨s, x⟩ := st
      have e : wR3 (PB := PB) (F := F) (INVM := INVM) (BS := BS) (NB := NB) (NT := NT)
          (PSF := PSF) (PSB := PSB) (RD := RD) (RW := RW) (RA := RA) r w a n back (j + 1)
          (s, x) =
          wR3 (PB := PB) (F := F) (INVM := INVM) (BS := BS) (NB := NB) (NT := NT) (PSF := PSF)
          (PSB := PSB) (RD := RD) (RW := RW) (RA := RA) r w a n back j
          (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w
            (if back = true then a - (n - 1 - j) else a + (n - 1 - j)) back (s, x)) := by
        have e0 : wR3 (PB := PB) (F := F) (INVM := INVM) (BS := BS) (NB := NB) (NT := NT)
            (PSF := PSF) (PSB := PSB) (RD := RD) (RW := RW) (RA := RA) r w a n back (j + 1)
            (s, x) = sW s (fun s' => sW x (fun x' =>
              wR3 (PB := PB) (F := F) (INVM := INVM) (BS := BS) (NB := NB) (NT := NT)
                (PSF := PSF) (PSB := PSB) (RD := RD) (RW := RW) (RA := RA) r w a n back j
                (posStep PB F INVM BS NB NT PSF PSB RD RW RA r w
                  (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n 1) j))
                    (Nat.sub a (Nat.sub (Nat.sub n 1) j)) back) back (s', x')))) := rfl
        rw [e0, sW_eq, sW_eq, brec_eq]
        rfl
      rw [e, ih (by omega), show n - (j + 1) = n - 1 - j by omega,
        show n - j = n - 1 - j + 1 by omega, List.range'_succ]
      rfl
  have := key n le_rfl st
  rw [Nat.sub_self] at this
  exact this

theorem walk_core (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r d c : ℕ} {sf sb : WS} {vg : G}
    (hRW : GD (2 ^ 16) (RW r)) (hRA : GD (2 ^ 16) (RA r))
    (gf : GD (2 ^ 29) sf.2) (gb : GD (2 ^ 29) sb.2)
    (key : CE H (X (wsK sf.1) * val x sf.2 * vg) (X (wsK sb.1) * val x sb.2))
    (hv12 : c = 12 → vg = t) (hv13 : c = 13 → vg = t⁻¹) (hv14 : c = 14 → vg = 1)
    (h : Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq c 14) (andB (Nat.beq (dKind d) 3)
        (andB (Nat.beq (wsK sf.1) (dN1 d)) (andB (Nat.beq (wsK sb.1) (dN2 d))
          (isOne PB F BS NB (wCat (wInv INVM (RW r)) (wCat sb.2 (wInv INVM sf.2))))))))
      (andB (Nat.beq (dKind d) 2)
        (Bool.rec (motive := fun _ => Bool)
          (andB (Nat.beq c 13)
            (andB (Nat.beq (wsK sb.1) (dN1 d)) (andB (Nat.beq (wsK sf.1) (dN2 d))
            (andB (isOne PB F BS NB (wCat (wInv INVM (RW r)) sb.2))
              (isOne PB F BS NB (wCat (wInv INVM (RA r)) sf.2))))))
          (andB (Nat.beq (wsK sf.1) (dN1 d)) (andB (Nat.beq (wsK sb.1) (dN2 d))
            (andB (isOne PB F BS NB (wCat (wInv INVM (RW r)) sf.2))
              (isOne PB F BS NB (wCat (wInv INVM (RA r)) sb.2)))))
          (Nat.beq c 12)))
      (Nat.blt c 14) = true) :
    (dKind d = 2 ∧ CE H (X (dN1 d) * val x (RW r) * t) (X (dN2 d) * val x (RA r))) ∨
    (dKind d = 3 ∧ CE H (X (dN1 d)) (X (dN2 d) * val x (RW r))) := by
  rw [brec_eq] at h
  by_cases h14 : Nat.blt c 14 = true
  · rw [if_pos h14, kandB_iff, brec_eq] at h
    obtain ⟨hk2, h⟩ := h
    left
    refine ⟨Nat.eq_of_beq_eq_true hk2, ?_⟩
    by_cases h12 : Nat.beq c 12 = true
    · rw [if_pos h12] at h
      simp only [kandB_iff] at h
      obtain ⟨hkf, hkb, h1f, h1b⟩ := h
      rw [hv12 (Nat.eq_of_beq_eq_true h12)] at key
      rw [← Nat.eq_of_beq_eq_true hkf, ← Nat.eq_of_beq_eq_true hkb,
        val_eq_of_isOne3 hinv hone hRW gf (by norm_num) h1f,
        val_eq_of_isOne3 hinv hone hRA gb (by norm_num) h1b]
      exact key
    · rw [if_neg h12] at h
      simp only [kandB_iff] at h
      obtain ⟨h13, hkb, hkf, h1b, h1f⟩ := h
      rw [hv13 (Nat.eq_of_beq_eq_true h13)] at key
      rw [← Nat.eq_of_beq_eq_true hkb, ← Nat.eq_of_beq_eq_true hkf,
        val_eq_of_isOne3 hinv hone hRW gb (by norm_num) h1b,
        val_eq_of_isOne3 hinv hone hRA gf (by norm_num) h1f]
      exact ce_flip_inv key
  · rw [if_neg h14] at h
    simp only [kandB_iff] at h
    obtain ⟨h14', hk3, hkf, hkb, h1⟩ := h
    right
    refine ⟨Nat.eq_of_beq_eq_true hk3, ?_⟩
    rw [hv14 (Nat.eq_of_beq_eq_true h14'), mul_one] at key
    obtain ⟨gi, ei⟩ := gf.inv hinv
    obtain ⟨g3, e3⟩ := gb.cat gi (by norm_num)
    have hv := val_eq_of_isOne3 hinv hone hRW g3 (by norm_num) h1
    rw [val_cat e3, ei] at hv
    rw [← Nat.eq_of_beq_eq_true hkf, ← Nat.eq_of_beq_eq_true hkb, hv]
    have := key.mul_right (val x sf.2)⁻¹
    rw [mul_inv_cancel_right] at this
    simpa only [mul_assoc] using this

variable (PB F INVM BS NB NT PSF PSB RD RW RA WD H x t) in
theorem walkOK_spec (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hNT : NT ≤ 12)
    (hTf : ∀ c < NT, thL PSF c < 12 ∧ x c * t = t * x (thL PSF c))
    (hTb : ∀ c < NT, thL PSB c < 12 ∧ x c * t⁻¹ = t⁻¹ * x (thL PSB c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (v : ℕ → G) (hv : ∀ c < 12, v c = x c) (hv12 : v 12 = t) (hv13 : v 13 = t⁻¹)
    (hv14 : v 14 = 1)
    (hWD : ∀ i < 4096, wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ lst (WD i), c < 15) ∧
      evalWord v (lst (WD i)) = 1)
    {X : ℕ → G} {r d J : ℕ} (hH : Hist2 RD RW RA H x t X r) (hRW : GD (2 ^ 16) (RW r))
    (hRA : GD (2 ^ 16) (RA r))
    (h : walkOK PB F INVM BS NB NT PSF PSB RD RW RA WD r d J = true) :
    (dKind d = 2 ∧ CE H (X (dN1 d) * val x (RW r) * t) (X (dN2 d) * val x (RA r))) ∨
    (dKind d = 3 ∧ CE H (X (dN1 d)) (X (dN2 d) * val x (RW r))) := by
  unfold walkOK at h
  simp only [sB_eq, prod_rec_eq, walkRun_eq, kandB_iff] at h
  obtain ⟨hh0, hg, hff, hfb, -, h⟩ := h
  obtain ⟨hL, hlt, hwv⟩ := hWD _ (land4095_lt J)
  generalize WD (Nat.land J 4095) = w at hL hlt hwv hg hff hfb h
  generalize Nat.land (hAfterWord (hDrop J 24)) 255 = g at hg hff hfb h
  have hgL : g < wLen w := Nat.blt_eq.mp hg
  replace hff := Nat.eq_of_beq_eq_true hff
  replace hfb := Nat.eq_of_beq_eq_true hfb
  have hi : fld J 12 4095 < 4096 := fld_lt_succ _ _ _
  have hat : ∀ p < wLen w, wAt w p < 15 := fun p hp =>
    hlt _ (List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩)
  have h0 : GD 131072 (hWord (hDrop J 24)) :=
    ⟨(wBelow_spec hh0).1, (wBelow_spec hh0).2, lt_trans (hWord_spec _).1 (by norm_num)⟩
  have hL' : wLen w < 4096 := by simpa using hL
  obtain ⟨c1, g1⟩ := walk_list PB F RD RW RA INVM BS NB NT PSF PSB H x t hinv hNT hTf hTb hone v
    hv hv12 hv13 hv14 false hH _ (by
      intro p hp
      simp only [List.mem_map, List.mem_range'_1] at hp
      obtain ⟨o, ho, rfl⟩ := hp
      exact hat _ (by simp only [Nat.sub_eq, Bool.false_eq_true, ↓reduceIte] at ho ⊢; omega))
    _ 131072 le_rfl (by simp only [List.length_map, List.length_range']; omega) h0 hff
  obtain ⟨c2, g2⟩ := walk_list PB F RD RW RA INVM BS NB NT PSF PSB H x t hinv hNT hTf hTb hone v
    hv hv12 hv13 hv14 true hH _ (by
      intro p hp
      simp only [List.mem_map, List.mem_range'_1] at hp
      obtain ⟨o, ho, rfl⟩ := hp
      exact hat _ (by simp only [Nat.sub_eq, ↓reduceIte] at ho ⊢; omega))
    _ 131072 le_rfl (by simp only [List.length_map, List.length_range', Nat.sub_eq]; omega) h0 hfb
  have h1 : ((List.range (wLen w)).map (pval v w false)).prod = 1 := by
    rw [← hwv]
    unfold evalWord lst
    rw [List.map_map]
    congr 1
  have key := walk_finish c1 c2 ((wsK_wsMk hi _).trans (wsK_wsMk hi _).symm) rfl
    (fun p => by simp [pval]) hgL rfl rfl h1
  exact walk_core hinv hone hRW hRA
    (g1.mono (by simp only [List.length_map, List.length_range']; omega))
    (g2.mono (by simp only [List.length_map, List.length_range', Nat.sub_eq]; omega)) key
    (fun e => by simp [pval, e, hv12]) (fun e => by simp [pval, e, hv13])
    (fun e => by simp [pval, e, hv14]) h

end Walk

end CFSG.Certificates.TwDce3.Walk

end
