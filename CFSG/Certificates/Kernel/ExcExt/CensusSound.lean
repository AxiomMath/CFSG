module

public import Certificates.Data.CFSGNative.ExcCensus.Check
public import Certificates.Data.Kernel.ExcExt.CensusTwin
public import CFSG.Certificates.Kernel.ExcExt.Sound

public section

noncomputable section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def pickC (d cv : Nat) : Nat → List KCPlane → Nat → Option KCPlane
  | 0, _, _ => none
  | n + 1, ps, cy =>
    if Chk.canonN d cv n then
      match ps with
      | [] => none
      | P :: tl => if cy = n then some P else pickC d cv n tl cy
    else pickC d cv n ps cy

@[expose] def decRows (rows : KL) : List Nat := (List.range rows.len).map (ln7 rows.P)

@[expose] def decTwoNode : KCW → Option (Nat × Nat × List Nat × Array (Array Int) × Nat)
  | .twoNode a b rows B φ _ => some (a, b, decRows rows, decMat B, φ)
  | _ => none

@[expose] def decCommon : KCW → Option (Nat × Nat × List Nat × Array (Array Int) × Chk.CommonW)
  | .common a b rows B _ w Ll Lk Bl Bk =>
    some (a, b, decRows rows, decMat B,
      { w := decLin w, Lℓ := decDer Ll, Lk := decDer Lk, Bℓ := decMat Bl, Bk := decMat Bk })
  | _ => none

@[expose] def decAmb : KCA → Option (Chk.AmbW × Array (Array Int) × Array (Array Int))
  | .amb w Lk La Bk Bb B B' =>
    some ({ w := decLin w, Lk := decDer Lk, La := decDer La, Bk := decMat Bk, Bb := decMat Bb },
      decMat B, decMat B')
  | _ => none

@[expose] def candAt (d cv cy cz : Nat) (ws : List KCA) : Option KCA :=
  ((List.range 6).find? fun i => Chk.combN d cv cy (i / 2) (i % 2 + 1) == cz).bind fun i => ws[i]?

@[expose] def csearchOf (m : Fin 6) (L : KCLine) : Chk.CSearch where
  S :=
    { line := fun cv => if cv = L.cv then decRefL L.ref else none
      plane := fun cv cy => (pickC (dim m) cv (3 ^ dim m) L.planes cy).bind fun P => decRefP P.ref
      cand := fun _ cz => decRefC (ln128 L.cref cz) }
  twoNode cv cy := (pickC (dim m) cv (3 ^ dim m) L.planes cy).bind fun P => decTwoNode P.body
  common cv cy := (pickC (dim m) cv (3 ^ dim m) L.planes cy).bind fun P => decCommon P.body
  amb cv cz := L.planes.findSome? fun P =>
    match P.body with
    | .cands ws => (candAt (dim m) cv P.cy cz ws).bind decAmb
    | _ => none

@[expose] def CensusLineOK (m : Fin 6) (K : KT) (L : KCLine) : Prop :=
  Chk.scanLineN (tabsK m K) m true false (csearchOf m L).S (Chk.bodyCC (tabsK m K) m (csearchOf m L))
    L.cv = true

theorem cen_and {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem cen_orL {a b : Bool} (h : a = true) : (a || b) = true := by
  rw [h]
  rfl

theorem cen_orR {a b : Bool} (h : b = true) : (a || b) = true := by
  rw [h, Bool.or_true]

theorem cen_abK {a b : Nat} (h : abK a b = true) : (decide (a < 3) && (b == 1 || b == 2)) = true := by
  simp only [abK, band_eq_true, bor_iff, Nat.blt_eq, Nat.beq_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  exact h

theorem cen_lowRec {r c : Nat} : ∀ {n : Nat}, n ≤ r →
    (Nat.rec (motive := fun _ => Nat) r
      (fun t acc => nif (Nat.blt acc r) acc (nif (bit c t) t r)) n : Nat) =
      ((List.range n).find? fun t => c.testBit t).getD r
  | 0, _ => rfl
  | n + 1, h => by
    have ih := cen_lowRec (r := r) (c := c) (n := n) (by omega)
    have e : (Nat.rec (motive := fun _ => Nat) r
        (fun t acc => nif (Nat.blt acc r) acc (nif (bit c t) t r)) (n + 1) : Nat) =
        nif (Nat.blt (Nat.rec (motive := fun _ => Nat) r
          (fun t acc => nif (Nat.blt acc r) acc (nif (bit c t) t r)) n) r)
          (Nat.rec (motive := fun _ => Nat) r
            (fun t acc => nif (Nat.blt acc r) acc (nif (bit c t) t r)) n)
          (nif (bit c n) n r) := rfl
    rw [e, ih, List.range_succ, List.find?_append]
    cases hf : (List.range n).find? (fun t => c.testBit t) with
    | some k =>
      have hk : k < n := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have hkr : k < r := by omega
      simp [nif_eq, nblt_eq, hkr]
    | none =>
      have hrr : ¬ r < r := Nat.lt_irrefl r
      cases hb : c.testBit n <;> simp [nif_eq, nblt_eq, hrr, bit_eq, hb]

theorem cen_lowK (r c : Nat) : lowK r c = Chk.lowN r c := by
  unfold lowK Chk.lowN
  exact cen_lowRec (Nat.le_refl _)

theorem cen_growK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c S : Nat) : growK K c S = Chk.growN (tabsK m K) (nroots m) c S := by
  have key : ∀ n ≤ nroots m, (Nat.rec (motive := fun _ => Nat) S
      (fun t acc => nif (bit S t) (Nat.lor acc (Nat.land (adjK K t) c)) acc) n : Nat) =
      Nat.fold n (fun t _ acc => if S.testBit t then acc ||| ((tabsK m K).adj[t]! &&& c) else acc)
        S := by
    intro n hn
    induction n with
    | zero =>
      rw [Nat.fold_zero]
      rfl
    | succ n ih =>
      have e : (Nat.rec (motive := fun _ => Nat) S
          (fun t acc => nif (bit S t) (Nat.lor acc (Nat.land (adjK K t) c)) acc) (n + 1) : Nat) =
          nif (bit S n) (Nat.lor (Nat.rec (motive := fun _ => Nat) S
            (fun t acc => nif (bit S t) (Nat.lor acc (Nat.land (adjK K t) c)) acc) n)
            (Nat.land (adjK K n) c)) (Nat.rec (motive := fun _ => Nat) S
            (fun t acc => nif (bit S t) (Nat.lor acc (Nat.land (adjK K t) c)) acc) n) := rfl
      rw [e, Nat.fold_succ, ih (by omega), nif_eq, bit_eq, adjK_eq hT (by omega)]
      rfl
  unfold growK Chk.growN
  rw [hT.hr]
  exact key _ (Nat.le_refl _)

theorem cen_growNK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c S n : Nat) : growNK K c S n = Nat.repeat (Chk.growN (tabsK m K) (nroots m) c) n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : growNK K c S (n + 1) = growK K c (growNK K c S n) := rfl
    rw [e, ih, cen_growK hT]
    rfl

theorem cen_grow_fix (T : Chk.Tabs) (r c : Nat) : Chk.growN T r c c = c := by
  unfold Chk.growN
  induction r with
  | zero => rw [Nat.fold_zero]
  | succ n ih =>
    rw [Nat.fold_succ, ih]
    split
    · apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_or, Nat.testBit_and]
      cases c.testBit i <;> simp
    · rfl

theorem cen_repeat_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    Nat.repeat f (a + b) x = Nat.repeat f a (Nat.repeat f b x) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.succ_add]
    change f (Nat.repeat f (a + b) x) = f (Nat.repeat f a (Nat.repeat f b x))
    rw [ih]

theorem cen_repeat_fix {α : Type} {f : α → α} {x : α} (h : f x = x) (a : Nat) :
    Nat.repeat f a x = x := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change f (Nat.repeat f a x) = x
    rw [ih, h]

theorem cen_connK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {c n : Nat} (h : connK K c n = true) : Chk.connN (tabsK m K) (nroots m) c = true := by
  simp only [connK, band_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [hT.hr, truncK_eq, cen_lowK, Nat.blt_eq] at h1
  rw [hT.hr, Nat.ble_eq] at h2
  rw [hT.hr, truncK_eq, cen_lowK, Nat.beq_eq, cen_growNK hT] at h3
  unfold Chk.connN
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨h1, ?_⟩
  have e : ∀ S, Nat.repeat (Chk.growN (tabsK m K) (nroots m) (Chk.trunc (nroots m) c)) (nroots m) S =
      Nat.repeat (Chk.growN (tabsK m K) (nroots m) (Chk.trunc (nroots m) c)) (nroots m - n)
        (Nat.repeat (Chk.growN (tabsK m K) (nroots m) (Chk.trunc (nroots m) c)) n S) := by
    intro S
    rw [← cen_repeat_add, Nat.sub_add_cancel h2]
  rw [e]
  have h3' : Nat.repeat (Chk.growN (tabsK m K) (nroots m) (Chk.trunc (nroots m) c)) n
      (1 <<< Chk.lowN (nroots m) (Chk.trunc (nroots m) c)) = Chk.trunc (nroots m) c := h3
  rw [h3']
  exact cen_repeat_fix (cen_grow_fix _ _ _) _

theorem cen_outK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {c φ cv : Nat} (h : outK K c φ cv = true) :
    Chk.outOK (tabsK m K) (dim m) (nroots m) c φ cv = true := by
  simp only [outK, band_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold Chk.outOK
  refine cen_and ?_ ?_
  · rw [nat_all_iff]
    intro t ht
    have := allN_iff.mp h1 t (by rw [hT.hr]; exact ht)
    rw [bor_iff, bnot_eq, bit_eq] at this
    rcases this with h | h
    · exact cen_orL h
    · refine cen_orR ?_
      rw [beq_iff_eq]
      rw [hT.hd] at h
      refine wk_fin0 ?_ h
      intro k hk
      rw [tabsK_h ht hk]
      exact dvd_term' (hK_dvd hT ht hk)
  · rw [hT.hd] at h2
    have key : ((sumN (dim m) fun k => Nat.mul (digK φ k) (digK cv k) : Nat) : Int) =
        Nat.fold (dim m) (fun k _ s => s + (Chk.dig φ k : Int) * (Chk.dig cv k : Int)) 0 := by
      rw [sumN_cast]
      apply fold_congr
      intro k _
      exact Int.natCast_mul _ _
    rw [← key]
    generalize (sumN (dim m) fun k => Nat.mul (digK φ k) (digK cv k)) = S at h2 ⊢
    rw [bnot_eq, nbeq_eq] at h2
    simp only [xk_mod, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h2
    simp only [bne_iff_ne, ne_eq]
    omega

theorem cen_candK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cz : Nat} {rows : KL} {B n : Nat} (h : candK K cv cz rows B n = true) :
    Chk.candOK (tabsK m K) m cv cz (decRows rows) (decMat B) = true := by
  simp only [candK, band_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold Chk.candOK
  refine cen_and (cen_and (cen_and (cen_and (cen_and ?_ ?_) ?_) ?_) ?_) ?_
  · rw [Nat.blt_eq, hT.hd, xk_pow] at h1
    exact decide_eq_true h1
  · rw [← zmK_eq hT]
    exact cen_connK_sound hT h2
  · have hl := wk_line hT h3
    have e : (List.range rows.len).map (fun i => nodeK (rowsW rows) (idK i)) = decRows rows := by
      unfold decRows
      apply List.map_congr_left
      intro i hi
      exact wk_nodeK_lt (List.mem_range.mp hi)
    rw [e] at hl
    exact hl
  · rw [← zmK_eq hT, ← lam2K_labK hT]
    exact h4
  · rw [bnot_eq, subK_eq, truncK_eq, hT.hr, zmK_eq hT, zmK_eq hT] at h5
    exact h5
  · rw [← zmK_eq hT, ← wk_notB2 hT]
    exact h6

theorem cen_cand_common {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cy a b : Nat} {rows : KL} {B n : Nat} {w : KLin} {Ll Lk : KL} {Bl Bk : Nat}
    (h : band (abK a b) (band (candK K cv (combK K.d cv cy a b) rows B n)
      (commonK K cv (combK K.d cv cy a b) (zmK K cv) (zmK K (combK K.d cv cy a b)) w Ll Lk Bl
        Bk)) = true) :
    (decide (a < 3) && (b == 1 || b == 2) &&
      Chk.candOK (tabsK m K) m cv (Chk.combN (dim m) cv cy a b) (decRows rows) (decMat B) &&
      Chk.commonOK (tabsK m K) m cv (Chk.combN (dim m) cv cy a b) ((tabsK m K).zm[cv]!)
        ((tabsK m K).zm[Chk.combN (dim m) cv cy a b]!)
        { w := decLin w, Lℓ := decDer Ll, Lk := decDer Lk, Bℓ := decMat Bl, Bk := decMat Bk }) =
      true := by
  simp only [band_eq_true] at h
  obtain ⟨hab, hc, hm⟩ := h
  simp only [hT.hd, combK_eq] at hc hm
  have hm' := wk_common hT hm
  simp only [zmK_eq hT] at hm'
  exact cen_and (cen_and (cen_abK hab) (cen_candK_sound hT hc)) hm'

theorem cen_offK (a : Nat) : offK a = Chk.offN a := by
  funext p
  simp only [offK, Chk.offN, nif_eq, nblt_eq, decide_eq_true_eq]

theorem cen_invP {tc n k : Nat} {pos : Nat → Nat} {B : Nat} (hk : k ≤ 8)
    (h : invCK tc n k pos B = true) :
    Chk.invOK k (fun p q => Chk.cartanN tc n (pos p) (pos q)) (decMat B) = true := by
  unfold Chk.invOK
  rw [nat_all_iff]
  intro i hi
  rw [nat_all_iff]
  intro j hj
  have hij := allN_iff.mp (allN_iff.mp h i hi) j hj
  rw [beq_iff_eq]
  refine wk_fin ?_ (wk_ndel i j) hij
  intro l hl
  dsimp only
  rw [wk_decMat (by omega) (by omega)]
  apply dvd_term'
  have := wk_cart tc n (pos l) (pos j)
  omega

theorem cen_ambientK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {cv cz : Nat} {w : KLin} {Lk La : KL} {Bk Bb B B' : Nat}
    (h : ambientK K cv cz (zmK K cv) (zmK K cz) w Lk La Bk Bb B B' = true) :
    Chk.ambientOK (tabsK m K) m cv cz ((tabsK m K).zm[cv]!) ((tabsK m K).zm[cz]!)
      { w := decLin w, Lk := decDer Lk, La := decDer La, Bk := decMat Bk, Bb := decMat Bb }
      (decMat B) (decMat B') = true := by
  simp only [ambientK, band_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h8 : rkW w ≤ 8 := by
    simp only [ambK, band_eq_true] at h1
    exact (wk_lin hT h1.1).2.1
  have ha := wk_amb hT h1
  simp only [zmK_eq hT] at ha
  have hi1 := wk_inv h8 h2
  have hi2 := cen_invP (by omega : rkW w - 1 ≤ 8) h3
  rw [cen_offK] at hi2
  rw [wk_rkW] at hi1
  rw [wk_rkW] at hi2
  unfold Chk.ambientOK Chk.detOK
  exact cen_and ha (cen_and hi1 hi2)

theorem cen_refLCK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {cv : Nat} {e : KRefL} (h : refLCK K cv e = true) :
    ∃ e', decRefL e = some e' ∧ Chk.refLOK (tabsK m K) m true false cv e' = true := by
  cases e with
  | none => exact Bool.noConfusion h
  | q2 => exact Bool.noConfusion h
  | zero =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .zero) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | disc S =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .disc S) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | cent w =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .cent w) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | label =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .label) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | ins c =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .ins c) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩

theorem cen_pickC_succ (d cv n : Nat) (ps : List KCPlane) (cy : Nat) :
    pickC d cv (n + 1) ps cy = if Chk.canonN d cv n then
      (match ps with
        | [] => none
        | P :: tl => if cy = n then some P else pickC d cv n tl cy)
    else pickC d cv n ps cy := rfl

theorem cen_pickC_mem {d cv cy : Nat} {P : KCPlane} :
    ∀ {n : Nat} {ps : List KCPlane}, pickC d cv n ps cy = some P → P ∈ ps
  | 0, _, h => by simp [pickC] at h
  | n + 1, ps, h => by
    rw [cen_pickC_succ] at h
    split at h
    · cases ps with
      | nil => simp at h
      | cons Q tl =>
        dsimp only at h
        split at h
        · rw [Option.some.injEq] at h
          subst h
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (cen_pickC_mem h)
    · exact cen_pickC_mem h

theorem cen_walk_sound {d cv : Nat} {pl : KCPlane → Bool} {W : Nat → List KCPlane → Bool}
    (hW : ∀ n ps, W (n + 1) ps = Bool.rec (motive := fun _ => Bool) (W n ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy n) (band (pl P) (W n tl))) ps) (canonK d cv n)) :
    ∀ {n : Nat} {ps : List KCPlane}, W n ps = true → ∀ cy < n, Chk.canonN d cv cy = true →
      ∃ P, pickC d cv n ps cy = some P ∧ P.cy = cy ∧ pl P = true := by
  intro n
  induction n with
  | zero =>
    intro ps _ cy hcy
    exact absurd hcy (Nat.not_lt_zero cy)
  | succ n ih =>
    intro ps hw cy hcy hc
    rw [hW, canonK_eq] at hw
    rw [cen_pickC_succ]
    cases hcn : Chk.canonN d cv n
    · rw [hcn] at hw
      have hne : cy ≠ n := by
        rintro rfl
        rw [hc] at hcn
        exact Bool.noConfusion hcn
      rw [if_neg (by simp)]
      exact ih hw cy (by omega) hc
    · rw [hcn] at hw
      rw [if_pos rfl]
      cases ps with
      | nil => exact Bool.noConfusion hw
      | cons P tl =>
        have hw' : band (Nat.beq P.cy n) (band (pl P) (W n tl)) = true := hw
        simp only [band_eq_true, Nat.beq_eq] at hw'
        obtain ⟨h1, h2, h3⟩ := hw'
        by_cases hcn' : cy = n
        · subst hcn'
          exact ⟨P, by simp, h1, h2⟩
        · obtain ⟨Q, hQ, hQ1, hQ2⟩ := ih h3 cy (by omega) hc
          exact ⟨Q, by simp [hcn', hQ], hQ1, hQ2⟩

theorem cen_walk_all {d cv : Nat} {pl : KCPlane → Bool} {W : Nat → List KCPlane → Bool}
    (hW0 : ∀ ps, W 0 ps = List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ps)
    (hW : ∀ n ps, W (n + 1) ps = Bool.rec (motive := fun _ => Bool) (W n ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy n) (band (pl P) (W n tl))) ps) (canonK d cv n)) :
    ∀ {n : Nat} {ps : List KCPlane}, W n ps = true → ∀ P ∈ ps, pl P = true := by
  intro n
  induction n with
  | zero =>
    intro ps hw P hP
    rw [hW0] at hw
    cases ps with
    | nil => simp at hP
    | cons Q tl => exact Bool.noConfusion hw
  | succ n ih =>
    intro ps hw P hP
    rw [hW] at hw
    cases hcn : canonK d cv n
    · rw [hcn] at hw
      exact ih hw P hP
    · rw [hcn] at hw
      cases ps with
      | nil => simp at hP
      | cons Q tl =>
        have hw' : band (Nat.beq Q.cy n) (band (pl Q) (W n tl)) = true := hw
        simp only [band_eq_true] at hw'
        rcases List.mem_cons.mp hP with rfl | hP
        · exact hw'.2.1
        · exact ih hw'.2.2 P hP

theorem cen_ccands_sound {K : KT} {cv cy cref : Nat} :
    ∀ {ws : List KCA} {i : Nat}, ccandsK K cv cy cref ws i = true →
      ∀ j, i ≤ j → j < 6 →
        bor (refCK K cv (combK K.d cv cy (j / 2) (j % 2 + 1))
            (ln128 cref (combK K.d cv cy (j / 2) (j % 2 + 1))))
          (caK K cv cy (combK K.d cv cy (j / 2) (j % 2 + 1)) (ws.getD (j - i) .ref)) = true := by
  intro ws
  induction ws with
  | nil =>
    intro i h j hij hj
    have h' : Nat.beq i 6 = true := h
    rw [Nat.beq_eq] at h'
    omega
  | cons X tl ih =>
    intro i h j hij hj
    have h' : band (bor (refCK K cv (combK K.d cv cy (i / 2) (i % 2 + 1))
          (ln128 cref (combK K.d cv cy (i / 2) (i % 2 + 1))))
        (caK K cv cy (combK K.d cv cy (i / 2) (i % 2 + 1)) X))
        (ccandsK K cv cy cref tl (i + 1)) = true := h
    rw [band_eq_true] at h'
    by_cases hji : j = i
    · subst hji
      rw [Nat.sub_self]
      exact h'.1
    · have := ih h'.2 j (by omega) hj
      have e : j - i = (j - (i + 1)) + 1 := by omega
      rw [e]
      exact this

theorem cen_ccands_len {K : KT} {cv cy cref : Nat} :
    ∀ {ws : List KCA} {i : Nat}, ccandsK K cv cy cref ws i = true → ws.length + i = 6 := by
  intro ws
  induction ws with
  | nil =>
    intro i h
    have h' : Nat.beq i 6 = true := h
    rw [Nat.beq_eq] at h'
    simp [h']
  | cons X tl ih =>
    intro i h
    have h' : band (bor (refCK K cv (combK K.d cv cy (i / 2) (i % 2 + 1))
          (ln128 cref (combK K.d cv cy (i / 2) (i % 2 + 1))))
        (caK K cv cy (combK K.d cv cy (i / 2) (i % 2 + 1)) X))
        (ccandsK K cv cy cref tl (i + 1)) = true := h
    rw [band_eq_true] at h'
    have := ih h'.2
    rw [List.length_cons]
    omega

theorem cen_amb_found {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {L : KCLine} (hall : ∀ P ∈ L.planes, cplaneK K L.cv L.cref P = true) {cz : Nat}
    {v : Chk.AmbW × Array (Array Int) × Array (Array Int)}
    (hv : (csearchOf m L).amb L.cv cz = some v) :
    (∃ e, decRefC (ln128 L.cref cz) = some e ∧ Chk.refCOK (tabsK m K) m L.cv cz e = true) ∨
      Chk.ambientOK (tabsK m K) m L.cv cz ((tabsK m K).zm[L.cv]!) ((tabsK m K).zm[cz]!) v.1 v.2.1
        v.2.2 = true := by
  simp only [csearchOf] at hv
  obtain ⟨P, hmem, hf⟩ := List.exists_of_findSome?_eq_some hv
  have hpl : bor (band (notCandsK P.body) (refPK K L.cv P.cy P.ref))
      (cbodyK K L.cv P.cy L.cref P.body) = true := hall P hmem
  cases hb : P.body with
  | cands ws =>
    rw [hb] at hpl
    simp only [hb] at hf
    have hc : ccandsK K L.cv P.cy L.cref ws 0 = true := by
      rcases bor_iff.mp hpl with h | h
      · exact Bool.noConfusion h
      · exact h
    cases hca : candAt (dim m) L.cv P.cy cz ws with
    | none => simp [hca] at hf
    | some X =>
      simp only [hca, Option.bind_some] at hf
      unfold candAt at hca
      cases hfi : (List.range 6).find?
          (fun i => Chk.combN (dim m) L.cv P.cy (i / 2) (i % 2 + 1) == cz) with
      | none => simp [hfi] at hca
      | some i =>
        simp only [hfi, Option.bind_some] at hca
        have hi6 : i < 6 := List.mem_range.mp (List.mem_of_find?_eq_some hfi)
        have hic : Chk.combN (dim m) L.cv P.cy (i / 2) (i % 2 + 1) = cz := by
          have := List.find?_some hfi
          exact beq_iff_eq.mp this
        have hgetD : ws.getD i .ref = X := by
          rw [List.getD_eq_getElem?_getD, hca]
          rfl
        have hj := cen_ccands_sound hc i (Nat.zero_le _) hi6
        rw [Nat.sub_zero, hgetD, bor_iff, hT.hd, combK_eq, hic] at hj
        rcases hj with hr | ha
        · exact Or.inl (refCK_sound hT hr)
        · right
          cases X with
          | ref => exact Bool.noConfusion ha
          | two => simp [decAmb] at hf
          | amb w Lk La Bk Bb B B' =>
            simp only [decAmb, Option.some.injEq] at hf
            subst hf
            exact cen_ambientK_sound hT ha
  | twoL => simp [hb] at hf
  | twoNode _ _ _ _ _ _ => simp [hb] at hf
  | common _ _ _ _ _ _ _ _ _ _ => simp [hb] at hf

theorem cen_cbody_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {L : KCLine} (hall : ∀ P ∈ L.planes, cplaneK K L.cv L.cref P = true) {cy : Nat} {P : KCPlane}
    (hP : pickC (dim m) L.cv (3 ^ dim m) L.planes cy = some P) (hPcy : P.cy = cy)
    (h : cbodyK K L.cv cy L.cref P.body = true) :
    Chk.bodyCC (tabsK m K) m (csearchOf m L) L.cv cy = true := by
  dsimp only [Chk.bodyCC]
  cases hb : P.body with
  | twoL =>
    rw [hb] at h
    have h' : twoNodeK (labK K (zmK K L.cv)) (labK K (Nat.land (zmK K L.cv) (zmK K cy))) = true :=
      h
    rw [twoNodeK_labK hT] at h'
    simp only [zmK_eq hT, xk_land] at h'
    exact cen_orL (cen_orL (cen_orL h'))
  | twoNode a b rows B φ n =>
    rw [hb] at h
    have h' : band (abK a b) (band (candK K L.cv (combK K.d L.cv cy a b) rows B n)
        (band (outK K (zmK K (combK K.d L.cv cy a b)) φ (combK K.d L.cv cy a b))
          (twoNodeK (labK K (zmK K (combK K.d L.cv cy a b)))
            (labK K (Nat.land (zmK K L.cv) (zmK K cy)))))) = true := h
    simp only [band_eq_true] at h'
    obtain ⟨hab, hc, ho, ht⟩ := h'
    simp only [hT.hd, combK_eq] at hc ho ht
    rw [twoNodeK_labK hT] at ht
    simp only [zmK_eq hT, xk_land] at ho ht
    have e : (csearchOf m L).twoNode L.cv cy = some (a, b, decRows rows, decMat B, φ) := by
      simp only [csearchOf, hP, Option.bind_some, hb, decTwoNode]
    refine cen_orL (cen_orL (cen_orR ?_))
    simp only [e]
    exact cen_and (cen_and (cen_and (cen_abK hab) (cen_candK_sound hT hc))
      (cen_outK_sound hT ho)) ht
  | common a b rows B n w Ll Lk Bl Bk =>
    rw [hb] at h
    have e : (csearchOf m L).common L.cv cy = some (a, b, decRows rows, decMat B,
        { w := decLin w, Lℓ := decDer Ll, Lk := decDer Lk, Bℓ := decMat Bl, Bk := decMat Bk }) := by
      simp only [csearchOf, hP, Option.bind_some, hb, decCommon]
    refine cen_orL (cen_orR ?_)
    simp only [e]
    exact cen_cand_common hT h
  | cands ws =>
    rw [hb] at h
    have hc : ccandsK K L.cv cy L.cref ws 0 = true := h
    have hlen : ws.length = 6 := by
      have := cen_ccands_len hc
      omega
    refine cen_orR ?_
    rw [Chk.candScanN, nat_all_iff]
    intro a ha
    rw [nat_all_iff]
    intro b' hb'
    generalize hcz : Chk.combN (dim m) L.cv cy a (b' + 1) = cz
    obtain ⟨i, hfi⟩ : ∃ i, (List.range 6).find?
        (fun i => Chk.combN (dim m) L.cv cy (i / 2) (i % 2 + 1) == cz) = some i := by
      cases hf : (List.range 6).find?
          (fun i => Chk.combN (dim m) L.cv cy (i / 2) (i % 2 + 1) == cz) with
      | some i => exact ⟨i, rfl⟩
      | none =>
        rw [List.find?_eq_none] at hf
        have e1 : (2 * a + b') / 2 = a := by omega
        have e2 : (2 * a + b') % 2 = b' := by omega
        have := hf (2 * a + b') (List.mem_range.mpr (by omega))
        rw [e1, e2, hcz] at this
        simp at this
    have hi6 : i < 6 := List.mem_range.mp (List.mem_of_find?_eq_some hfi)
    have hic : Chk.combN (dim m) L.cv cy (i / 2) (i % 2 + 1) = cz := by
      have := List.find?_some hfi
      exact beq_iff_eq.mp this
    have hj := cen_ccands_sound hc i (Nat.zero_le _) hi6
    rw [Nat.sub_zero, bor_iff, hT.hd, combK_eq, hic] at hj
    rcases hj with hr | ha
    · obtain ⟨e, he, hok⟩ := refCK_sound hT hr
      refine cen_orL ?_
      simp only [csearchOf, he]
      exact hok
    · cases hX : ws.getD i .ref with
      | ref =>
        rw [hX] at ha
        exact Bool.noConfusion ha
      | two =>
        rw [hX] at ha
        have h2 : twoNodeK (labK K (zmK K cz)) (labK K (Nat.land (zmK K L.cv) (zmK K cy))) =
            true := ha
        rw [twoNodeK_labK hT] at h2
        simp only [zmK_eq hT, xk_land] at h2
        exact cen_orR (cen_orL h2)
      | amb w Lk La Bk Bb B B' =>
        cases hv : (csearchOf m L).amb L.cv cz with
        | none =>
          exfalso
          simp only [csearchOf] at hv
          rw [List.findSome?_eq_none_iff] at hv
          have hP0 := hv P (cen_pickC_mem hP)
          have hws : ws[i]? = some (KCA.amb w Lk La Bk Bb B B') := by
            rw [← hX, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            rfl
          simp [hb, hPcy, candAt, hfi, hws, decAmb] at hP0
        | some v =>
          rcases v with ⟨W, B1, B2⟩
          rcases cen_amb_found hT hall hv with ⟨e, he, hok⟩ | hok
          · refine cen_orL ?_
            simp only [csearchOf, he]
            exact hok
          · refine cen_orR (cen_orR ?_)
            simp only [hv]
            exact hok

theorem scanLineCK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {L : KCLine} (hL : scanLineCK K L = true) :
    CensusLineOK m K L := by
  have hd := hT.hd
  unfold CensusLineOK
  have hL' : bor (refLCK K L.cv L.ref) (cwalkK K L.cv L.cref (Nat.pow 3 K.d) L.planes) = true :=
    hL
  rw [bor_iff] at hL'
  rw [Chk.scanLineN, Bool.or_eq_true]
  rcases hL' with hL' | hL'
  · left
    obtain ⟨e, he, hok⟩ := cen_refLCK_sound hT hL'
    simp only [csearchOf, if_pos rfl, he]
    exact hok
  · right
    have hW : ∀ n ps, cwalkK K L.cv L.cref (n + 1) ps = Bool.rec (motive := fun _ => Bool)
        (cwalkK K L.cv L.cref n ps) (List.rec (motive := fun _ => Bool) false
          (fun P tl _ => band (Nat.beq P.cy n) (band (cplaneK K L.cv L.cref P)
            (cwalkK K L.cv L.cref n tl))) ps) (canonK (dim m) L.cv n) := by
      intro n ps
      rw [← hd]
      rfl
    rw [hd] at hL'
    have hall := cen_walk_all (fun _ => rfl) hW hL'
    rw [nat_all_iff]
    intro cy hcy
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases hc : Chk.canonN (dim m) L.cv cy = true
    · obtain ⟨P, hP, hPcy, hpl⟩ := cen_walk_sound hW hL' cy hcy hc
      have hP' : pickC (dim m) L.cv (3 ^ dim m) L.planes cy = some P := hP
      have hpl' : bor (band (notCandsK P.body) (refPK K L.cv P.cy P.ref))
          (cbodyK K L.cv P.cy L.cref P.body) = true := hpl
      rw [bor_iff, hPcy] at hpl'
      rcases hpl' with hr | hr
      · left
        right
        rw [band_eq_true] at hr
        obtain ⟨e, he, hok⟩ := refPK_sound hT hr.2
        simp only [csearchOf, hP', Option.bind_some, he]
        exact hok
      · right
        exact cen_cbody_sound hT hall hP' hPcy hr
    · left
      left
      simp [hc]

end CFSG.ExcExtK

end

end
