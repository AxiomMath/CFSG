module

public import Certificates.Data.Kernel.EvenSporM22.I22FourDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Four

import CFSG.Certificates.Kernel.Spor.RelTR
import CFSG.Certificates.Kernel.Enum.ZCSound
import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.Kernel.LocalQTCovParse
import CFSG.Certificates.Kernel.LocalQTCovEqns
public import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import CFSG.Certificates.Kernel.Spor.DecLinesRead

namespace CFSG.KC.I22F.Pf

open CFSG.KC.DecText CFSG.KS.DecLines CFSG.KS.SporSch.LyTxt

theorem dDigits_cons (ch : Char) (cs : List Char) :
    digitsOK (ch :: cs) = ((Nat.beq ch.toNat 32 || (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57)) &&
      digitsOK cs) := rfl

theorem dRun_nil (cur : Nat) (st : Bool) : natsRun [] cur st = if st then [cur] else [] := by
  cases st <;> rfl

theorem dRun_cons (ch : Char) (cs : List Char) (cur : Nat) (st : Bool) :
    natsRun (ch :: cs) cur st = if Nat.beq ch.toNat 32 = true then
      (if st then cur :: natsRun cs 0 false else natsRun cs 0 false)
      else natsRun cs (cur * 10 + (ch.toNat - 48)) true := by
  have e : natsRun (ch :: cs) cur st = Bool.rec (motive := fun _ => List Nat)
      (natsRun cs (Nat.add (Nat.mul cur 10) (Nat.sub ch.toNat 48)) true)
      (Bool.rec (motive := fun _ => List Nat) (natsRun cs 0 false)
        (List.cons cur (natsRun cs 0 false)) st) (Nat.beq ch.toNat 32) := rfl
  rw [e]
  generalize Nat.beq ch.toNat 32 = b
  cases b <;> cases st <;> rfl

theorem dDigits_mem : ∀ {cs : List Char}, digitsOK cs = true → ∀ c ∈ cs, c = ' ' ∨ c.isDigit = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | ch :: cs, h, c, hc => by
    rw [dDigits_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · by_cases hs : Nat.beq c.toNat 32 = true
      · exact Or.inl ((char_of_beq hs (by decide)).trans (by decide))
      · exact Or.inr (isDigit_of (by simpa [hs] using h.1))
    · exact dDigits_mem h.2 c hc

theorem dRun_toks : ∀ (cs o : List Char), digitsOK cs = true → (∀ c ∈ o, c.isDigit = true) →
    natsRun cs (val o) (!o.isEmpty) = toks (o ++ cs)
  | [], o, _, ho => by
    rw [dRun_nil, List.append_nil, toks_digits ho]
    cases o <;> rfl
  | ch :: cs, o, h, ho => by
    have hd := h
    rw [dDigits_cons, Bool.and_eq_true] at hd
    rw [dRun_cons]
    by_cases hs : Nat.beq ch.toNat 32 = true
    · have hch : ch = ' ' := (char_of_beq hs (by decide)).trans (by decide)
      subst hch
      have hr := dRun_toks cs [] hd.2 (by simp)
      rw [List.nil_append, val_nil] at hr
      rw [ite_eq_left hs, toks_space ho cs, ← hr]
      cases o <;> rfl
    · rw [ite_eq_right hs]
      have hdig : ch.isDigit = true := isDigit_of (by simpa [hs] using hd.1)
      have ho' : ∀ c ∈ o ++ [ch], c.isDigit = true := by
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact ho c hc
        · rw [List.mem_singleton.1 hc]
          exact hdig
      have e : o ++ ch :: cs = (o ++ [ch]) ++ cs := by simp
      rw [e, ← dRun_toks cs (o ++ [ch]) hd.2 ho']
      have hv : val (o ++ [ch]) = val o * 10 + (ch.toNat - 48) := ofDigitChars_snoc o ch
      have hne : (o ++ [ch]).isEmpty = false := by simp
      rw [hv, hne]
      rfl

theorem toNat?_piece {q : List Char} (hq : ∀ c ∈ q, c.isDigit = true) :
    (String.ofList q).toNat? = if q.isEmpty then none else some (val q) := by
  cases q with
  | nil =>
    have e : ([] : List Char).isEmpty = true := rfl
    rw [if_pos e]
    refine String.toNat?_eq_none ?_
    rw [Bool.eq_false_iff]
    intro h
    exact (String.isNat_iff.1 h).1 (by simp)
  | cons c q =>
    rw [toNat_digits hq (List.cons_ne_nil _ _)]
    rfl

theorem filterMap_pieces : ∀ (L : List (List Char)), (∀ q ∈ L, ∀ c ∈ q, c.isDigit = true) →
    (L.map String.ofList).filterMap String.toNat? = (L.filter fun p => !p.isEmpty).map val
  | [], _ => rfl
  | q :: L, h => by
    rw [List.map_cons, List.filterMap_cons, toNat?_piece (h q List.mem_cons_self),
      filterMap_pieces L (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
    cases q <;> simp

theorem parse_eq {cs : List Char} (h : digitsOK cs = true) :
    CFSG.EvenSporadicStandard.M22Std.i22fParse (String.ofList cs) =
      ((natsK cs).map UInt32.ofNat).toArray := by
  have hr := dRun_toks cs [] h (by simp)
  rw [List.nil_append, val_nil, List.isEmpty_nil, Bool.not_true] at hr
  unfold CFSG.EvenSporadicStandard.M22Std.i22fParse natsK
  rw [splitOn_sp, List.splitOnPPrepend_nil_right, hr]
  unfold toks
  rw [filterMap_pieces]
  intro q hq c hc
  obtain ⟨h1, h2⟩ := mem_splitOnP cs q hq c hc
  rcases dDigits_mem h c h1 with rfl | hc'
  · exact absurd h2 (by decide)
  · exact hc'

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.RelTR CFSG.Sporadic.Th.Native CFSG.KC.LQT.Syl

noncomputable abbrev pp (P i : Nat) : Nat := pg 15 32767 P i

theorem chkL_spec {P : Nat} : ∀ (l : List Nat) (i : Nat), chkL P l i = true →
    i + l.length = 32256 ∧ ∀ j (hj : j < l.length), l[j] = pp P (i + j)
  | [], i, h => by
    have h' : Nat.beq i 32256 = true := h
    exact ⟨by simpa using Nat.eq_of_beq_eq_true h', fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | x :: l, i, h => by
    have e : chkL P (x :: l) i = (Nat.beq x (pp P i) && chkL P l (i + 1)) := by
      rw [← PK.bAnd_eq]
      rfl
    rw [e, Bool.and_eq_true] at h
    obtain ⟨hl, hv⟩ := chkL_spec l (i + 1) h.2
    refine ⟨by simp only [List.length_cons]; omega, fun j hj => ?_⟩
    cases j with
    | zero =>
      rw [List.getElem_cons_zero, Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h.1
    | succ k =>
      rw [List.getElem_cons_succ, hv k (by simpa using hj)]
      congr 1
      omega

theorem TR_congr {n : Nat} {t : Table} {f g : Nat → Nat} (h : TR n t f) (e : ∀ i < n, f i = g i) :
    TR n t g :=
  ⟨h.1, fun i hi => by rw [← e i hi]; exact h.2 i hi⟩

theorem tab_TR {P : Nat} {l : List Nat} (hc : chkL P l 0 = true)
    (hb : ∀ i < 32256, pp P i < 32256) :
    TR 32256 ((l.map UInt32.ofNat).toArray) (pp P) := by
  obtain ⟨hlen, hv⟩ := chkL_spec l 0 hc
  rw [Nat.zero_add] at hlen
  refine ⟨by simp [hlen], fun i hi => ⟨?_, hb i hi⟩⟩
  have hi' : i < l.length := by omega
  unfold ap
  rw [getElem!_pos _ i (by simp; omega)]
  simp only [List.getElem_toArray, List.getElem_map, UInt32.toNat_ofNat']
  rw [hv i hi', Nat.zero_add]
  exact Nat.mod_eq_of_lt (by have := hb i hi; omega)

theorem perm_facts {n nw p q : Nat} (h : permOK n 15 32767 nw p q = true) :
    ∀ i < n, pp p i < n ∧ pp q i < n ∧ pp q (pp p i) = i ∧ pp p (pp q i) = i := by
  have h' : permOK n 15 (mask 15) nw p q = true := h
  obtain ⟨g, hg, hgi⟩ := CFSG.KC.EnumSound.permOK_perm h'
  have hg' : ∀ x : Fin n, pp p x = g x := hg
  have hgi' : ∀ x : Fin n, pp q x = g⁻¹ x := hgi
  intro i hi
  refine ⟨by rw [hg' ⟨i, hi⟩]; exact (g _).2, by rw [hgi' ⟨i, hi⟩]; exact (g⁻¹ _).2, ?_, ?_⟩
  · have e := hgi' (g ⟨i, hi⟩)
    rw [hg' ⟨i, hi⟩, e]
    simp
  · have e := hg' (g⁻¹ ⟨i, hi⟩)
    rw [hgi' ⟨i, hi⟩, e]
    simp

theorem permOK_of {n : Nat} {P R : Table} {f g : Nat → Nat} (hP : TR n P f) (hR : TR n R g)
    (hfg : ∀ i < n, g (f i) = i ∧ f (g i) = i) :
    CFSG.EvenSporadicStandard.M22Std.i22fPermOK n P R = true := by
  unfold CFSG.EvenSporadicStandard.M22Std.i22fPermOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨allIn_iff.2 fun i hi => ?_, invOK_of hP hR fun i hi => (hfg i hi).1⟩,
    invOK_of hR hP fun i hi => (hfg i hi).2⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [(hP.2 i hi).1, (hR.2 i hi).1]
  exact ⟨(hP.2 i hi).2, (hR.2 i hi).2⟩

def invN (u : List (Nat × Bool)) : List (Nat × Bool) := (u.map fun l => (l.1, !l.2)).reverse

theorem invN_cons (l : Nat × Bool) (u : List (Nat × Bool)) :
    invN (l :: u) = invN u ++ [(l.1, !l.2)] := by
  simp [invN]

theorem invN_invN (u : List (Nat × Bool)) : invN (invN u) = u := by
  simp [invN, List.map_reverse, List.map_map, Function.comp_def]

def LInv (n : Nat) (F : Nat × Bool → Nat → Nat) : Prop :=
  ∀ l : Nat × Bool, ∀ y < n, F l y < n ∧ F (l.1, !l.2) (F l y) = y

variable {n : Nat} {F : Nat × Bool → Nat → Nat}

theorem wordF_lt (hF : LInv n F) : ∀ (u : List (Nat × Bool)), ∀ y < n, wordF F u y < n
  | [], y, hy => hy
  | l :: u, y, hy => by
    rw [wordF_cons]
    exact (hF l _ (wordF_lt hF u y hy)).1

theorem wordF_inv (hF : LInv n F) : ∀ (u : List (Nat × Bool)), ∀ y < n,
    wordF F (invN u) (wordF F u y) = y
  | [], _, _ => rfl
  | l :: u, y, hy => by
    rw [invN_cons, wordF_append, wordF_cons, wordF_cons]
    have e : wordF F [] = fun z => z := rfl
    rw [e]
    dsimp only
    rw [(hF l _ (wordF_lt hF u y hy)).2]
    exact wordF_inv hF u y hy

theorem wordF_inv' (hF : LInv n F) (u : List (Nat × Bool)) {y : Nat} (hy : y < n) :
    wordF F u (wordF F (invN u) y) = y := by
  have h := wordF_inv hF (invN u) y hy
  rwa [invN_invN] at h

theorem comm_fix (hF : LInv n F) {i : Nat} {u : List (Nat × Bool)} {ζ : Nat → Nat}
    (hu : ∀ y < n, wordF F u y = ζ y) (hc : ∀ l, ∀ y < n, ζ (F l y) = F l (ζ y)) :
    ∀ p < n, wordF F ([(i, true)] ++ u ++ [(i, false)] ++ invN u) p = p := by
  intro p hp
  have hq := wordF_lt hF (invN u) p hp
  have hz : ζ (wordF F (invN u) p) = p := by
    rw [← hu _ hq]
    exact wordF_inv' hF u hp
  rw [wordF_append, wordF_append, wordF_append, wordF_cons, wordF_cons]
  have e : wordF F [] = fun z => z := rfl
  rw [e]
  dsimp only
  rw [hu _ (hF (i, false) _ hq).1, hc _ _ hq, hz]
  exact (hF (i, false) p hp).2

theorem comm_inv {f g ζ : Nat → Nat} (hf : ∀ y < n, f y < n) (hg : ∀ y < n, g y < n)
    (hgf : ∀ y < n, g (f y) = y) (hfg : ∀ y < n, f (g y) = y) (hζ : ∀ y < n, ζ y < n)
    (hc : ∀ y < n, ζ (f y) = f (ζ y)) : ∀ y < n, ζ (g y) = g (ζ y) := by
  intro y hy
  have h1 : f (ζ (g y)) = ζ y := by rw [← hc _ (hg y hy), hfg y hy]
  rw [← h1, hgf _ (hζ _ (hg y hy))]

variable {A AI B BI : Nat}

noncomputable abbrev FL (A AI B BI : Nat) : Nat × Bool → Nat → Nat :=
  letterF (pp A) (pp AI) (pp B) (pp BI)

theorem lsel_eq (l : Nat × Bool) (p : Nat) :
    pg 15 32767 (lsel A AI B BI l) p = FL A AI B BI l p := by
  rcases l with ⟨_ | k, _ | _⟩ <;> rfl

theorem wimg_eq : ∀ (v : List (Nat × Bool)) (p : Nat), wimg A AI B BI v p = wordF (FL A AI B BI) v p
  | [], _ => rfl
  | l :: v, p => by
    rw [wordF_cons, ← wimg_eq v p, ← lsel_eq]
    rfl

theorem linv_of (pa : ∀ i < n, pp A i < n ∧ pp AI i < n ∧ pp AI (pp A i) = i ∧ pp A (pp AI i) = i)
    (pb : ∀ i < n, pp B i < n ∧ pp BI i < n ∧ pp BI (pp B i) = i ∧ pp B (pp BI i) = i) :
    LInv n (FL A AI B BI) := by
  rintro ⟨_ | k, _ | _⟩ y hy
  · exact ⟨(pa y hy).2.1, (pa y hy).2.2.2⟩
  · exact ⟨(pa y hy).1, (pa y hy).2.2.1⟩
  · exact ⟨(pb y hy).2.1, (pb y hy).2.2.2⟩
  · exact ⟨(pb y hy).1, (pb y hy).2.2.1⟩

theorem fixW_spec {v : List (Nat × Bool)} (h : fixW A AI B BI v = true) :
    ∀ i < 32256, wordF (FL A AI B BI) v i = i := by
  intro i hi
  rw [← wimg_eq]
  exact Nat.eq_of_beq_eq_true (PK.allN_iff.1 h i hi)

theorem tabW_spec {v : List (Nat × Bool)} {Z : Nat} (h : tabW A AI B BI v Z = true) :
    ∀ i < 32256, wordF (FL A AI B BI) v i = pp Z i := by
  intro i hi
  rw [← wimg_eq]
  exact Nat.eq_of_beq_eq_true (PK.allN_iff.1 h i hi)

theorem commW_spec {P Z : Nat} (h : commW P Z = true) :
    ∀ i < 32256, pp P (pp Z i) = pp Z (pp P i) := by
  intro i hi
  unfold commW eq22 at h
  exact Nat.eq_of_beq_eq_true (PK.allN_iff.1 h i hi)

theorem comm_letters {ζ : Nat → Nat}
    (pa : ∀ i < n, pp A i < n ∧ pp AI i < n ∧ pp AI (pp A i) = i ∧ pp A (pp AI i) = i)
    (pb : ∀ i < n, pp B i < n ∧ pp BI i < n ∧ pp BI (pp B i) = i ∧ pp B (pp BI i) = i)
    (hζ : ∀ y < n, ζ y < n) (hA : ∀ y < n, ζ (pp A y) = pp A (ζ y))
    (hB : ∀ y < n, ζ (pp B y) = pp B (ζ y)) :
    ∀ l, ∀ y < n, ζ (FL A AI B BI l y) = FL A AI B BI l (ζ y) := by
  rintro ⟨_ | k, _ | _⟩
  · exact comm_inv (fun y hy => (pa y hy).1) (fun y hy => (pa y hy).2.1) (fun y hy => (pa y hy).2.2.1)
      (fun y hy => (pa y hy).2.2.2) hζ hA
  · exact hA
  · exact comm_inv (fun y hy => (pb y hy).1) (fun y hy => (pb y hy).2.1) (fun y hy => (pb y hy).2.2.1)
      (fun y hy => (pb y hy).2.2.2) hζ hB
  · exact hB

noncomputable def xL (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun l _ ih p => strictN (ih p) (fun q => nIf(Nat.beq l (nat_lit 0), wimg A AI B BI sA q,
      wimg A AI B BI sB q))) L

theorem xpt_xL (sA sB : List (Nat × Bool)) (xw : List (List Nat)) (i : Nat) :
    xpt A AI B BI sA sB xw i = xL A AI B BI sA sB (getK xw i []) := rfl

theorem xL_cons (sA sB : List (Nat × Bool)) (l : Nat) (L : List Nat) (p : Nat) :
    xL A AI B BI sA sB (l :: L) p = strictN (xL A AI B BI sA sB L p)
      (fun q => nIf(Nat.beq l (nat_lit 0), wimg A AI B BI sA q, wimg A AI B BI sB q)) := rfl

noncomputable abbrev GLt (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (l : Nat) : Nat → Nat :=
  if l = 0 then wimg A AI B BI sA else wimg A AI B BI sB

theorem xL_eq (sA sB : List (Nat × Bool)) : ∀ (L : List Nat) (p : Nat),
    xL A AI B BI sA sB L p = L.foldr (fun l q => GLt A AI B BI sA sB l q) p
  | [], _ => rfl
  | l :: L, p => by
    rw [List.foldr_cons, ← xL_eq sA sB L p, xL_cons, PK.strictN_eq]
    rcases l with _ | k
    · rfl
    · rfl

theorem vpt_cons (sA sB : List (Nat × Bool)) (xw : List (List Nat)) (l : Nat) (wd : List Nat)
    (p : Nat) : vpt A AI B BI sA sB xw (l :: wd) p =
      xpt A AI B BI sA sB xw (l % 3) (vpt A AI B BI sA sB xw wd p) := by
  change strictN (vpt A AI B BI sA sB xw wd p) _ = _
  rw [PK.strictN_eq]
  rfl

theorem prod_TR (hn : n < 2 ^ 32) {gen : Nat → Table} {G : Nat → Nat → Nat}
    (hg : ∀ l, TR n (gen l) (G l)) : ∀ w : List Nat,
    TR n (CFSG.EvenSporadicStandard.M22Std.i22fProd n gen w) (fun p => w.foldr (fun l q => G l q) p)
  | [] => idT_TR hn
  | l :: w => compT_TR (hg l) (prod_TR hn hg w)

theorem notR_iff (c : Bool) : Bool.rec (motive := fun _ => Bool) true false c = true ↔ c = false := by
  cases c <;> simp

theorem beqF_iff {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h e
    subst e
    rw [Nat.beq_refl] at h
    exact absurd h (by decide)
  · intro h
    cases e : Nat.beq a b
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem recK_spec : ∀ {wl : List (Nat × Nat × Nat)} {v w : Nat}, recK wl v w = true →
    ∃ r ∈ wl, r.1 = v ∧ r.2.1 = w
  | [], _, _, h => absurd h Bool.false_ne_true
  | r :: wl, v, w, h => by
    have e : recK (r :: wl) v w =
        if (Nat.beq r.1 v && Nat.beq r.2.1 w) = true then true else recK wl v w := by
      rw [← PK.bAnd_eq, ← PK.bIf_eq]
      rfl
    rw [e] at h
    by_cases hc : (Nat.beq r.1 v && Nat.beq r.2.1 w) = true
    · rw [Bool.and_eq_true] at hc
      exact ⟨r, List.mem_cons_self, Nat.eq_of_beq_eq_true hc.1, Nat.eq_of_beq_eq_true hc.2⟩
    · rw [if_neg hc] at h
      obtain ⟨r', hr', h1, h2⟩ := recK_spec h
      exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩

theorem witsD_spec {sA sB : List (Nat × Bool)} {D : CFSG.KC.LQT.Cov.CD} :
    ∀ {wl : List (Nat × Nat × Nat)}, witsD A AI B BI sA sB D wl = true → ∀ r ∈ wl,
      r.2.2 < 32256 ∧ vpt A AI B BI sA sB D.xw (getK D.words r.1 [])
        (vpt A AI B BI sA sB D.xw (getK D.words r.2.1 []) r.2.2) ≠
      vpt A AI B BI sA sB D.xw (getK D.words r.2.1 []) (vpt A AI B BI sA sB D.xw (getK D.words r.1 []) r.2.2)
  | [], _, _, hr => absurd hr List.not_mem_nil
  | r :: wl, h, r', hr' => by
    have e : witsD A AI B BI sA sB D (r :: wl) = (Nat.blt r.1 D.nV && (Nat.blt r.2.1 D.nV &&
        (witOK A AI B BI sA sB D.xw (getK D.words r.1 []) (getK D.words r.2.1 []) r.2.2 &&
          witsD A AI B BI sA sB D wl))) := by
      rw [← PK.bAnd_eq, ← PK.bAnd_eq, ← PK.bAnd_eq]
      rfl
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, -, hw, hrest⟩ := h
    rcases List.mem_cons.1 hr' with rfl | hr'
    · unfold witOK at hw
      rw [PK.bAnd_eq, Bool.and_eq_true, notR_iff, beqF_iff, Nat.blt_eq] at hw
      exact hw
    · exact witsD_spec hrest r' hr'

theorem len_filter_le {α : Type} {p q : α → Bool} : ∀ (l : List α),
    (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => le_refl _
  | x :: l, h => by
    have ih := len_filter_le l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.filter_cons, List.filter_cons]
    by_cases hp : p x = true
    · rw [if_pos hp, if_pos (h x List.mem_cons_self hp), List.length_cons, List.length_cons]
      omega
    · rw [if_neg hp]
      split
      · rw [List.length_cons]
        omega
      · exact ih

theorem cover_words : (CFSG.LieType.Multipliers.coverWords
      CFSG.Sporadic.Recognition.M22Multiplier.m22Rels
      CFSG.Sporadic.Recognition.M22Multiplier.m22CommWord).map
      CFSG.Sporadic.Recognition.CoverRecipe.natWord =
    relK.map (fun r => [(0, true)] ++ r ++ [(0, false)] ++ invN r) ++
      relK.map (fun r => [(1, true)] ++ r ++ [(1, false)] ++ invN r) ++ [cwA, cwB] := by
  decide +kernel

end CFSG.KC.I22F.Pf

public section

namespace CFSG.KC.I22F

open CFSG.KC.I22F.Pf CFSG.KC.Enum CFSG.KC.DecText CFSG.KS CFSG.KS.TW CFSG.KS.RelTR
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native CFSG.EvenSporadicStandard.M22Std
  CFSG.QuasithinUnique.Ch1.M22Cover CFSG.KC.LQT.Cov CFSG.KC.LQT.Syl CFSG.KC.M22S
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.LieType.Multipliers
open CFSG.Sporadic.Mathieu (m22gA m22gB)
open CFSG.Sporadic.Schreier.Tits (getElem!_ofFn_of_lt)

theorem i22fCheckT_of {A AI B BI Z cA cB : Nat} {ca cb ct : List Char} {WL : List (Nat × Nat × Nat)}
    (hA : CFSG.KC.LQT.P.code m22gA = cA) (hB : CFSG.KC.LQT.P.code m22gB = cB)
    (hct : covData = parseData (String.ofList ct))
    (hda : digitsOK ca = true) (hdb : digitsOK cb = true)
    (hta : chkL A (CFSG.KC.DecText.natsK ca) 0 = true)
    (htb : chkL B (CFSG.KC.DecText.natsK cb) 0 = true)
    (hpa : permOK 32256 15 32767 483840 A AI = true) (hpb : permOK 32256 15 32767 483840 B BI = true)
    (hr0 : fixW A AI B BI (getK relK 0 []) = true) (hr1 : fixW A AI B BI (getK relK 1 []) = true)
    (hr2 : tabW A AI B BI (getK relK 2 []) Z = true) (hr3 : fixW A AI B BI (getK relK 3 []) = true)
    (hr4 : fixW A AI B BI (getK relK 4 []) = true) (hr5 : tabW A AI B BI (getK relK 5 []) Z = true)
    (hzA : commW A Z = true) (hzB : commW B Z = true)
    (hcA : fixW A AI B BI cwA = true) (hcB : fixW A AI B BI cwB = true)
    (hw : witsK A AI B BI sAK sBK ct WL = true) (hc : cntK cA cB ct WL = true) :
    i22fCheckT 32256 (i22fParse (String.ofList ca)) (i22fParse (String.ofList cb)) = true := by
  have hn : (32256 : Nat) < 2 ^ 32 := by norm_num
  have pa := perm_facts hpa
  have pb := perm_facts hpb
  rw [parse_eq hda, parse_eq hdb]
  set α : Table := ((CFSG.KC.DecText.natsK ca).map UInt32.ofNat).toArray with hα
  set β : Table := ((CFSG.KC.DecText.natsK cb).map UInt32.ofNat).toArray with hβ
  have tA : TR 32256 α (pp A) := tab_TR hta fun i hi => (pa i hi).1
  have tB : TR 32256 β (pp B) := tab_TR htb fun i hi => (pb i hi).1
  have tAI : TR 32256 (invT 32256 α) (pp AI) :=
    invT_TR hn tA fun i hi => ⟨(pa i hi).2.1, (pa i hi).2.2.2, (pa i hi).2.2.1⟩
  have tBI : TR 32256 (invT 32256 β) (pp BI) :=
    invT_TR hn tB fun i hi => ⟨(pb i hi).2.1, (pb i hi).2.2.2, (pb i hi).2.2.1⟩
  have hL : ∀ l, TR 32256 (letterTab α (invT 32256 α) β (invT 32256 β) l) (FL A AI B BI l) :=
    letterTab_TR tA tAI tB tBI
  have hF : LInv 32256 (FL A AI B BI) := linv_of pa pb
  unfold i22fCheckT
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨permOK_of tA tAI fun i hi => ⟨(pa i hi).2.2.1, (pa i hi).2.2.2⟩,
    permOK_of tB tBI fun i hi => ⟨(pb i hi).2.2.1, (pb i hi).2.2.2⟩⟩, ?_⟩, ?_⟩
  ·
    refine relCheck_of_TR hn hL ?_
    have hZ : ∀ {r : List (Nat × Bool)}, tabW A AI B BI r Z = true →
        ∃ ζ : Nat → Nat, (∀ y < 32256, wordF (FL A AI B BI) r y = ζ y) ∧
          ∀ l, ∀ y < 32256, ζ (FL A AI B BI l y) = FL A AI B BI l (ζ y) := by
      intro r hr
      have hs := tabW_spec hr
      have hzb : ∀ y < 32256, pp Z y < 32256 := fun y hy => by
        rw [← hs y hy]
        exact wordF_lt hF r y hy
      refine ⟨pp Z, hs, comm_letters pa pb hzb (fun y hy => (commW_spec hzA y hy).symm)
        (fun y hy => (commW_spec hzB y hy).symm)⟩
    have hI : ∀ {r : List (Nat × Bool)}, fixW A AI B BI r = true →
        ∃ ζ : Nat → Nat, (∀ y < 32256, wordF (FL A AI B BI) r y = ζ y) ∧
          ∀ l, ∀ y < 32256, ζ (FL A AI B BI l y) = FL A AI B BI l (ζ y) :=
      fun hr => ⟨fun y => y, fixW_spec hr, fun _ _ _ => rfl⟩
    have hrel : ∀ r ∈ relK, ∃ ζ : Nat → Nat, (∀ y < 32256, wordF (FL A AI B BI) r y = ζ y) ∧
        ∀ l, ∀ y < 32256, ζ (FL A AI B BI l y) = FL A AI B BI l (ζ y) := by
      intro r hr
      simp only [relK, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hI hr0
      · exact hI hr1
      · exact hZ hr2
      · exact hI hr3
      · exact hI hr4
      · exact hZ hr5
    rw [cover_words]
    intro v hv
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | rfl | rfl
    · obtain ⟨ζ, h1, h2⟩ := hrel r hr
      exact comm_fix hF h1 h2
    · obtain ⟨ζ, h1, h2⟩ := hrel r hr
      exact comm_fix hF h1 h2
    · exact fixW_spec hcA
    · exact fixW_spec hcB
  ·
    cases hp : parseCov ct with
    | none =>
      rw [witsK, hp] at hw
      exact absurd hw Bool.false_ne_true
    | some D =>
    have hw' : witsD A AI B BI sAK sBK D WL = true := by
      rw [witsK, hp] at hw
      exact hw
    have hc' : cntD (eltsOf cA cB D) WL D.nV = true := by
      rw [cntK, hp] at hc
      exact hc
    obtain ⟨hxw, hwl, -, hpd⟩ := CFSG.KC.LQT.Cov.Parse.parseCov_sound hp
    have hcd : covData = CFSG.KC.LQT.Cov.Eqns.ofCD D := hct.trans hpd
    set d := CFSG.KC.LQT.Cov.Eqns.ofCD D with hd
    set tAP := wordTab 32256 α (invT 32256 α) β (invT 32256 β) (natWord m22SurjA) with htAP
    set tBP := wordTab 32256 α (invT 32256 α) β (invT 32256 β) (natWord m22SurjB) with htBP
    have rAP : TR 32256 tAP (wimg A AI B BI sAK) := by
      have h1 := wordTab_TR hn hL (natWord m22SurjA)
      have e : natWord m22SurjA = sAK := by decide +kernel
      rw [e] at h1
      exact TR_congr h1 fun y _ => (wimg_eq sAK y).symm
    have rBP : TR 32256 tBP (wimg A AI B BI sBK) := by
      have h1 := wordTab_TR hn hL (natWord m22SurjB)
      have e : natWord m22SurjB = sBK := by decide +kernel
      rw [e] at h1
      exact TR_congr h1 fun y _ => (wimg_eq sBK y).symm
    set gen : Nat → Table := fun l => if l = 0 then tAP else tBP with hgen
    have hg : ∀ l, TR 32256 (gen l) (GLt A AI B BI sAK sBK l) := by
      intro l
      by_cases hl : l = 0
      · simp only [hgen, GLt, hl, if_true]
        exact rAP
      · simp only [hgen, GLt, hl, if_false]
        exact rBP
    have hxwOf : ∀ i : Fin 3, covData.xwOf i = getK D.xw i.val [] := by
      intro i
      rw [hcd, CFSG.KC.LQT.Cov.Perm.sgetK_eq]
      fin_cases i <;> rfl
    have hword : ∀ v, covData.words[v]! = getK D.words v [] := by
      intro v
      rw [hcd, CFSG.KC.LQT.Cov.Perm.sgetK_eq]
      change D.words.toArray[v]! = D.words.getD v []
      by_cases hv : v < D.words.length
      · rw [getElem!_pos D.words.toArray v (by simpa using hv), List.getElem_toArray,
          List.getD_eq_getElem _ _ hv]
      · rw [getElem!_neg D.words.toArray v (by simpa using hv),
          List.getD_eq_default _ _ (by omega)]
        rfl
    have hvert : ∀ v < covData.nV, TR 32256 ((i22fVertexTabs 32256 tAP tBP)[v]!)
        (vpt A AI B BI sAK sBK D.xw (getK D.words v [])) := by
      intro v hv
      set tx : Array Table := Array.ofFn (n := 3) fun i => i22fProd 32256 gen (covData.xwOf i)
        with htxdef
      have htx : ∀ l : Nat, TR 32256 (tx[l % 3]!) (xpt A AI B BI sAK sBK D.xw (l % 3)) := by
        intro l
        rw [htxdef, getElem!_ofFn_of_lt _ (Nat.mod_lt l (by norm_num)), hxwOf]
        refine TR_congr (prod_TR hn hg _) fun p _ => ?_
        dsimp only
        rw [xpt_xL, xL_eq]
      have e : (i22fVertexTabs 32256 tAP tBP)[v]! =
          i22fProd 32256 (fun l => tx[l % 3]!) (covData.words[v]!) := by
        unfold i22fVertexTabs
        exact getElem!_ofFn_of_lt _ hv
      rw [e, hword v]
      refine TR_congr (prod_TR (gen := fun l => tx[l % 3]!)
        (G := fun l => xpt A AI B BI sAK sBK D.xw (l % 3)) hn htx _) fun p _ => ?_
      generalize getK D.words v [] = wd
      induction wd with
      | nil => rfl
      | cons l wd ih => rw [List.foldr_cons, ih, vpt_cons]
    have cm := @CFSG.KC.LQT.P.code_mul 22 (by norm_num)
    have cb := @CFSG.KC.LQT.P.beq_code 22 (by norm_num)
    have ce := @CFSG.KC.LQT.P.code_eq_iff 22 (by norm_num)
    have c1 := CFSG.KC.LQT.P.code_one (n := 22)
    have hnV : covData.nV = D.nV := by
      rw [hcd]
      rfl
    have hE : ∀ v < D.nV, getK (eltsOf cA cB D) v 0 = CFSG.KC.LQT.P.code (d.tab.el d.x v) := by
      intro v hv
      rw [CFSG.KC.LQT.Cov.Perm.sgetK_eq]
      exact CFSG.KC.LQT.Cov.Perm.codes_E (d := d) hA hB hxw rfl rfl rfl rfl hwl v hv
    have hrep : ∀ v < D.nV, CFSG.Monster.B.Co2.Rep 22 (covData.elaTab[v]!) (d.tab.el d.x v) := by
      intro v hv
      rw [hcd]
      exact d.rep_el (fun i => d.xa_rep i) hv
    have hinv : ∀ v < D.nV, i22fIsInv covData.elaTab v = isInvK (getK (eltsOf cA cB D) v 0) := by
      intro v hv
      have l1 : i22fIsInv covData.elaTab v = true ↔
          (d.tab.el d.x v ≠ 1 ∧ d.tab.el d.x v * d.tab.el d.x v = 1) := by
        unfold i22fIsInv
        rw [Bool.and_eq_true, Bool.not_eq_true', ne_eq, ← CFSG.Monster.B.Co2.eqA_iff (hrep v hv)
          CFSG.Monster.B.Co2.rep_idA, ← CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Co2.rep_compA
          (hrep v hv) (hrep v hv)) CFSG.Monster.B.Co2.rep_idA, Bool.eq_false_iff, ne_eq]
      have l2 : isInvK (getK (eltsOf cA cB D) v 0) = true ↔
          (d.tab.el d.x v ≠ 1 ∧ d.tab.el d.x v * d.tab.el d.x v = 1) := by
        unfold isInvK
        rw [PK.bAnd_eq, Bool.and_eq_true, notR_iff, hE v hv, c1, cm, cb, beqF_iff, Ne, Ne, ce]
      rw [Bool.eq_iff_iff, l1, l2]
    have hpc : ∀ v < D.nV, ∀ w < D.nV,
        i22fPartner 32256 covData.elaTab (i22fVertexTabs 32256 tAP tBP) v w = true →
          candK (eltsOf cA cB D) WL v w = true := by
      intro v hv w hwn h
      unfold i22fPartner at h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hc2 := (CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Co2.rep_compA (hrep v hv) (hrep w hwn))
        (CFSG.Monster.B.Co2.rep_compA (hrep w hwn) (hrep v hv))).1 h2
      have hT := beq_iff_eq.1 h3
      have hvv := hvert v (by rw [hnV]; exact hv)
      have hww := hvert w (by rw [hnV]; exact hwn)
      unfold candK
      rw [PK.bAnd_eq, PK.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, notR_iff, notR_iff, beqF_iff,
        hE v hv, hE w hwn, cm, cm, cb]
      refine ⟨bne_iff_ne.1 h1, hc2, ?_⟩
      rw [Bool.eq_false_iff]
      intro hr
      obtain ⟨r, hrm, hr1, hr2⟩ := recK_spec hr
      obtain ⟨hpt, hne⟩ := witsD_spec hw' r hrm
      rw [hr1, hr2] at hne
      apply hne
      have k1 := (compT_TR hvv hww).2 r.2.2 hpt
      have k2 := (compT_TR hww hvv).2 r.2.2 hpt
      rw [hT] at k1
      exact k1.1.symm.trans k2.1
    unfold i22fCount
    simp only [decide_eq_true_eq]
    have hinvs : (List.range covData.nV).filter (i22fIsInv covData.elaTab) =
        (List.range D.nV).filter (fun v => isInvK (getK (eltsOf cA cB D) v 0)) := by
      rw [hnV]
      exact List.filter_congr fun v hv => hinv v (List.mem_range.1 hv)
    rw [hinvs]
    rw [cntD] at hc'
    simp only [Nat.ble_eq, CFSG.KC.LQT.Cov.Perm.slenK_eq] at hc'
    refine le_trans ?_ hc'
    refine len_filter_le _ fun v hv h => ?_
    have hvn : v < D.nV := List.mem_range.1 (List.mem_filter.1 hv).1
    rw [decide_eq_true_eq] at h
    rw [Nat.ble_eq]
    exact le_trans h (len_filter_le _ fun w hw h' =>
      hpc v hvn w (List.mem_range.1 (List.mem_filter.1 hw).1) h')

end CFSG.KC.I22F

end
