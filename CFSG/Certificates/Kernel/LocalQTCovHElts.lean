module

public import CFSG.Certificates.Kernel.LocalQTCovHBase
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.LocalQTCovTElts
import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.Kernel.MonsterB.Co2MatSound
import CFSG.Certificates.Kernel.LocalQTTab2KSound
import CFSG.Certificates.Kernel.LocalQTBaseWProved

public section

namespace CFSG.KC.LQT.Cov.H

open CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.HSCover CFSG.Sporadic.Schreier
open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KC.LQT.Syl CFSG.Monster.B.Co2.Native
open CFSG.QuasithinUnique.Ch1.M22Cover (fo)

private noncomputable def eltsH_wGo (n w A B : Nat) (wd : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcomp n w (mask w) acc
      (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0))) ih) wd acc

private theorem eltsH_wPK_eq (n w A B : Nat) (wd : List Nat) :
    wPK n w A B wd = eltsH_wGo n w A B wd (pidn n w) := rfl

private theorem eltsH_wGo_nil (n w A B acc : Nat) : eltsH_wGo n w A B [] acc = acc := rfl

private theorem eltsH_wGo_cons (n w A B l : Nat) (wd : List Nat) (acc : Nat) :
    eltsH_wGo n w A B (l :: wd) acc =
      eltsH_wGo n w A B wd (pcomp n w (mask w) acc
        (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0))) := by
  change strictN (pcomp n w (mask w) acc (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0)))
    (eltsH_wGo n w A B wd) = _
  exact CFSG.KS.PF.strictN_eqP _ _

private theorem eltsH_gen_unpack {A B : Nat}
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A)
    (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B) (l : Nat) :
    Raw.unpack 3850 12 (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0)) = genArr l := by
  unfold genArr lc
  cases h : Nat.beq l 0
  · have hl : l ≠ 0 := fun e => by subst e; simp at h
    rw [if_neg hl]
    exact hB.symm
  · have hl : l = 0 := Nat.eq_of_beq_eq_true h
    rw [if_pos hl]
    exact hA.symm

private theorem eltsH_wGo_spec {A B : Nat}
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A) (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
    (hAr : ∀ i < 3850, pg 12 (mask 12) A i < 3850)
    (hBr : ∀ i < 3850, pg 12 (mask 12) B i < 3850) :
    ∀ (wd : List Nat) (acc : Nat), (∀ i < 3850, pg 12 (mask 12) acc i < 3850) →
      Raw.unpack 3850 12 (eltsH_wGo 3850 12 A B wd acc) =
        wd.foldl (fun a l => compA 3850 a (genArr l)) (Raw.unpack 3850 12 acc) ∧
      ∀ i < 3850, pg 12 (mask 12) (eltsH_wGo 3850 12 A B wd acc) i < 3850 := by
  intro wd
  induction wd with
  | nil =>
    intro acc hacc
    rw [eltsH_wGo_nil, List.foldl_nil]
    exact ⟨rfl, hacc⟩
  | cons l wd ih =>
    intro acc hacc
    have hgr : ∀ i < 3850,
        pg 12 (mask 12) (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0)) i < 3850 := by
      cases Nat.beq l 0
      · exact hBr
      · exact hAr
    have hnew : ∀ i < 3850, pg 12 (mask 12) (pcomp 3850 12 (mask 12) acc
        (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0))) i < 3850 := by
      intro i hi
      rw [CFSG.KS.PF.pg_pcomp (by norm_num) hi]
      exact hacc _ (hgr i hi)
    rw [eltsH_wGo_cons]
    obtain ⟨h1, h2⟩ := ih _ hnew
    refine ⟨?_, h2⟩
    rw [h1, List.foldl_cons, ← CFSG.KC.LQT.Cov.T.compA_unpack (by norm_num) hgr,
      eltsH_gen_unpack hA hB l]

private theorem eltsH_wPK_unpack {A B : Nat}
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A) (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
    (hAr : ∀ i < 3850, pg 12 (mask 12) A i < 3850)
    (hBr : ∀ i < 3850, pg 12 (mask 12) B i < 3850) (wd : List Nat) :
    Raw.unpack 3850 12 (wPK 3850 12 A B wd) = wordArrP wd ∧
      ∀ i < 3850, pg 12 (mask 12) (wPK 3850 12 A B wd) i < 3850 := by
  have hid : ∀ i < 3850, pg 12 (mask 12) (pidn 3850 12) i < 3850 := by
    intro i hi
    rw [CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hi]
    exact hi
  obtain ⟨h1, h2⟩ := eltsH_wGo_spec hA hB hAr hBr wd (pidn 3850 12) hid
  rw [eltsH_wPK_eq]
  refine ⟨?_, h2⟩
  rw [h1, CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num)]
  rfl

private noncomputable def eltsH_bGo (n w : Nat) (X : List Nat)
    (WR : List (List (List Nat))) (k : List Nat → Bool) :
    List Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ acc => List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) acc [])
    (fun p _ ih c acc => strictB c fun c =>
      strictB (pcomp n w (mask w) (getK acc (Nat.sub (Nat.sub c 1) p) 0)
        (getK X (Nat.mod (lastK (getRG WR c [])) 3) 0)) fun e =>
      ih (Nat.succ c) (List.cons e acc))

private theorem eltsH_buildEH_eq (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P : List Nat) (k : List Nat → Bool) :
    buildEH n w X WR P k = eltsH_bGo n w X WR k P 1 [pidn n w] := rfl

private theorem eltsH_getK_rev_range {α : Type} (E : Nat → α) (d : α) {c p : Nat}
    (hp : p < c) : getK ((List.range c).reverse.map E) (c - 1 - p) d = E p := by
  rw [CFSG.KC.LQT.Cov.Parse.getK_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_reverse (by
      rw [List.length_range]
      exact Nat.lt_of_le_of_lt (Nat.sub_le (c - 1) p) (Nat.sub_lt (by omega) (by decide))),
    List.length_range,
    show c - 1 - (c - 1 - p) = p by omega, List.getElem?_range hp,
    Option.map_some, Option.getD_some]

private theorem eltsH_bGo_rev (acc r : List Nat) (k : List Nat → Bool) :
    List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) acc r = k (acc.reverse ++ r) := by
  induction acc generalizing r with
  | nil => rfl
  | cons x xs ih =>
    change List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) xs (x :: r) = _
    rw [ih, List.reverse_cons, List.append_assoc]
    rfl

private theorem eltsH_bGo_spec_nil (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P0 : List Nat) (k : List Nat → Bool) :
    ∀ (c : Nat) (acc : List Nat) (E : Nat → Nat),
      0 < c → ([] : List Nat) = P0.drop (c - 1) → acc = (List.range c).reverse.map E →
      (∀ v, 0 < v → v < c →
        E v = pcomp n w (mask w) (E (getK P0 (v - 1) 0))
          (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0)) →
      (∀ v, 0 < v → v < c → getK P0 (v - 1) 0 < v) →
      ∃ E' : Nat → Nat,
        eltsH_bGo n w X WR k [] c acc = k ((List.range c).map E') ∧
        (∀ v < c, E' v = E v) ∧
        (∀ v, 0 < v → v < c →
          E' v = pcomp n w (mask w) (E' (getK P0 (v - 1) 0))
            (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0)) := by
  intro c acc E hc hsuf hacc hrec hpar
  refine ⟨E, ?_, fun v hv => rfl, ?_⟩
  · have e : eltsH_bGo n w X WR k [] c acc = k acc.reverse := by
      change List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
        (fun x _ ih r => ih (x :: r)) acc [] = k acc.reverse
      simpa using eltsH_bGo_rev acc [] k
    rw [e, hacc, List.map_reverse, List.reverse_reverse]
  · intro v hv vlt
    exact hrec v hv (by simpa using vlt)

private theorem eltsH_bGo_spec_p {P0 : List Nat} {acc : List Nat} {E : Nat → Nat}
    {p c : Nat} {P' : List Nat} (hc : 0 < c) (hsuf : p :: P' = P0.drop (c - 1))
    (hacc : acc = (List.range c).reverse.map E)
    (hpar : ∀ v, 0 < v → v < c + (p :: P').length → getK P0 (v - 1) 0 < v) :
    p = getK P0 (c - 1) 0 ∧ p < c ∧ getK acc (c.sub 1 - p) 0 = E p := by
  have hp_eq : p = getK P0 (c - 1) 0 := by
    have h0 : getK (P0.drop (c - 1)) 0 0 = p := by
      rw [← hsuf, CFSG.KC.LQT.Cov.Parse.getK_getD]
      rfl
    rw [← h0, CFSG.KC.LQT.Cov.Parse.getK_getD, CFSG.KC.LQT.Cov.Parse.getK_getD,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  have hpc : p < c := by
    rw [hp_eq]
    exact hpar c hc (by simp)
  refine ⟨hp_eq, hpc, ?_⟩
  rw [hacc]
  exact eltsH_getK_rev_range E 0 hpc

private theorem eltsH_bGo_spec_acc {P0 : List Nat} {n w c : Nat} {X : List Nat}
    {WR : List (List (List Nat))} {acc : List Nat} {E : Nat → Nat} {p : Nat} {P' : List Nat}
    (hc : 0 < c) (hsuf : p :: P' = P0.drop (c - 1))
    (hacc : acc = (List.range c).reverse.map E) :
    ∃ (E1 : Nat → Nat) (e : Nat),
      e = pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 3) 0) ∧
      P' = P0.drop c ∧
      e :: acc = (List.range (c + 1)).reverse.map E1 ∧
      E1 c = e ∧ (∀ v < c, E1 v = E v) := by
  let e := pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 3) 0)
  let E1 : Nat → Nat := fun v => if v = c then e else E v
  refine ⟨E1, e, rfl, ?_, ?_, by simp [E1], fun v hv => by simp [E1, show v ≠ c by omega]⟩
  · rw [show c = (c - 1) + 1 by omega, ← List.drop_drop (i := 1) (j := c - 1)]
    rw [← hsuf]
    rfl
  · rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.map_append,
      List.map_cons, List.map_nil, List.singleton_append, hacc]
    congr 1
    · simp [E1]
    · rw [List.map_congr_left]
      intro v hv
      rw [List.mem_reverse, List.mem_range] at hv
      simp [E1, show v ≠ c by omega]

private theorem eltsH_bGo_spec_rec {P0 : List Nat} {n w c : Nat} {X : List Nat}
    {WR : List (List (List Nat))} {E E1 : Nat → Nat} {e p : Nat} {P' : List Nat}
    (he : e = pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 3) 0))
    (hp_eq : p = getK P0 (c - 1) 0) (hpc : p < c) (hE1c : E1 c = e)
    (hE1lt : ∀ v < c, E1 v = E v)
    (hrec : ∀ v, 0 < v → v < c →
      E v = pcomp n w (mask w) (E (getK P0 (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0))
    (hpar : ∀ v, 0 < v → v < c + (p :: P').length → getK P0 (v - 1) 0 < v) :
    ∀ v, 0 < v → v < c + 1 →
      E1 v = pcomp n w (mask w) (E1 (getK P0 (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0) := by
  intro v hv hvlt
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hvlt) with hlt | rfl
  · rw [hE1lt v hlt, hrec v hv hlt]
    congr 1
    rw [hE1lt (getK P0 (v - 1) 0) (by
      have := hpar v hv (by simp; omega)
      omega)]
  · rw [hE1c, ← hp_eq, hE1lt p hpc]
    exact he

private theorem eltsH_bGo_spec_step {n w : Nat} {X : List Nat} {WR : List (List (List Nat))}
    (k : List Nat → Bool) {P' : List Nat} {c p : Nat} {acc : List Nat} {E : Nat → Nat}
    {e : Nat}
    (he : e = pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 3) 0))
    (hacc_p : getK acc (c.sub 1 - p) 0 = E p) :
    eltsH_bGo n w X WR k (p :: P') c acc = eltsH_bGo n w X WR k P' (c + 1) (e :: acc) := by
  have hstep : eltsH_bGo n w X WR k (p :: P') c acc =
      strictB c (fun c =>
        strictB (pcomp n w (mask w) (getK acc (Nat.sub c 1 - p) 0)
          (getK X (Nat.mod (lastK (getRG WR c [])) 3) 0)) fun e =>
        eltsH_bGo n w X WR k P' (c + 1) (e :: acc)) := rfl
  rw [hstep, CFSG.KS.PF.strictB_eqP, CFSG.KS.PF.strictB_eqP, hacc_p, ← he]

private theorem eltsH_bGo_spec (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P0 : List Nat) (k : List Nat → Bool) :
    ∀ (P : List Nat) (c : Nat) (acc : List Nat) (E : Nat → Nat),
      0 < c → P = P0.drop (c - 1) → acc = (List.range c).reverse.map E →
      (∀ v, 0 < v → v < c →
        E v = pcomp n w (mask w) (E (getK P0 (v - 1) 0))
          (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0)) →
      (∀ v, 0 < v → v < c + P.length → getK P0 (v - 1) 0 < v) →
      ∃ E' : Nat → Nat,
        eltsH_bGo n w X WR k P c acc = k ((List.range (c + P.length)).map E') ∧
        (∀ v < c, E' v = E v) ∧
        (∀ v, 0 < v → v < c + P.length →
          E' v = pcomp n w (mask w) (E' (getK P0 (v - 1) 0))
            (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0)) := by
  intro P
  induction P with
  | nil => simpa using eltsH_bGo_spec_nil n w X WR P0 k
  | cons p P' ih =>
    intro c acc E hc hsuf hacc hrec hpar
    obtain ⟨hp_eq, hpc, hacc_p⟩ := eltsH_bGo_spec_p (p := p) (P' := P') hc hsuf hacc hpar
    obtain ⟨E1, e, he, hsuf', hacc1, hE1c, hE1lt⟩ :=
      eltsH_bGo_spec_acc (n := n) (w := w) (X := X) (WR := WR) (p := p) (P' := P') hc hsuf
        hacc
    have hrec1 := eltsH_bGo_spec_rec (n := n) (w := w) (X := X) (WR := WR)
      (p := p) (P' := P') he hp_eq hpc hE1c hE1lt hrec hpar
    have hpar1 : ∀ v, 0 < v → v < c + 1 + P'.length → getK P0 (v - 1) 0 < v := by
      intro v hv hvlt
      exact hpar v hv (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hvlt)
    obtain ⟨E', hres, hagree, hrec'⟩ := ih (c + 1) (e :: acc) E1 (by omega) hsuf' hacc1
      hrec1 hpar1
    refine ⟨E', ?_, ?_, ?_⟩
    · rw [eltsH_bGo_spec_step k he hacc_p]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hres
    · intro v hv
      rw [hagree v (by omega)]
      exact hE1lt v hv
    · intro v hv hvlt
      exact hrec' v hv (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hvlt)

private theorem eltsH_build_exists (n w : Nat) (WR : List (List (List Nat))) (nV : Nat)
    (X P : List Nat) (k : List Nat → Bool) (hpar : parOK WR nV P = true)
    (hbuild : buildEH n w X WR P k = true) :
    ∃ E : Nat → Nat,
      k ((List.range nV).map E) = true ∧ E 0 = pidn n w ∧
      (∀ v, 0 < v → v < nV →
        E v = pcomp n w (mask w) (E (getK P (v - 1) 0))
          (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0)) := by
  obtain ⟨hnV, hpar'⟩ := CFSG.KC.LQT.Cov.T.parOK_spec hpar
  let E0 : Nat → Nat := fun _ => pidn n w
  have hacc : [pidn n w] = (List.range 1).reverse.map E0 := by
    simp [E0]
  have hrec : ∀ v, 0 < v → v < 1 →
      E0 v = pcomp n w (mask w) (E0 (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0) := by
    intro v hv hv1; omega
  have hpar0 : ∀ v, 0 < v → v < 1 + P.length → getK P (v - 1) 0 < v := by
    intro v hv hvlt
    exact (hpar' v hv (by omega)).1
  obtain ⟨E, hres, hagree, hrec'⟩ := eltsH_bGo_spec n w X WR P k P 1
    [pidn n w] E0 (by omega) (by simp) hacc hrec hpar0
  refine ⟨E, ?_, by simpa [E0] using hagree 0 (by omega), ?_⟩
  · have hb' : eltsH_bGo n w X WR k P 1 [pidn n w] = true := by
      rw [← eltsH_buildEH_eq]
      exact hbuild
    have hkres : k (List.map E (List.range (1 + P.length))) = true := by
      rw [← hres]
      exact hb'
    rwa [show 1 + P.length = nV by omega] at hkres
  · intro v hv0 hv
    exact hrec' v hv0 (by omega)

private theorem eltsH_elaOf_nil (XA : Fin 3 → Array Nat) : elaOf XA [] = idA 3850 := by
  simp [elaOf]

private theorem eltsH_elaOf_append (XA : Fin 3 → Array Nat) (w : List Nat) (i : Fin 3) :
    elaOf XA (w ++ [(i : Nat)]) = compA 3850 (elaOf XA w) (XA i) := by
  simp [elaOf, List.foldl_append, List.foldl_cons, List.foldl_nil, fo_val]

private theorem eltsH_lastK_lt {m : Nat} {w : List Nat} (h : ∀ l ∈ w, l < m) (hne : w ≠ []) :
    lastK w < m := by
  induction w with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · simpa [lastK] using h x (by simp)
    · have h' : ∀ l ∈ y :: ys, l < m := fun l hl => h l (by simp [hl])
      simpa [lastK] using ih h' (by simp)

private theorem eltsH_getRG_words (D : CH) (v : Nat) :
    getRG (rowsG D.words) v [] = D.words.getD v [] :=
  CFSG.KC.LQT.Cov.T.getRG_rowsG D.words v []

private theorem eltsH_word_mem {D : CH} (hwords : D.words.length = D.nV)
    {v : Nat} (hv : v < D.nV) : D.words.getD v [] ∈ D.words := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hwords]; exact hv),
    Option.getD_some]
  exact List.getElem_mem _

private theorem eltsH_E_unpack (D : CH) (X : List Nat) (XA : Fin 3 → Array Nat) (P : List Nat)
    (E : Nat → Nat) (hwords : D.words.length = D.nV)
    (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 3)
    (hpar : parOK (rowsG D.words) D.nV P = true)
    (hE0 : E 0 = pidn 3850 12)
    (hrec : ∀ v, 0 < v → v < D.nV →
      E v = pcomp 3850 12 (mask 12) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG D.words) v [])) 3) 0))
    (hX : ∀ i : Fin 3, Raw.unpack 3850 12 (getK X i 0) = XA i)
    (hXlt : ∀ i : Fin 3, ∀ j < 3850, pg 12 (mask 12) (getK X i 0) j < 3850)
    (hz : D.words.getD 0 [] = []) :
    ∀ v < D.nV, Raw.unpack 3850 12 (E v) = elaOf XA (D.words.getD v []) := by
  obtain ⟨hnV, hpar'⟩ := CFSG.KC.LQT.Cov.T.parOK_spec hpar
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [hE0, CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num), hz, eltsH_elaOf_nil]
    · have hpv : 0 < v := Nat.pos_of_ne_zero hv0
      obtain ⟨hparlt, hne, hwordeq⟩ := hpar' v hpv (by omega)
      have hmem : D.words.getD v [] ∈ D.words := eltsH_word_mem hwords hv
      have hlast : lastK (D.words.getD v []) < 3 := by
        refine eltsH_lastK_lt (fun l hl => hletters _ hmem l hl) ?_
        intro h0
        apply hne
        rw [eltsH_getRG_words, h0]
      have hmod : Nat.mod (lastK (D.words.getD v [])) 3 = lastK (D.words.getD v []) :=
        Nat.mod_eq_of_lt hlast
      let i : Fin 3 := ⟨Nat.mod (lastK (D.words.getD v [])) 3, Nat.mod_lt _ (by norm_num)⟩
      have hi : (i : Nat) = lastK (D.words.getD v []) := hmod
      have hpv' : getK P (v - 1) 0 < D.nV := by omega
      rw [hrec v hpv hv, eltsH_getRG_words]
      rw [← CFSG.KC.LQT.Cov.T.compA_unpack (n := 3850) (w := 12) (by norm_num) (hXlt i)]
      rw [ih (getK P (v - 1) 0) hparlt hpv', hX i]
      rw [← eltsH_elaOf_append]
      have hwordeq' := hwordeq
      simp only [eltsH_getRG_words] at hwordeq'
      have hw : D.words.getD (getK P (v - 1) 0) [] ++ [(i : Nat)] = D.words.getD v [] := by
        rw [hi]
        exact hwordeq'
      rw [hw]

private theorem eltsH_E_canon {nV : Nat} {WR : List (List (List Nat))} {E : Nat → Nat}
    {P X : List Nat} (hE0 : E 0 = pidn 3850 12)
    (hrec : ∀ v, 0 < v → v < nV →
      E v = pcomp 3850 12 (mask 12) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0)) :
    ∀ v < nV, E v >>> (3850 * 12) = 0 := by
  intro v hv
  by_cases hv0 : v = 0
  · subst hv0
    rw [hE0]
    exact CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)
  · rw [hrec v (Nat.pos_of_ne_zero hv0) hv]
    exact CFSG.KS.PF.pcomp_shr _ _ (by norm_num) (by norm_num)

private theorem eltsH_E_range {nV : Nat} {WR : List (List (List Nat))} {E : Nat → Nat}
    {P X : List Nat} (hE0 : E 0 = pidn 3850 12)
    (hrec : ∀ v, 0 < v → v < nV →
      E v = pcomp 3850 12 (mask 12) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0))
    (hXlt : ∀ i : Fin 3, ∀ j < 3850, pg 12 (mask 12) (getK X i 0) j < 3850)
    (hpar : ∀ v, 0 < v → v < nV → getK P (v - 1) 0 < v) :
    ∀ v < nV, ∀ i < 3850, pg 12 (mask 12) (E v) i < 3850 := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv i hi
    by_cases hv0 : v = 0
    · subst hv0
      rw [hE0, CFSG.KS.PF.pg_pidn (n := 3850) (w := 12) (by norm_num) (by norm_num) hi]
      exact hi
    · have hpv : 0 < v := Nat.pos_of_ne_zero hv0
      have hp : getK P (v - 1) 0 < v := hpar v hpv hv
      rw [hrec v hpv hv, CFSG.KS.PF.pg_pcomp (by norm_num) hi]
      have hqi : pg 12 (mask 12)
          (getK X (Nat.mod (lastK (getRG WR v [])) 3) 0) i < 3850 :=
        hXlt ⟨_, Nat.mod_lt _ (by norm_num)⟩ i hi
      exact ih (getK P (v - 1) 0) hp (by omega) _ hqi

private theorem eltsH_xwOf (D : CH) (i : Fin 3) : (ofCH D).xwOf i = D.xw.getD i [] := by
  rcases i with ⟨i, hi⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

private theorem eltsH_X_get {A B : Nat} (D : CH) {i : Nat} (hi : i < D.xw.length) :
    getK (D.xw.map (wPK 3850 12 A B)) i 0 = wPK 3850 12 A B (D.xw.getD i []) := by
  rw [CFSG.KC.LQT.Cov.Parse.getK_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem eltsH_X_unpack {A B : Nat}
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A) (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
    (hAr : ∀ i < 3850, pg 12 (mask 12) A i < 3850)
    (hBr : ∀ i < 3850, pg 12 (mask 12) B i < 3850) (D : CH) (hxw : D.xw.length = 3)
    (i : Fin 3) :
    Raw.unpack 3850 12 (getK (D.xw.map (wPK 3850 12 A B)) i 0) = (ofCH D).xa i := by
  rw [eltsH_X_get D (by rw [hxw]; exact i.2), (eltsH_wPK_unpack hA hB hAr hBr _).1]
  show wordArrP (D.xw.getD i []) = wordArrP ((ofCH D).xwOf i)
  rw [eltsH_xwOf]

private theorem eltsH_X_range {A B : Nat}
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A) (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
    (hAr : ∀ i < 3850, pg 12 (mask 12) A i < 3850)
    (hBr : ∀ i < 3850, pg 12 (mask 12) B i < 3850) (D : CH) (hxw : D.xw.length = 3)
    (i : Fin 3) : ∀ j < 3850, pg 12 (mask 12) (getK (D.xw.map (wPK 3850 12 A B)) i 0) j < 3850 := by
  rw [eltsH_X_get D (by rw [hxw]; exact i.2)]
  exact (eltsH_wPK_unpack hA hB hAr hBr _).2

private theorem eltsH_elaTab_get (D : CH) {v : Nat} (hv : v < D.nV) :
    (ofCH D).elaTab[v]! = elaOf (ofCH D).xa (D.words.getD v []) := by
  unfold CovData.elaTab
  rw [CFSG.Sporadic.Schreier.Tits.getElem!_ofFn_of_lt]
  · congr 2
    change (ofCH D).words[v]! = D.words.getD v []
    rw [show (ofCH D).words = D.words.toArray from rfl,
      CFSG.KC.LQT.Cov.T.toArray_getElem!_list]
  · exact hv

private theorem eltsH_ER_get {nV : Nat} {E : Nat → Nat} {v : Nat} (hv : v < nV) :
    getRG (rowsG ((List.range nV).map E)) v 0 = E v := by
  rw [CFSG.KC.LQT.Cov.T.getRG_rowsG, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_range]; exact hv),
    Option.map_some, Option.getD_some, List.getElem_range]

private def eltsH_GoodStep (D : CH) (E : Nat → Nat) (P X : List Nat) (v i : Nat) : Prop :=
  strictB (getRG (rowsG D.tgt) (3 * v + i) D.nV) (fun t =>
    CFSG.KC.LQT.S.allBs [Nat.blt t D.nV,
      Nat.blt (getRG (rowsG D.back) (3 * v + i) D.nV) D.nV,
      Bool.rec
        (Nat.beq (getRG (rowsG (List.map E (List.range D.nV))) t 0)
          (pcomp 3850 12 (mask 12) (getRG (rowsG (List.map E (List.range D.nV))) v 0)
            (getK X i 0)))
        true
        (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq t 0))
          (CFSG.KC.Ord.andB (Nat.beq (getRG (rowsG P) (t - 1) 0) v)
            (Nat.beq (Nat.mod (lastK (getRG (rowsG D.words) t [])) 3) i))),
      Nat.beq (getRG (rowsG D.tgt) (3 * (getRG (rowsG D.back) (3 * v + i) 0) + i) 0) v]) = true

section GoodStep

variable {D : CH} {E : Nat → Nat} {P X : List Nat}

private theorem eltsH_step_parts {v i : Nat} (hstep : eltsH_GoodStep D E P X v i) :
    Nat.blt (D.tgt.getD (3 * v + i) D.nV) D.nV = true ∧
    Nat.blt (D.back.getD (3 * v + i) D.nV) D.nV = true ∧
    Bool.rec (motive := fun _ => Bool)
        (Nat.beq ((List.map E (List.range D.nV)).getD (D.tgt.getD (3 * v + i) D.nV) 0)
          (pcomp 3850 12 (mask 12) ((List.map E (List.range D.nV)).getD v 0) (getK X i 0)))
        true
        (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (D.tgt.getD (3 * v + i) D.nV) 0))
          (CFSG.KC.Ord.andB (Nat.beq (P.getD (D.tgt.getD (3 * v + i) D.nV - 1) 0) v)
            (Nat.beq (Nat.mod (lastK (D.words.getD (D.tgt.getD (3 * v + i) D.nV) [])) 3)
              i))) = true ∧
    Nat.beq (D.tgt.getD (3 * D.back.getD (3 * v + i) 0 + i) 0) v = true := by
  have hm := hstep
  unfold eltsH_GoodStep at hm
  rw [CFSG.KS.PF.strictB_eqP, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true] at hm
  simp only [Bool.and_eq_true, CFSG.KC.LQT.Cov.T.getRG_rowsG] at hm
  exact hm

private theorem eltsH_step_prod
    (hrec : ∀ v, 0 < v → v < D.nV →
      E v = pcomp 3850 12 (mask 12) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG D.words) v [])) 3) 0))
    {v i : Nat} (hv : v < D.nV) (hstep : eltsH_GoodStep D E P X v i) :
    E (D.tgt.getD (3 * v + i) D.nV) = pcomp 3850 12 (mask 12) (E v) (getK X i 0) := by
  obtain ⟨ht, -, hprodRaw, -⟩ := eltsH_step_parts hstep
  have htlt : D.tgt.getD (3 * v + i) D.nV < D.nV := Nat.blt_eq.mp ht
  have hERt : (List.map E (List.range D.nV)).getD (D.tgt.getD (3 * v + i) D.nV) 0 =
      E (D.tgt.getD (3 * v + i) D.nV) := by
    rw [← CFSG.KC.LQT.Cov.T.getRG_rowsG]
    exact eltsH_ER_get htlt
  have hERv : (List.map E (List.range D.nV)).getD v 0 = E v := by
    rw [← CFSG.KC.LQT.Cov.T.getRG_rowsG]
    exact eltsH_ER_get hv
  cases hcond : (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (D.tgt.getD (3 * v + i) D.nV) 0))
      (CFSG.KC.Ord.andB (Nat.beq (P.getD (D.tgt.getD (3 * v + i) D.nV - 1) 0) v)
        (Nat.beq (Nat.mod (lastK (D.words.getD (D.tgt.getD (3 * v + i) D.nV) [])) 3) i)))
  · rw [hcond] at hprodRaw
    have := Nat.eq_of_beq_eq_true hprodRaw
    rw [hERt, hERv] at this
    exact this
  · rw [CFSG.KC.LQT.Cov.Parse.andB_eq', Bool.and_eq_true, CFSG.KC.LQT.Cov.Parse.notB_eq',
      Bool.not_eq_true'] at hcond
    obtain ⟨ht0, hcond⟩ := hcond
    rw [CFSG.KC.LQT.Cov.Parse.andB_eq', Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hcond
    obtain ⟨hpar, hlast⟩ := hcond
    have ht0' : D.tgt.getD (3 * v + i) D.nV ≠ 0 := by
      intro h0
      rw [h0] at ht0
      simp at ht0
    have htpos : 0 < D.tgt.getD (3 * v + i) D.nV := Nat.pos_of_ne_zero ht0'
    have hparent : getK P ((D.tgt.getD (3 * v + i) D.nV) - 1) 0 = v := by
      rw [CFSG.KC.LQT.Cov.Parse.getK_getD, hpar]
    rw [hrec (D.tgt.getD (3 * v + i) D.nV) htpos htlt, hparent, eltsH_getRG_words, hlast]

private theorem eltsH_step_check
    (hEunpack : ∀ v < D.nV,
      Raw.unpack 3850 12 (E v) = elaOf (ofCH D).xa (D.words.getD v []))
    (hX : ∀ i : Fin 3, Raw.unpack 3850 12 (getK X i 0) = (ofCH D).xa i)
    (hXlt : ∀ i : Fin 3, ∀ j < 3850, pg 12 (mask 12) (getK X i 0) j < 3850)
    {v i : Nat} (hv : v < D.nV) (hi : i < 3) (hstep : eltsH_GoodStep D E P X v i)
    (hprod : E (D.tgt.getD (3 * v + i) D.nV) = pcomp 3850 12 (mask 12) (E v) (getK X i 0)) :
    (ofCH D).tgtA[3 * v + i]! < (ofCH D).nV ∧ (ofCH D).backA[3 * v + i]! < (ofCH D).nV ∧
    eqA 3850 (ofCH D).elaTab[(ofCH D).tgtA[3 * v + i]!]!
      (compA 3850 (ofCH D).elaTab[v]! ((ofCH D).xa (fo i))) = true ∧
    ((ofCH D).tgtA[3 * (ofCH D).backA[3 * v + i]! + i]! == v) = true := by
  obtain ⟨ht, hb, -, hback⟩ := eltsH_step_parts hstep
  have htlt : D.tgt.getD (3 * v + i) D.nV < D.nV := Nat.blt_eq.mp ht
  have hblt : D.back.getD (3 * v + i) D.nV < D.nV := Nat.blt_eq.mp hb
  obtain ⟨-, htd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt htlt
  obtain ⟨-, hbd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt hblt
  have htA : (ofCH D).tgtA[3 * v + i]! = D.tgt.getD (3 * v + i) D.nV := by
    rw [show (ofCH D).tgtA = D.tgt.toArray from rfl, CFSG.KC.LQT.Cov.Perm.arr_get, ← htd]
  have hbA : (ofCH D).backA[3 * v + i]! = D.back.getD (3 * v + i) D.nV := by
    rw [show (ofCH D).backA = D.back.toArray from rfl, CFSG.KC.LQT.Cov.Perm.arr_get, ← hbd]
  have hfo : fo i = (⟨i, hi⟩ : Fin 3) := by
    simpa using (fo_val (⟨i, hi⟩ : Fin 3))
  refine ⟨by rw [htA]; exact htlt, by rw [hbA]; exact hblt, ?_, ?_⟩
  · rw [htA, eltsH_elaTab_get D htlt, eltsH_elaTab_get D hv, ← hEunpack _ htlt,
      ← hEunpack _ hv, hfo, ← hX ⟨i, hi⟩,
      CFSG.KC.LQT.Cov.T.compA_unpack (n := 3850) (w := 12) (by norm_num) (hXlt ⟨i, hi⟩),
      ← hprod]
    exact CFSG.KS.Raw.eqA_self _
  · rw [hbA, ← hbd, show (ofCH D).tgtA = D.tgt.toArray from rfl,
      CFSG.KC.LQT.Cov.Perm.arr_get, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true hback

private theorem eltsH_distinct_step
    (hdist : CFSG.KC.LQT.T2.distinctS ((List.range D.nV).map E) = true)
    (hEunpack : ∀ v < D.nV,
      Raw.unpack 3850 12 (E v) = elaOf (ofCH D).xa (D.words.getD v []))
    (hEcanon : ∀ v < D.nV, E v >>> (3850 * 12) = 0)
    {u v : Nat} (hu : u < D.nV) (hv : v < D.nV) :
    (!decide (u < v) || !eqA 3850 (ofCH D).elaTab[u]! (ofCH D).elaTab[v]!) = true := by
  by_cases huv : u < v
  · have hdec : decide (u < v) = true := decide_eq_true huv
    rw [hdec]
    simp only [Bool.not_true, Bool.false_or]
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro heq
    have hnd : ((List.range D.nV).map E).Nodup :=
      CFSG.KC.LQT.T2.nodup_of_distinctS hdist
    have hpoint : ∀ j < 3850,
        (Raw.unpack 3850 12 (E u))[j]! = (Raw.unpack 3850 12 (E v))[j]! := by
      intro j hj
      have := (CFSG.KC.Co2Mem.eqA_iff).1 heq j hj
      rwa [eltsH_elaTab_get D hu, eltsH_elaTab_get D hv, ← hEunpack u hu,
        ← hEunpack v hv] at this
    have hEuv : E u = E v := by
      apply CFSG.KS.PF.eq_of_fields (by norm_num) (hEcanon u hu) (hEcanon v hv)
      intro j hj
      rw [← CFSG.KS.Raw.Orb.unpack_get hj, ← CFSG.KS.Raw.Orb.unpack_get hj]
      exact hpoint j hj
    have hlenu : u < ((List.range D.nV).map E).length := by
      rw [List.length_map, List.length_range]; exact hu
    have hlenv : v < ((List.range D.nV).map E).length := by
      rw [List.length_map, List.length_range]; exact hv
    have helem : ((List.range D.nV).map E)[u]'hlenu = ((List.range D.nV).map E)[v]'hlenv := by
      simp [List.getElem_map, List.getElem_range, hEuv]
    have := (List.Nodup.getElem_inj_iff hnd).1 helem
    omega
  · simp [huv]

end GoodStep

private theorem eltsH_good_base {D : CH} {WR : List (List (List Nat))}
    {TG TB PR : List (List Nat)} {X : List Nat} {ER : List (List Nat)}
    (h : goodH D WR TG TB PR 3850 12 X ER = true) :
    0 < D.nV ∧ D.words.getD 0 [] = [] := by
  rw [goodH] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h0, hw0, -⟩ := h
  refine ⟨Nat.blt_eq.mp h0, ?_⟩
  have hlen : (D.words.getD 0 [1]).length = 0 := by
    rw [← CFSG.KC.LQT.Cov.Parse.getK_getD]
    exact CFSG.KC.LQT.Cov.Parse.lenK_length .. ▸ Nat.beq_eq.mp hw0
  rw [List.getD_eq_getElem?_getD] at hlen ⊢
  cases h : D.words[0]? with
  | none => simp [h] at hlen
  | some w => simpa [h] using hlen

private theorem eltsH_good_sound (D : CH) (E : Nat → Nat) (P X : List Nat)
    (hEunpack : ∀ v < D.nV,
      Raw.unpack 3850 12 (E v) = elaOf (ofCH D).xa (D.words.getD v []))
    (hEcanon : ∀ v < D.nV, E v >>> (3850 * 12) = 0)
    (hX : ∀ i : Fin 3, Raw.unpack 3850 12 (getK X i 0) = (ofCH D).xa i)
    (hXlt : ∀ i : Fin 3, ∀ j < 3850, pg 12 (mask 12) (getK X i 0) j < 3850)
    (hrec : ∀ v, 0 < v → v < D.nV →
      E v = pcomp 3850 12 (mask 12) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG D.words) v [])) 3) 0))
    (hdist : CFSG.KC.LQT.T2.distinctS ((List.range D.nV).map E) = true)
    (h : goodH D (rowsG D.words) (rowsG D.tgt) (rowsG D.back) (rowsG P) 3850 12 X
      (rowsG ((List.range D.nV).map E)) = true) :
    goodCheck (ofCH D) (ofCH D).elaTab = true := by
  obtain ⟨h0', hword0⟩ := eltsH_good_base h
  rw [goodH] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, hmain⟩ := h
  rw [CFSG.KC.LQT.Cov.Perm.allLtK_iff] at hmain
  rw [goodCheck]
  simp only [Bool.and_eq_true, decide_eq_true_eq, CFSG.Monster.B.Co2.allLt_iff, and_assoc]
  refine ⟨h0', ?_, ?_, ?_⟩
  · rw [show (ofCH D).words = D.words.toArray from rfl, CFSG.KC.LQT.Cov.T.toArray_getElem!_list,
      hword0]
    rfl
  · intro v hv i hi
    have hstep : eltsH_GoodStep D E P X v i := by
      unfold eltsH_GoodStep
      simpa [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
        Bool.and_true, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
        using (CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1 (hmain v hv) i hi
    exact eltsH_step_check hEunpack hX hXlt hv hi hstep (eltsH_step_prod hrec hv hstep)
  · intro u hu v hv
    exact eltsH_distinct_step hdist hEunpack hEcanon hu hv

private theorem eltsH_conj {D : CH} {E : Nat → Nat} {G Gi Y : Nat} {gw : List Nat} {b : Nat}
    (hb : b < D.nV)
    (hEunpack : ∀ v < D.nV,
      Raw.unpack 3850 12 (E v) = elaOf (ofCH D).xa (D.words.getD v []))
    (hG : Raw.unpack 3850 12 G = wordArrP gw)
    (hGr : ∀ i < 3850, pg 12 (mask 12) G i < 3850)
    (hperm : permOK 3850 12 (mask 12) (3850 * 12) G Gi = true)
    (hYr : ∀ i < 3850, pg 12 (mask 12) Y i < 3850)
    (he : pcomp 3850 12 (mask 12) (pcomp 3850 12 (mask 12) Gi Y) G = E b) :
    isInvA 3850 (wordArrP gw) (invCand 3850 (wordArrP gw)) = true ∧
    eqA 3850 (compA 3850 (compA 3850 (invCand 3850 (wordArrP gw)) (Raw.unpack 3850 12 Y))
      (wordArrP gw)) (ofCH D).elaTab[b]! = true := by
  have hGi : invCand 3850 (wordArrP gw) = Raw.unpack 3850 12 Gi := by
    rw [← hG]
    exact CFSG.KC.LQT.Cov.T.invCand_unpack hperm
  refine ⟨?_, ?_⟩
  · rw [hGi, ← hG]
    exact CFSG.KS.Raw.Orb.isInvA_unpack hperm
  · rw [hGi, ← hG, CFSG.KC.LQT.Cov.T.compA_unpack (by norm_num) hYr,
      CFSG.KC.LQT.Cov.T.compA_unpack (by norm_num) hGr, he, eltsH_elaTab_get D hb,
      ← hEunpack b hb]
    exact CFSG.KS.Raw.eqA_self _

private theorem eltsH_pair_sound {A B : Nat} (D : CH) (E : Nat → Nat)
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A) (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
    (hAr : ∀ i < 3850, pg 12 (mask 12) A i < 3850)
    (hBr : ∀ i < 3850, pg 12 (mask 12) B i < 3850)
    (hEunpack : ∀ v < D.nV,
      Raw.unpack 3850 12 (E v) = elaOf (ofCH D).xa (D.words.getD v []))
    (hElt : ∀ v < D.nV, ∀ j < 3850, pg 12 (mask 12) (E v) j < 3850)
    (r : List Nat × Nat × Nat)
    (h : pairH 3850 12 A B D (rowsG ((List.range D.nV).map E)) r = true) :
    pairCheck (ofCH D) (ofCH D).elaTab { gw := r.1, a := r.2.1, b := r.2.2 } = true := by
  rw [pairH] at h
  simp only [CFSG.KS.PF.strictB_eqP] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨hperm, ha, hb, he⟩ := h
  have ha' : r.2.1 < D.nV := Nat.blt_eq.mp ha
  have hb' : r.2.2 < D.nV := Nat.blt_eq.mp hb
  rw [eltsH_ER_get ha', eltsH_ER_get hb'] at he
  obtain ⟨hGu, hGr⟩ := eltsH_wPK_unpack hA hB hAr hBr r.1
  obtain ⟨hinv, heq⟩ := eltsH_conj hb' hEunpack hGu hGr hperm (hElt _ ha')
    (Nat.eq_of_beq_eq_true he)
  simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hinv, ha'⟩, hb'⟩, ?_⟩
  rwa [eltsH_elaTab_get D ha', ← hEunpack _ ha']

private theorem eltsH_anchor_sound {A B : Nat} (D : CH) (E : Nat → Nat)
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A) (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
    (hAr : ∀ i < 3850, pg 12 (mask 12) A i < 3850)
    (hBr : ∀ i < 3850, pg 12 (mask 12) B i < 3850)
    (hEunpack : ∀ v < D.nV,
      Raw.unpack 3850 12 (E v) = elaOf (ofCH D).xa (D.words.getD v []))
    (r : List Nat × Nat)
    (h : anchorH 3850 12 A B (wPK 3850 12 A B [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]) D
      (rowsG ((List.range D.nV).map E)) r = true) :
    anchorCheck (ofCH D) (ofCH D).elaTab { gw := r.1, a := 0, b := r.2 } = true := by
  rw [anchorH] at h
  simp only [CFSG.KS.PF.strictB_eqP] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨hperm, hb, he⟩ := h
  have hb' : r.2 < D.nV := Nat.blt_eq.mp hb
  rw [eltsH_ER_get hb'] at he
  obtain ⟨hGu, hGr⟩ := eltsH_wPK_unpack hA hB hAr hBr r.1
  obtain ⟨hCu, hCr⟩ := eltsH_wPK_unpack hA hB hAr hBr
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  obtain ⟨hinv, heq⟩ := eltsH_conj hb' hEunpack hGu hGr hperm hCr (Nat.eq_of_beq_eq_true he)
  simp only [anchorCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hinv, hb'⟩, ?_⟩
  rw [hCu] at heq
  exact heq

theorem covHA_sound {cs : List Char} {D : CH} (hp : parseH cs = some D)
    (hxw : D.xw.length = 3) (hwords : D.words.length = D.nV)
    (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) {P : List ℕ} {nV0 A B : ℕ}
    (hA : hsStrongArrs[0]! = CFSG.KS.Raw.unpack 3850 12 A)
    (hB : hsStrongArrs[1]! = CFSG.KS.Raw.unpack 3850 12 B)
    (h : covHA 3850 12 A B cs P nV0 = true) :
    goodCheck (ofCH D) (ofCH D).elaTab = true ∧
      (ofCH D).pairs.all (pairCheck (ofCH D) (ofCH D).elaTab) = true ∧
      (ofCH D).anchors.all (anchorCheck (ofCH D) (ofCH D).elaTab) = true ∧
      D.nV = nV0 ∧ 0 < D.nV := by
  rw [covHA, hp] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, hnv0, hpermA, hpermB, hpar, hbuild⟩ := h
  simp only [CFSG.KS.PF.strictB_eqP] at hbuild
  have hAr : ∀ i < 3850, pg 12 (mask 12) A i < 3850 :=
    fun i hi => ((CFSG.KC.LQT.Cov.T.perm_facts hpermA).1 i hi).1
  have hBr : ∀ i < 3850, pg 12 (mask 12) B i < 3850 :=
    fun i hi => ((CFSG.KC.LQT.Cov.T.perm_facts hpermB).1 i hi).1
  obtain ⟨E, hk, hE0, hrec⟩ :=
    eltsH_build_exists 3850 12 (rowsG D.words) D.nV _ P _ hpar hbuild
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hgood, hdist, hpairs, hanchors⟩ := hk
  obtain ⟨hnV, hz⟩ := eltsH_good_base hgood
  have hX := eltsH_X_unpack hA hB hAr hBr D hxw
  have hXlt := eltsH_X_range hA hB hAr hBr D hxw
  have hEunpack := eltsH_E_unpack D _ (ofCH D).xa P E hwords hletters hpar hE0 hrec hX hXlt hz
  have hElt := eltsH_E_range hE0 hrec hXlt
    (fun v hv hlt => ((CFSG.KC.LQT.Cov.T.parOK_spec hpar).2 v hv hlt).1)
  refine ⟨eltsH_good_sound D E P _ hEunpack (eltsH_E_canon hE0 hrec) hX hXlt hrec hdist hgood,
    ?_, ?_, Nat.beq_eq.mp hnv0, hnV⟩
  · rw [show (ofCH D).pairs =
        D.pairs.map (fun p => ({ gw := p.1, a := p.2.1, b := p.2.2 } : Rec)) from rfl,
      List.all_map]
    apply List.all_eq_true.2
    intro r hr
    exact eltsH_pair_sound D E hA hB hAr hBr hEunpack hElt r
      ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hpairs r hr)
  · rw [show (ofCH D).anchors =
        D.anchors.map (fun p => ({ gw := p.1, a := 0, b := p.2 } : Rec)) from rfl,
      List.all_map]
    apply List.all_eq_true.2
    intro r hr
    exact eltsH_anchor_sound D E hA hB hAr hBr hEunpack r
      ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hanchors r hr)

end CFSG.KC.LQT.Cov.H

end
