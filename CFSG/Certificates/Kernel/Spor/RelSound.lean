module

public import Certificates.Data.Kernel.Spor.Rel
import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
import CFSG.Certificates.Kernel.Spor.PK.Perm.Make

public section

namespace CFSG.KS.Rel

open CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Th.Native CFSG.KC.Enum CFSG.KS
  CFSG.KS.Mathieu CFSG.KS.PK

private def Good (n : Nat) (t : Table) : Prop := t.size = n ∧ ∀ x ∈ t.toList, x.toNat < n

private theorem lenU_eq' (l : List UInt32) : lenU l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show Nat.succ (lenU l) = l.length + 1
    rw [ih]

private theorem allLtU_iff' (n : Nat) (l : List UInt32) :
    allLtU n l = true ↔ ∀ x ∈ l, x.toNat < n := by
  induction l with
  | nil => exact ⟨fun _ x hx => absurd hx (by simp), fun _ => rfl⟩
  | cons x l ih =>
    have h : allLtU n (x :: l) = (Nat.blt x.toNat n && allLtU n l) := by
      rw [← bAnd_eq]
      rfl
    rw [h, Bool.and_eq_true, Nat.blt_eq, ih]
    simp

private theorem good_of_tabOK {n : Nat} {t : Table} (h : tabOK n t = true) : Good n t := by
  unfold tabOK at h
  rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, lenU_eq', allLtU_iff'] at h
  exact ⟨by simpa using h.1, h.2⟩

private theorem Good.ap_lt {n : Nat} {t : Table} (h : Good n t) {i : Nat} (hi : i < n) :
    ap t i < n := by
  unfold ap
  rw [getElem!_pos t i (by rw [h.1]; exact hi)]
  exact h.2 _ (by simp)

private theorem packU_tab {n w : Nat} {t : Table} (h : Good n t) (hw : n < 2 ^ w) :
    packU w t.toList = enc w (ap t) n := by
  have hlen : t.toList.length = n := by simpa using h.1
  rw [packU_eq (fun x hx => Nat.lt_trans (h.2 x hx) hw), hlen]
  apply enc_congr
  intro i hi
  have hi' : i < t.size := by rw [h.1]; exact hi
  simp [ap, List.getD_eq_getElem?_getD, hi', getElem!_pos t i hi']

private theorem letter_packU (w : Nat) (α αi β βi : Table) (l : Nat × Bool) :
    letter (packU w α.toList) (packU w αi.toList) (packU w β.toList) (packU w βi.toList) l =
      packU w (letterTab α αi β βi l).toList := by
  obtain ⟨i, b⟩ := l
  show nIf(Nat.beq i 0, nIf(b, _, _), nIf(b, _, _)) = _
  simp only [nIf_eq, Nat.beq_eq, letterTab]
  by_cases hi : i = 0 <;> cases b <;> simp [hi]

private theorem good_letterTab {n : Nat} {α αi β βi : Table} (hα : Good n α) (hαi : Good n αi)
    (hβ : Good n β) (hβi : Good n βi) (l : Nat × Bool) : Good n (letterTab α αi β βi l) := by
  unfold letterTab
  split
  · split
    · exact hα
    · exact hαi
  · split
    · exact hβ
    · exact hβi

private def wordAp (α αi β βi : Table) (v : List (Nat × Bool)) (x : Nat) : Nat :=
  v.foldr (fun l y => ap (letterTab α αi β βi l) y) x

private theorem wordAp_lt {n : Nat} {α αi β βi : Table} (hα : Good n α) (hαi : Good n αi)
    (hβ : Good n β) (hβi : Good n βi) (v : List (Nat × Bool)) {x : Nat} (hx : x < n) :
    wordAp α αi β βi v x < n := by
  induction v with
  | nil => exact hx
  | cons l v ih => exact (good_letterTab hα hαi hβ hβi l).ap_lt ih

private theorem wordP_eq {n w : Nat} {α αi β βi : Table} (hn : n < 2 ^ 24) (hw : n < 2 ^ w)
    (hα : Good n α) (hαi : Good n αi) (hβ : Good n β) (hβi : Good n βi) (v : List (Nat × Bool)) :
    wordP n w (mask w) (pidn n w) (packU w α.toList) (packU w αi.toList) (packU w β.toList)
        (packU w βi.toList) v = enc w (wordAp α αi β βi v) n := by
  have hn32 : n < 2 ^ 32 := Nat.lt_trans hn (by decide)
  induction v with
  | nil =>
    show pidn n w = _
    rw [pidn_eq (Nat.le_of_lt hn) (Nat.le_of_lt hw)]
    rfl
  | cons l v ih =>
    have e : wordP n w (mask w) (pidn n w) (packU w α.toList) (packU w αi.toList)
        (packU w β.toList) (packU w βi.toList) (l :: v) =
        pcomp n w (mask w) (letter (packU w α.toList) (packU w αi.toList) (packU w β.toList)
          (packU w βi.toList) l) (wordP n w (mask w) (pidn n w) (packU w α.toList)
            (packU w αi.toList) (packU w β.toList) (packU w βi.toList) v) := by
      show strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e, ih, pcomp_eq hn32, letter_packU,
      packU_tab (good_letterTab hα hαi hβ hβi l) hw]
    refine enc_congr fun i hi => ?_
    have hv := wordAp_lt hα hαi hβ hβi v hi
    have hL := good_letterTab hα hαi hβ hβi l
    rw [fd_enc (fun x hx => Nat.lt_trans (wordAp_lt hα hαi hβ hβi v hx) hw) hi,
      fd_enc (fun x hx => Nat.lt_trans (hL.ap_lt hx) hw) hv]
    rfl

private theorem relsId_iff (n w m idn A Ai B Bi : Nat) (rels : List (List (Nat × Bool))) :
    relsId n w m idn A Ai B Bi rels = true ↔ ∀ v ∈ rels, wordP n w m idn A Ai B Bi v = idn := by
  induction rels with
  | nil => simp [relsId]
  | cons v rels ih =>
    have h : relsId n w m idn A Ai B Bi (v :: rels) =
        bAnd(Nat.beq (wordP n w m idn A Ai B Bi v) idn, relsId n w m idn A Ai B Bi rels) := rfl
    rw [h, bAnd_eq, Bool.and_eq_true, Nat.beq_eq, ih, List.forall_mem_cons]

private theorem ap_wordTab {n : Nat} {α αi β βi : Table} (hn : n < 2 ^ 32) (hα : Good n α)
    (hαi : Good n αi) (hβ : Good n β) (hβi : Good n βi) (v : List (Nat × Bool)) :
    (wordTab n α αi β βi v).size = n ∧
      ∀ i < n, ap (wordTab n α αi β βi v) i = wordAp α αi β βi v i := by
  induction v with
  | nil =>
    refine ⟨by simp [wordTab, idT], fun i hi => ?_⟩
    show ((idT n)[i]!).toNat = i
    rw [getElem!_pos (idT n) i (by simpa [idT] using hi)]
    simp [idT, Nat.mod_eq_of_lt (Nat.lt_trans hi hn)]
  | cons l v ih =>
    have e : wordTab n α αi β βi (l :: v) =
        compT n (letterTab α αi β βi l) (wordTab n α αi β βi v) := rfl
    rw [e]
    refine ⟨by simp [compT], fun i hi => ?_⟩
    show ((compT n _ _)[i]!).toNat = ap (letterTab α αi β βi l) (wordAp α αi β βi v i)
    rw [getElem!_pos (compT n _ _) i (by simpa [compT] using hi), ← ih.2 i hi]
    simp [compT, ap]

theorem relK_sound {n w : Nat} {α αi β βi : Array UInt32} {rels : List (List (Nat × Bool))}
    (h : relK n w α αi β βi rels = true) : relCheck n α αi β βi rels = true := by
  simp only [relK, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hn, hm, hα, hαi, hβ, hβi, hrel⟩ := h
  have hα := good_of_tabOK hα
  have hαi := good_of_tabOK hαi
  have hβ := good_of_tabOK hβ
  have hβi := good_of_tabOK hβi
  rw [mask_eq] at hm
  have hw : n < 2 ^ w := by omega
  have hn24 : n < 2 ^ 24 := by simpa using hn
  have hn32 : n < 2 ^ 32 := Nat.lt_trans hn24 (by decide)
  have hid : pidn n w = enc w (fun i => i) n := pidn_eq (Nat.le_of_lt hn24) (Nat.le_of_lt hw)
  have hrel' := (relsId_iff _ _ _ _ _ _ _ _ rels).1 hrel
  unfold relCheck
  rw [List.all_eq_true]
  intro v hv
  rw [beq_iff_eq]
  have hP := hrel' v hv
  rw [wordP_eq hn24 hw hα hαi hβ hβi, hid] at hP
  obtain ⟨hsz, hap⟩ := ap_wordTab hn32 hα hαi hβ hβi v
  have hidsz : (idT n).size = n := by simp [idT]
  refine Array.ext (by rw [hsz, hidsz]) fun i hi hi' => ?_
  have hin : i < n := by rwa [hsz] at hi
  have h1 : wordAp α αi β βi v i = i := by
    have := congrArg (fun x => fd w x i) hP
    rwa [fd_enc (fun x hx => Nat.lt_trans (wordAp_lt hα hαi hβ hβi v hx) hw) hin,
      fd_enc (fun x hx => Nat.lt_trans hx hw) hin] at this
  have h2 := hap i hin
  unfold ap at h2
  rw [getElem!_pos _ i hi, h1] at h2
  apply UInt32.toNat_inj.1
  rw [h2]
  simp [idT, Nat.mod_eq_of_lt (Nat.lt_trans hin hn32)]

end CFSG.KS.Rel

end
