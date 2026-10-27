module

public import Certificates.Data.Kernel.Spor.MatK
public import CFSG.Sporadic.SuzOddCore.GraphArraysCheckInputs
import CFSG.Certificates.Kernel.Common.Loop
import CFSG.Certificates.Kernel.MtxKSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import Init.Data.String.Slice
import Init.Data.String.Search
import Batteries.Data.String.Lemmas
import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KC.MatK

open CFSG.Sporadic.SuzOddCore CFSG.KC.Mtx CFSG.KC.Enum CFSG.KC.SurjK CFSG.KS

private theorem matRun_cons_zero (h₀ h₁ h₂ h₃ cnt : Nat) (ch : Char) (cs : List Char)
    (k v dg cc : Nat) :
    matRun h₀ h₁ h₂ h₃ cnt (ch :: cs) 0 k v dg cc =
      strictB (Char.toNat ch) (fun c =>
        bIf(Nat.blt (digV c) 10,
          strictB (Nat.add (Nat.mul v 10) (digV c)) (fun v' =>
            matRun h₀ h₁ h₂ h₃ cnt cs 0 k v' 1 cc),
          bIf(Nat.beq c 10,
            bIf(Nat.beq dg 1,
              bAnd(hdrOK h₀ h₁ h₂ h₃ k v,
                bAnd(Nat.beq (Nat.succ k) 4, matRun h₀ h₁ h₂ h₃ cnt cs 1 0 0 0 0)),
              bAnd(Nat.beq k 4, matRun h₀ h₁ h₂ h₃ cnt cs 1 0 0 0 0)),
            bIf(wsB c,
              bIf(Nat.beq dg 1,
                bAnd(hdrOK h₀ h₁ h₂ h₃ k v,
                  matRun h₀ h₁ h₂ h₃ cnt cs 0 (Nat.succ k) 0 0 0),
                matRun h₀ h₁ h₂ h₃ cnt cs 0 k 0 0 0),
              false)))) := rfl

private theorem matRun_cons_one (h₀ h₁ h₂ h₃ cnt : Nat) (ch : Char) (cs : List Char)
    (k v dg cc : Nat) :
    matRun h₀ h₁ h₂ h₃ cnt (ch :: cs) 1 k v dg cc =
      strictB (Char.toNat ch) (fun c =>
        bIf(wsB c,
          matRun h₀ h₁ h₂ h₃ cnt cs 1 0 0 0 cc,
          bIf(Nat.blt c 48, false,
            bIf(Nat.blt c 51,
              strictB (Nat.succ cc) (fun cc' =>
                matRun h₀ h₁ h₂ h₃ cnt cs 1 0 0 0 cc'),
              false)))) := rfl

private theorem matRun_nil_zero (h₀ h₁ h₂ h₃ cnt : Nat) (k v dg cc : Nat) :
    matRun h₀ h₁ h₂ h₃ cnt [] 0 k v dg cc = false := rfl

private theorem matRun_nil_one (h₀ h₁ h₂ h₃ cnt : Nat) (k v dg cc : Nat) :
    matRun h₀ h₁ h₂ h₃ cnt [] 1 k v dg cc = Nat.beq cc cnt := rfl

private theorem runT_nil (n : Nat) (tok : Nat → Nat → Bool) (k v dg : Nat) :
    runT n tok [] k v dg =
      bIf(Nat.beq dg 1, bAnd(tok k v, Nat.beq (Nat.succ k) (Nat.add n 4)),
        Nat.beq k (Nat.add n 4)) := rfl

private theorem runT_cons (n : Nat) (tok : Nat → Nat → Bool) (ch : Char) (cs : List Char)
    (k v dg : Nat) :
    runT n tok (ch :: cs) k v dg =
      strictB (Char.toNat ch) (fun c =>
        bIf(Nat.blt (digV c) 10,
          runT n tok cs k (Nat.add (Nat.mul v 10) (digV c)) 1,
          bIf(wsB c,
            bIf(Nat.beq dg 1,
              bAnd(tok k v, runT n tok cs (Nat.succ k) 0 0),
              runT n tok cs k 0 0),
            false))) := rfl

private theorem bAnd_assoc (a b c : Bool) :
    bAnd(bAnd(a, b), c) = bAnd(a, bAnd(b, c)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (c && t || !c && e) := by
  cases c <;> cases t <;> cases e <;> rfl

private theorem nbeq (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])

private theorem toNat_eq {c d : Char} : c = d ↔ c.toNat = d.toNat := Char.toNat_inj.symm

private theorem wsB_eq (c : Char) : wsB c.toNat = c.isWhitespace := by
  unfold wsB Char.isWhitespace
  simp only [bIf_eq, nbeq, toNat_eq]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  by_cases a : c.toNat = 32 <;> by_cases b : c.toNat = 10 <;> by_cases d : c.toNat = 9 <;>
    by_cases f : c.toNat = 13 <;> simp [a, b, d, f]

private def isMatDigit (c : Char) : Bool := c == '0' || c == '1' || c == '2'

private theorem isMatDigit_iff (c : Char) :
    isMatDigit c = true ↔ c = '0' ∨ c = '1' ∨ c = '2' := by
  unfold isMatDigit
  rw [Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

private theorem isMatDigit_eq_false_of_wsB {c : Char} (h : wsB c.toNat = true) :
    isMatDigit c = false := by
  rw [wsB_eq] at h
  cases hd : isMatDigit c with
  | false => rfl
  | true =>
      exfalso
      rcases (isMatDigit_iff c).1 hd with rfl | rfl | rfl <;> exact absurd h (by decide)

private theorem wsB_eq_false_of_isMatDigit {c : Char} (h : isMatDigit c = true) :
    wsB c.toNat = false := by
  rcases (isMatDigit_iff c).1 h with rfl | rfl | rfl <;> decide

private theorem matRun_digits {h₀ h₁ h₂ h₃ cnt : Nat} {cs : List Char} {k v dg cc : Nat}
    (h : matRun h₀ h₁ h₂ h₃ cnt cs 1 k v dg cc = true) :
    (∀ c ∈ cs, isMatDigit c = true ∨ wsB c.toNat = true) ∧
      cc + cs.countP isMatDigit = cnt := by
  induction cs generalizing k v dg cc with
  | nil =>
      rw [matRun_nil_one] at h
      have hc := Nat.eq_of_beq_eq_true h
      refine ⟨by simp, ?_⟩
      simpa using hc
  | cons ch cs ih =>
      rw [matRun_cons_one] at h
      rw [PackFld.strictB_eqP] at h
      by_cases hw : wsB (Char.toNat ch) = true
      · rw [hw] at h
        obtain ⟨hmem, hcount⟩ := ih (cc := cc) h
        have hd : isMatDigit ch = false := isMatDigit_eq_false_of_wsB hw
        refine ⟨?_, ?_⟩
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact Or.inr hw
          · exact hmem c hc
        · rw [List.countP_cons, hd]
          simpa using hcount
      · have hw' : wsB (Char.toNat ch) = false := Bool.eq_false_iff.2 hw
        rw [hw'] at h
        by_cases h48 : Nat.blt (Char.toNat ch) 48 = true
        · rw [h48] at h
          exact absurd h Bool.false_ne_true
        · have h48' : Nat.blt (Char.toNat ch) 48 = false := Bool.eq_false_iff.2 h48
          rw [h48'] at h
          by_cases h51 : Nat.blt (Char.toNat ch) 51 = true
          · rw [h51] at h
            rw [PackFld.strictB_eqP] at h
            obtain ⟨hmem, hcount⟩ := ih (cc := cc + 1) h
            have h1 : 48 ≤ Char.toNat ch := by
              have hlt : ¬ Char.toNat ch < 48 := by
                intro hlt
                have htrue : Nat.blt (Char.toNat ch) 48 = true := by
                  rw [Nat.blt_eq]
                  exact hlt
                exact h48 htrue
              omega
            have h2 : Char.toNat ch < 51 := by
              have := h51
              rw [Nat.blt_eq] at this
              exact this
            have hcrange : Char.toNat ch = 48 ∨ Char.toNat ch = 49 ∨
                Char.toNat ch = 50 := by omega
            have hd : isMatDigit ch = true := by
              rcases hcrange with hc | hc | hc
              · have hch : ch = '0' := Char.toNat_inj.1 (by simpa using hc)
                simp [isMatDigit, hch]
              · have hch : ch = '1' := Char.toNat_inj.1 (by simpa using hc)
                simp [isMatDigit, hch]
              · have hch : ch = '2' := Char.toNat_inj.1 (by simpa using hc)
                simp [isMatDigit, hch]
            refine ⟨?_, ?_⟩
            · intro c hc
              rcases List.mem_cons.1 hc with rfl | hc
              · exact Or.inl hd
              · exact hmem c hc
            · rw [List.countP_cons]
              simp [hd]
              omega
          · have h51' : Nat.blt (Char.toNat ch) 51 = false := Bool.eq_false_iff.2 h51
            rw [h51'] at h
            exact absurd h Bool.false_ne_true

private theorem exists_split_of_phase0 {h₀ h₁ h₂ h₃ cnt : Nat} :
    ∀ {cs : List Char} {k v dg cc : Nat},
      matRun h₀ h₁ h₂ h₃ cnt cs 0 k v dg cc = true →
      ∃ line rest, cs = line ++ '\n' :: rest ∧ ∀ c ∈ line, c ≠ '\n' := by
  intro cs
  induction cs with
  | nil =>
      intro k v dg cc h
      rw [matRun_nil_zero] at h
      exact absurd h Bool.false_ne_true
  | cons ch cs ih =>
      intro k v dg cc h
      rw [matRun_cons_zero, PackFld.strictB_eqP] at h
      by_cases hnl : Nat.beq (Char.toNat ch) 10 = true
      · have hch : ch = '\n' := Char.toNat_inj.1 (by simpa using Nat.eq_of_beq_eq_true hnl)
        subst hch
        exact ⟨[], cs, rfl, by simp⟩
      · have hnl' : Nat.beq (Char.toNat ch) 10 = false := Bool.eq_false_iff.2 hnl
        rw [hnl'] at h
        have hch : ch ≠ '\n' := by
          rintro rfl
          have h10 : Nat.beq (Char.toNat '\n') 10 = true := by decide
          exact hnl h10
        by_cases hdig : Nat.blt (digV (Char.toNat ch)) 10 = true
        · rw [hdig] at h
          rw [PackFld.strictB_eqP] at h
          obtain ⟨line, rest, e, hno⟩ := ih (k := k)
            (v := Nat.add (Nat.mul v 10) (digV (Char.toNat ch))) (dg := 1) (cc := cc) h
          exact ⟨ch :: line, rest, by rw [e]; rfl, by
            intro c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · exact hch
            · exact hno c hc⟩
        · have hdig' : Nat.blt (digV (Char.toNat ch)) 10 = false :=
            Bool.eq_false_iff.2 hdig
          rw [hdig'] at h
          by_cases hws : wsB (Char.toNat ch) = true
          · rw [hws] at h
            by_cases hdg : Nat.beq dg 1 = true
            · rw [hdg] at h
              obtain ⟨-, hrun⟩ := (CFSG.KS.bAnd_iff _ _).1 h
              obtain ⟨line, rest, e, hno⟩ :=
                ih (k := Nat.succ k) (v := 0) (dg := 0) (cc := 0) hrun
              exact ⟨ch :: line, rest, by rw [e]; rfl, by
                intro c hc
                rcases List.mem_cons.1 hc with rfl | hc
                · exact hch
                · exact hno c hc⟩
            · have hdg' : Nat.beq dg 1 = false := Bool.eq_false_iff.2 hdg
              rw [hdg'] at h
              obtain ⟨line, rest, e, hno⟩ := ih (k := k) (v := 0) (dg := 0) (cc := 0) h
              exact ⟨ch :: line, rest, by rw [e]; rfl, by
                intro c hc
                rcases List.mem_cons.1 hc with rfl | hc
                · exact hch
                · exact hno c hc⟩
          · have hws' : wsB (Char.toNat ch) = false := Bool.eq_false_iff.2 hws
            rw [hws'] at h
            exact absurd h Bool.false_ne_true

private theorem matRun_nl_zero (h₀ h₁ h₂ h₃ cnt : Nat) (rest : List Char) (k v dg cc : Nat) :
    matRun h₀ h₁ h₂ h₃ cnt ('\n' :: rest) 0 k v dg cc =
      bAnd(runT 0 (hdrOK h₀ h₁ h₂ h₃) [] k v dg,
        matRun h₀ h₁ h₂ h₃ cnt rest 1 0 0 0 0) := by
  rw [matRun_cons_zero, runT_nil, PackFld.strictB_eqP]
  cases hdg : Nat.beq dg 1
  · rfl
  · exact (bAnd_assoc _ _ _).symm

private theorem matRun_split {h₀ h₁ h₂ h₃ cnt : Nat} :
    ∀ {line rest : List Char}, (∀ c ∈ line, c ≠ '\n') →
    ∀ k v dg cc,
      matRun h₀ h₁ h₂ h₃ cnt (line ++ '\n' :: rest) 0 k v dg cc = true →
      runT 0 (hdrOK h₀ h₁ h₂ h₃) line k v dg = true ∧
        matRun h₀ h₁ h₂ h₃ cnt rest 1 0 0 0 0 = true := by
  intro line
  induction line with
  | nil =>
      intro rest _ k v dg cc h
      rw [List.nil_append, matRun_nl_zero] at h
      exact (CFSG.KS.bAnd_iff _ _).1 h
  | cons ch line ih =>
      intro rest hno k v dg cc h
      have hch : ch ≠ '\n' := hno ch (List.mem_cons_self ..)
      have hno' : ∀ c ∈ line, c ≠ '\n' := fun c hc =>
        hno c (List.mem_cons_of_mem _ hc)
      rw [List.cons_append, matRun_cons_zero, PackFld.strictB_eqP] at h
      have hnl : Nat.beq (Char.toNat ch) 10 = false := by
        cases e : Nat.beq (Char.toNat ch) 10
        · rfl
        · exact absurd (Char.toNat_inj.1 (by simpa using Nat.eq_of_beq_eq_true e)) hch
      rw [hnl] at h
      by_cases hdig : Nat.blt (digV (Char.toNat ch)) 10 = true
      · rw [hdig] at h
        rw [PackFld.strictB_eqP] at h
        obtain ⟨hrun, hrest⟩ := ih hno' (k := k)
          (v := Nat.add (Nat.mul v 10) (digV (Char.toNat ch))) (dg := 1) (cc := cc) h
        refine ⟨?_, hrest⟩
        rw [runT_cons, PackFld.strictB_eqP, hdig]
        exact hrun
      · have hdig' : Nat.blt (digV (Char.toNat ch)) 10 = false :=
          Bool.eq_false_iff.2 hdig
        rw [hdig'] at h
        by_cases hws : wsB (Char.toNat ch) = true
        · rw [hws] at h
          by_cases hdg : Nat.beq dg 1 = true
          · rw [hdg] at h
            obtain ⟨hhdr, hrun0⟩ := (CFSG.KS.bAnd_iff _ _).1 h
            obtain ⟨hrun, hrest⟩ :=
              ih hno' (k := Nat.succ k) (v := 0) (dg := 0) (cc := 0) hrun0
            refine ⟨?_, hrest⟩
            rw [runT_cons, PackFld.strictB_eqP, hdig', hws, hdg]
            exact (CFSG.KS.bAnd_iff _ _).2 ⟨hhdr, hrun⟩
          · have hdg' : Nat.beq dg 1 = false := Bool.eq_false_iff.2 hdg
            rw [hdg'] at h
            obtain ⟨hrun, hrest⟩ := ih hno' (k := k) (v := 0) (dg := 0) (cc := 0) h
            refine ⟨?_, hrest⟩
            rw [runT_cons, PackFld.strictB_eqP, hdig', hws, hdg']
            exact hrun
        · have hws' : wsB (Char.toNat ch) = false := Bool.eq_false_iff.2 hws
          rw [hws'] at h
          exact absurd h Bool.false_ne_true

private theorem filter_not_ws_eq_filter_digit {cs : List Char}
    (h : ∀ c ∈ cs, isMatDigit c = true ∨ wsB c.toNat = true) :
    cs.filter (fun c => !c.isWhitespace) = cs.filter isMatDigit := by
  apply List.filter_congr
  intro c hc
  rcases h c hc with hd | hw
  · have hw' : wsB c.toNat = false := wsB_eq_false_of_isMatDigit hd
    rw [wsB_eq] at hw'
    simp [hw', hd]
  · have hd' : isMatDigit c = false := isMatDigit_eq_false_of_wsB hw
    rw [wsB_eq] at hw
    rw [hw, hd']
    simp

private theorem matDigits_ofList_split {line rest : List Char}
    (hno : ∀ c ∈ line, c ≠ '\n') :
    matDigits (String.ofList (line ++ '\n' :: rest)) =
      rest.filter (fun c => !c.isWhitespace) := by
  unfold matDigits
  rw [String.toList_ofList, List.dropWhile_append_of_pos]
  · simp
  · intro c hc
    simpa [bne_iff_ne] using hno c hc

private theorem mtxTokens_append_nl (line rest : List Char) :
    mtxTokens (String.ofList (line ++ '\n' :: rest)) =
      mtxTokens (String.ofList line) ++ mtxTokens (String.ofList rest) := by
  unfold mtxTokens
  simp only [String.splitToList_of_valid, String.toList_ofList]
  rw [List.splitOnP_append_cons _ _ (by decide), List.map_append, List.filter_append]

private theorem hdrOK_eq {h₀ h₁ h₂ h₃ k v : Nat} (hk : k < 4)
    (h : hdrOK h₀ h₁ h₂ h₃ k v = true) :
    v = [h₀, h₁, h₂, h₃].getD k 0 := by
  unfold hdrOK at h
  rw [CFSG.KS.bAnd_iff] at h
  have hv := Nat.eq_of_beq_eq_true h.2
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl | rfl | rfl
  · change v = h₀
    exact hv
  · change v = h₁
    exact hv
  · change v = h₂
    exact hv
  · change v = h₃
    exact hv

private theorem header_take {h₀ h₁ h₂ h₃ : Nat} {toks : List String}
    (hl : toks.length = 4)
    (ht : ∀ i < 4, hdrOK h₀ h₁ h₂ h₃ i (tokenVal (toks.getD i "")) = true) :
    (toks.take 4).map tokenVal = [h₀, h₁, h₂, h₃] := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    have hi : i < 4 := by simpa using h2
    have hval := hdrOK_eq hi (ht i hi)
    rw [List.getElem_map (h := h1)]
    rw [← List.getElem_take' (xs := toks) (i := i) (j := 4) (by rw [hl]; exact hi) hi]
    rw [← CFSG.KC.Mtx.getD_of_lt (l := toks) "" (by rw [hl]; exact hi)]
    rw [hval]
    exact CFSG.KC.Mtx.getD_of_lt 0 h2

theorem matK_sound {cs : List Char} {h₀ h₁ h₂ h₃ cnt : Nat}
    (h : matK cs h₀ h₁ h₂ h₃ cnt = true) :
    matHeader (String.ofList cs) = [h₀, h₁, h₂, h₃] ∧
      (matDigits (String.ofList cs)).length = cnt ∧
      ∀ c ∈ matDigits (String.ofList cs), c = '0' ∨ c = '1' ∨ c = '2' := by
  change matRun h₀ h₁ h₂ h₃ cnt cs 0 0 0 0 0 = true at h
  obtain ⟨line, rest, rfl, hno⟩ := exists_split_of_phase0 h
  obtain ⟨hrun, hrest⟩ := matRun_split hno (k := 0) (v := 0) (dg := 0) (cc := 0) h
  obtain ⟨htoks, htokvals⟩ :=
    CFSG.KC.Mtx.runT_sound (n := 0) (tok := hdrOK h₀ h₁ h₂ h₃) hrun
  have htoks4 : (mtxTokens (String.ofList line)).length = 4 := by simpa using htoks
  have htok4 : ∀ i < 4, hdrOK h₀ h₁ h₂ h₃ i
      (tokenVal ((mtxTokens (String.ofList line)).getD i "")) = true := by
    intro i hi
    exact htokvals i (by omega)
  have hdigits := matRun_digits hrest
  have hfilter : matDigits (String.ofList (line ++ '\n' :: rest)) =
      rest.filter isMatDigit := by
    rw [matDigits_ofList_split hno, filter_not_ws_eq_filter_digit hdigits.1]
  have hheader : matHeader (String.ofList (line ++ '\n' :: rest)) = [h₀, h₁, h₂, h₃] := by
    unfold matHeader
    rw [mtxTokens_append_nl, List.take_append_of_le_length (by omega)]
    exact header_take htoks4 htok4
  refine ⟨hheader, ?_, ?_⟩
  · rw [hfilter, ← List.countP_eq_length_filter]
    simpa using hdigits.2
  · intro c hc
    rw [hfilter, List.mem_filter] at hc
    exact (isMatDigit_iff c).1 hc.2

end CFSG.KC.MatK

end
