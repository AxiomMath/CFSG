module

public import CFSG.Certificates.Kernel.OpsLayKSndP
public import CFSG.Certificates.Kernel.OpsLayMcertSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsLayK.SndP

theorem rel_evalWP {c : Lay} (hc : c.ok = true) {R : List Nat}
    {Rn : Array (Array (Array Nat))} (hR : LCorr c R Rn) :
    ∀ w : Word, wordOK R.length w = true → LRel c (evalW (opsP c.p c.d) Rn w) (evalWL c R w)
  | [], _ => by
    simp only [evalW, evalWL]
    exact rel_one hc
  | (r, e) :: w, h => by
    simp only [wordOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [evalW, evalWL]
    exact rel_mul hc (rel_pow hc (hR.2 r h.1.1) h.1.2)
      (rel_evalWP hc hR w (by simpa only [wordOK] using h.2))

theorem factOK_ofP {c : Lay} (hc : c.ok = true) {R : List Nat}
    {Rn : Array (Array (Array Nat))} (hR : LCorr c R Rn) {n : Nat} (hn : R.length = n)
    (f : MFact) (h : factL c R n f = true) : factOK (opsP c.p c.d) Rn n f = true := by
  subst hn
  cases f with
  | ord r e =>
    simp only [factL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hr, he0⟩, he⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hr, he0⟩, eq_of_rel (rel_pow hc (hR.2 r hr) he) (rel_one hc) hb⟩
  | conj g u w =>
    simp only [factL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hg, hu⟩, hw⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hg, wordLt_of_wordOK hu⟩, wordLt_of_wordOK hw⟩, ?_⟩
    exact eq_of_rel (rel_mul hc (hR.2 g hg) (rel_evalWP hc hR u hu))
      (rel_mul hc (rel_evalWP hc hR w hw) (hR.2 g hg)) hb
  | ne u w t =>
    simp only [factL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hu, hw⟩, ht⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true]
    refine ⟨⟨wordLt_of_wordOK hu, wordLt_of_wordOK hw⟩, ?_⟩
    exact vne_of_vrel hc (vrel_vmul hc (vrel_unit hc ht) (rel_evalWP hc hR u hu))
      (vrel_vmul hc (vrel_unit hc ht) (rel_evalWP hc hR w hw)) (Snd.ne_of_not_beq hb)
  | eq u w =>
    simp only [factL, Bool.and_eq_true] at h
    obtain ⟨⟨hu, hw⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true]
    exact ⟨⟨wordLt_of_wordOK hu, wordLt_of_wordOK hw⟩,
      eq_of_rel (rel_evalWP hc hR u hu) (rel_evalWP hc hR w hw) hb⟩

theorem mcert_of_factsP {c : Lay} (hc : c.ok = true) {A B : Nat}
    {LA LB : List Char} {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert}
    (hprog : progOK C.nregs C.prog = true)
    (hf : C.facts.all (factL c (Snd.runL c C.prog (initR c A B C.nregs)) C.nregs) = true) :
    mcertCheck (opsP c.p c.d) sA sB C = true := by
  have hL : LCorr c (Snd.runL c C.prog (initR c A B C.nregs))
      ((opsP c.p c.d).regsOf sA sB C.nregs C.prog) := lcorr_regs hc hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c C.prog A B C.nregs
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hf' := hf
  unfold mcertCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf' hlt ⊢
  exact ⟨⟨h2, hlt⟩, fun f hfm => factOK_ofP hc hL hlen f (hf' f hfm)⟩

theorem mcertLP_sound {c : Lay} {p d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert}
    (h : mcertL c A B C = true) : mcertCheck (opsP p d) sA sB C = true := by
  subst hp hd
  unfold mcertL at h
  rw [Bool.and_eq_true, Snd.runC_eq] at h
  exact mcert_of_factsP hc hA hB hsA hsB h.1 h.2

theorem seeds_of_runLP {c : Lay} {p d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert} {rA rB : Nat}
    (hprog : progOK C.nregs C.prog = true) (hrA : rA < C.nregs) (hrB : rB < C.nregs)
    (hf : C.facts.all (factL c (Snd.runL c C.prog (initR c A B C.nregs)) C.nregs) = true)
    (he : seedRegsL c (Snd.runL c C.prog (initR c A B C.nregs)) A B rA rB = true) :
    mcertCheck (opsP p d) sA sB C = true ∧ rA < C.nregs ∧ rB < C.nregs ∧
      (opsP p d).eq ((opsP p d).regsOf sA sB C.nregs C.prog)[rA]! ((opsP p d).decode sA) = true ∧
      (opsP p d).eq ((opsP p d).regsOf sA sB C.nregs C.prog)[rB]! ((opsP p d).decode sB) =
        true := by
  subst hp hd
  simp only [seedRegsL, Bool.and_eq_true] at he
  have hL : LCorr c (Snd.runL c C.prog (initR c A B C.nregs))
      ((opsP c.p c.d).regsOf sA sB C.nregs C.prog) := lcorr_regs hc hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c C.prog A B C.nregs
  refine ⟨mcert_of_factsP hc hA hB hsA hsB hprog hf, hrA, hrB, ?_, ?_⟩
  · exact eq_of_rel (hL.2 rA (by rw [hlen]; exact hrA)) (rel_decode hc hA hsA) he.1
  · exact eq_of_rel (hL.2 rB (by rw [hlen]; exact hrB)) (rel_decode hc hB hsB) he.2

theorem seedsLP_sound {c : Lay} {p d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert} {rA rB : Nat}
    (h : seedsL c A B C rA rB = true) :
    mcertCheck (opsP p d) sA sB C = true ∧ rA < C.nregs ∧ rB < C.nregs ∧
      (opsP p d).eq ((opsP p d).regsOf sA sB C.nregs C.prog)[rA]! ((opsP p d).decode sA) = true ∧
      (opsP p d).eq ((opsP p d).regsOf sA sB C.nregs C.prog)[rB]! ((opsP p d).decode sB) =
        true := by
  unfold seedsL at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hprog, hrA⟩, hrB⟩, ⟨hf, hea⟩, heb⟩ := h
  exact seeds_of_runLP hc hp hd hA hB hsA hsB hprog hrA hrB hf
    (by simp only [seedRegsL, Bool.and_eq_true]; exact ⟨hea, heb⟩)

theorem seedsLCP_sound {c : Lay} {p d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert} {rA rB : Nat}
    (hprog : progOK C.nregs C.prog = true) (hrA : rA < C.nregs) (hrB : rB < C.nregs)
    {S : Nat → List Nat} {k m kf mf : Nat} (h0 : S 0 = initR c A B C.nregs)
    (hm : C.prog.length ≤ m * k) (hch : ∀ i < m, chunkL c C.prog k i (S i) (S (i + 1)) = true)
    (hmf : C.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c (S m) C.nregs C.facts kf i = true)
    (he : seedRegsL c (S m) A B rA rB = true) :
    mcertCheck (opsP p d) sA sB C = true ∧ rA < C.nregs ∧ rB < C.nregs ∧
      (opsP p d).eq ((opsP p d).regsOf sA sB C.nregs C.prog)[rA]! ((opsP p d).decode sA) = true ∧
      (opsP p d).eq ((opsP p d).regsOf sA sB C.nregs C.prog)[rB]! ((opsP p d).decode sB) =
        true := by
  have hrun : Snd.runL c C.prog (initR c A B C.nregs) = S m := by
    rw [← h0]
    exact runL_of_chunks hm hch
  refine seeds_of_runLP hc hp hd hA hB hsA hsB hprog hrA hrB ?_ (by rw [hrun]; exact he)
  rw [hrun]
  exact all_of_chunks hmf hf

end CFSG.KC.OpsLayK

end
