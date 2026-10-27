module

public import Certificates.Data.Kernel.OpsLayMcert
public import CFSG.Certificates.Kernel.OpsLayKSnd

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.KC.LocalComp.Ops3Snd CFSG.KC.OpsLayK.Snd

theorem wordLt_of_wordOK {n : Nat} {w : Word} (h : wordOK n w = true) : wordLt n w = true := by
  simp only [wordOK, wordLt, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact fun p hp => (h p hp).1

theorem rel_evalW {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {R : List Nat}
    {Rn : Array (Array FV)} (hR : LCorr c R Rn) :
    ∀ w : Word, wordOK R.length w = true → LRel c (evalW (ops3 c.d) Rn w) (evalWL c R w)
  | [], _ => by
    simp only [evalW, evalWL]
    exact rel_one hc hp
  | (r, e) :: w, h => by
    simp only [wordOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [evalW, evalWL]
    exact rel_mul hc hp (rel_pow hc hp (hR.2 r h.1.1) h.1.2)
      (rel_evalW hc hp hR w (by simpa only [wordOK] using h.2))

theorem factOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {R : List Nat}
    {Rn : Array (Array FV)} (hR : LCorr c R Rn) {n : Nat} (hn : R.length = n) (f : MFact)
    (h : factL c R n f = true) : factOK (ops3 c.d) Rn n f = true := by
  subst hn
  cases f with
  | ord r e =>
    simp only [factL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hr, he0⟩, he⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hr, he0⟩, eq_pow_one hc hp (hR.2 r hr) he hb⟩
  | conj g u w =>
    simp only [factL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hg, hu⟩, hw⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hg, wordLt_of_wordOK hu⟩, wordLt_of_wordOK hw⟩, ?_⟩
    exact eq_of_rel (rel_mul hc hp (hR.2 g hg) (rel_evalW hc hp hR u hu))
      (rel_mul hc hp (rel_evalW hc hp hR w hw) (hR.2 g hg)) hb
  | ne u w t =>
    simp only [factL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hu, hw⟩, ht⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true]
    refine ⟨⟨wordLt_of_wordOK hu, wordLt_of_wordOK hw⟩, ?_⟩
    exact vne_of_vrel hc hp (vrel_vmul hc hp (vrel_unit hc hp ht) (rel_evalW hc hp hR u hu))
      (vrel_vmul hc hp (vrel_unit hc hp ht) (rel_evalW hc hp hR w hw)) (ne_of_not_beq hb)
  | eq u w =>
    simp only [factL, Bool.and_eq_true] at h
    obtain ⟨⟨hu, hw⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true]
    exact ⟨⟨wordLt_of_wordOK hu, wordLt_of_wordOK hw⟩,
      eq_of_rel (rel_evalW hc hp hR u hu) (rel_evalW hc hp hR w hw) hb⟩

theorem mcert_of_facts {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {A B : Nat}
    {LA LB : List Char} {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert}
    (hprog : progOK C.nregs C.prog = true)
    (hf : C.facts.all (factL c (runL c C.prog (initR c A B C.nregs)) C.nregs) = true) :
    mcertCheck (ops3 c.d) sA sB C = true := by
  have hL : LCorr c (runL c C.prog (initR c A B C.nregs))
      ((ops3 c.d).regsOf sA sB C.nregs C.prog) := lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := runL_initR_length c C.prog A B C.nregs
  obtain ⟨h2, hlt⟩ := progOK_spec hprog
  have hf' := hf
  unfold mcertCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf' hlt ⊢
  exact ⟨⟨h2, hlt⟩, fun f hfm => factOK_of hc hp hL hlen f (hf' f hfm)⟩

theorem mcertL_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert}
    (h : mcertL c A B C = true) : mcertCheck (ops3 d) sA sB C = true := by
  subst hd
  unfold mcertL at h
  rw [Bool.and_eq_true, runC_eq] at h
  exact mcert_of_facts hc hp hA hB hsA hsB h.1 h.2

theorem seeds_of_runL {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert} {rA rB : Nat}
    (hprog : progOK C.nregs C.prog = true) (hrA : rA < C.nregs) (hrB : rB < C.nregs)
    (hf : C.facts.all (factL c (runL c C.prog (initR c A B C.nregs)) C.nregs) = true)
    (he : seedRegsL c (runL c C.prog (initR c A B C.nregs)) A B rA rB = true) :
    mcertCheck (ops3 d) sA sB C = true ∧ rA < C.nregs ∧ rB < C.nregs ∧
      (ops3 d).eq ((ops3 d).regsOf sA sB C.nregs C.prog)[rA]! ((ops3 d).decode sA) = true ∧
      (ops3 d).eq ((ops3 d).regsOf sA sB C.nregs C.prog)[rB]! ((ops3 d).decode sB) = true := by
  subst hd
  simp only [seedRegsL, Bool.and_eq_true] at he
  have hL : LCorr c (runL c C.prog (initR c A B C.nregs))
      ((ops3 c.d).regsOf sA sB C.nregs C.prog) := lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := runL_initR_length c C.prog A B C.nregs
  refine ⟨mcert_of_facts hc hp hA hB hsA hsB hprog hf, hrA, hrB, ?_, ?_⟩
  · exact eq_of_rel (hL.2 rA (by rw [hlen]; exact hrA)) (rel_decode hc hp hA hsA) he.1
  · exact eq_of_rel (hL.2 rB (by rw [hlen]; exact hrB)) (rel_decode hc hp hB hsB) he.2

theorem seedsL_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert} {rA rB : Nat}
    (h : seedsL c A B C rA rB = true) :
    mcertCheck (ops3 d) sA sB C = true ∧ rA < C.nregs ∧ rB < C.nregs ∧
      (ops3 d).eq ((ops3 d).regsOf sA sB C.nregs C.prog)[rA]! ((ops3 d).decode sA) = true ∧
      (ops3 d).eq ((ops3 d).regsOf sA sB C.nregs C.prog)[rB]! ((ops3 d).decode sB) = true := by
  unfold seedsL at h
  rw [runC_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hprog, hrA⟩, hrB⟩, ⟨hf, hea⟩, heb⟩ := h
  exact seeds_of_runL hc hp hd hA hB hsA hsB hprog hrA hrB hf
    (by simp only [seedRegsL, Bool.and_eq_true]; exact ⟨hea, heb⟩)

theorem eq_of_eqL : ∀ {a b : List Nat}, eqL a b = true → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eq_of_eqL h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

theorem runL_append (c : Lay) (p q : List Op) (R : List Nat) :
    runL c (p ++ q) R = runL c q (runL c p R) := by
  unfold runL
  rw [List.foldl_append]

theorem runL_of_chunks {c : Lay} {prog : List Op} {k m : Nat} {S : Nat → List Nat}
    (hm : prog.length ≤ m * k) (h : ∀ i < m, chunkL c prog k i (S i) (S (i + 1)) = true) :
    runL c prog (S 0) = S m := by
  have key : ∀ j ≤ m, runL c (prog.take (j * k)) (S 0) = S j := by
    intro j
    induction j with
    | zero => intro _; simp [runL]
    | succ j ih =>
      intro hj
      have hc := h j (by omega)
      unfold chunkL at hc
      rw [runC_eq] at hc
      rw [Nat.succ_mul, List.take_add, runL_append, ih (by omega)]
      exact eq_of_eqL hc
  have e : prog.take (m * k) = prog := List.take_of_length_le hm
  rw [← e]
  exact key m le_rfl

theorem all_of_chunks {α : Type} {p : α → Bool} {fs : List α} {k m : Nat}
    (hm : fs.length ≤ m * k) (h : ∀ i < m, ((fs.drop (i * k)).take k).all p = true) :
    fs.all p = true := by
  have key : ∀ j ≤ m, (fs.take (j * k)).all p = true := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Nat.succ_mul, List.take_add, List.all_append, ih (by omega), h j (by omega)]
      rfl
  have e : fs.take (m * k) = fs := List.take_of_length_le hm
  rw [← e]
  exact key m le_rfl

theorem seedsLC_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {C : MCert} {rA rB : Nat}
    (hprog : progOK C.nregs C.prog = true) (hrA : rA < C.nregs) (hrB : rB < C.nregs)
    {S : Nat → List Nat} {k m kf mf : Nat} (h0 : S 0 = initR c A B C.nregs)
    (hm : C.prog.length ≤ m * k) (hch : ∀ i < m, chunkL c C.prog k i (S i) (S (i + 1)) = true)
    (hmf : C.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c (S m) C.nregs C.facts kf i = true)
    (he : seedRegsL c (S m) A B rA rB = true) :
    mcertCheck (ops3 d) sA sB C = true ∧ rA < C.nregs ∧ rB < C.nregs ∧
      (ops3 d).eq ((ops3 d).regsOf sA sB C.nregs C.prog)[rA]! ((ops3 d).decode sA) = true ∧
      (ops3 d).eq ((ops3 d).regsOf sA sB C.nregs C.prog)[rB]! ((ops3 d).decode sB) = true := by
  have hrun : runL c C.prog (initR c A B C.nregs) = S m := by
    rw [← h0]
    exact runL_of_chunks hm hch
  refine seeds_of_runL hc hp hd hA hB hsA hsB hprog hrA hrB ?_ (by rw [hrun]; exact he)
  rw [hrun]
  exact all_of_chunks hmf hf

end CFSG.KC.OpsLayK

end
