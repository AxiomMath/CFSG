module

public import Certificates.Data.Kernel.OpsMcertN
public import CFSG.Certificates.Kernel.OpsHom
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsMN

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC.OpsHom

variable {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V} (H : Hom O₀ O)

@[expose] def stepL (O : Ops Nat V) (R : List Nat) : Op → List Nat
  | .mul i j t => R.set t (O.mul (getN R i) (getN R j))
  | .pow e i t => R.set t (O.pow (getN R i) e)

theorem runN_eq (O : Ops Nat V) : ∀ (prog : List Op) (R : List Nat) (k : List Nat → Bool),
    runN O prog R k = k (prog.foldl (stepL O) R)
  | [], _, _ => rfl
  | op :: prog, R, k => by
    change stepN O R (fun R' => runN O prog R' k) op = _
    cases op with
    | mul i j t =>
      change forceB _ (fun a => forceL (R.set t a) fun R' => runN O prog R' k) = _
      rw [forceB_eq, forceL_eq, runN_eq O prog]
      rfl
    | pow e i t =>
      change forceB _ (fun a => forceL (R.set t a) fun R' => runN O prog R' k) = _
      rw [forceB_eq, forceL_eq, powN_eq O _ _ _ (Nat.lt_succ_self e), runN_eq O prog]
      rfl

@[expose] def Rel (Ra : Array M) (Rl : List Nat) : Prop :=
  Ra.size = Rl.length ∧ ∀ r < Rl.length, Ra[r]! = H.U (getN Rl r) ∧ H.P (getN Rl r)

theorem getN_set_eq {R : List Nat} {t : Nat} (ht : t < R.length) (x : Nat) :
    getN (R.set t x) t = x := by
  simp [getN, List.getD_eq_getElem?_getD, ht]

theorem getN_set_ne (R : List Nat) {t r : Nat} (h : t ≠ r) (x : Nat) :
    getN (R.set t x) r = getN R r := by
  simp [getN, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem rel_set {Ra : Array M} {Rl : List Nat} (hR : Rel H Ra Rl) {t : Nat}
    (ht : t < Rl.length) {x : Nat} (hx : H.P x) :
    Rel H (Ra.setIfInBounds t (H.U x)) (Rl.set t x) := by
  obtain ⟨hs, hR⟩ := hR
  refine ⟨by simp [hs], fun r hr => ?_⟩
  rw [List.length_set] at hr
  have hr' : r < Ra.size := hs ▸ hr
  rw [getElem!_pos _ r (by simpa using hr'), Array.getElem_setIfInBounds hr']
  by_cases htr : t = r
  · subst htr
    rw [getN_set_eq ht, if_pos rfl]
    exact ⟨rfl, hx⟩
  · rw [if_neg htr, getN_set_ne Rl htr, ← getElem!_pos Ra r hr']
    exact hR r hr

theorem rel_step {Ra : Array M} {Rl : List Nat} (hR : Rel H Ra Rl) (op : Op)
    (hop : op.lt Rl.length = true) : Rel H (O₀.step Ra op) (stepL O Rl op) := by
  cases op with
  | mul i j t =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, ht⟩ := hop
    obtain ⟨ei, pi⟩ := hR.2 i hi
    obtain ⟨ej, pj⟩ := hR.2 j hj
    obtain ⟨em, pm⟩ := H.mul pi pj
    change Rel H (Ra.set! t (O₀.mul Ra[i]! Ra[j]!)) _
    rw [Array.set!_eq_setIfInBounds, ei, ej, em]
    exact rel_set H hR ht pm
  | pow e i t =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨hi, ht⟩ := hop
    obtain ⟨ei, pi⟩ := hR.2 i hi
    obtain ⟨ep, pp⟩ := H.pow_U e pi
    change Rel H (Ra.set! t (O₀.pow Ra[i]! e)) _
    rw [Array.set!_eq_setIfInBounds, ei, ep]
    exact rel_set H hR ht pp

theorem length_stepL (R : List Nat) (op : Op) : (stepL O R op).length = R.length := by
  cases op <;> simp [stepL]

theorem rel_run : ∀ (prog : List Op) {Ra : Array M} {Rl : List Nat}, Rel H Ra Rl →
    prog.all (Op.lt Rl.length) = true → Rel H (O₀.run prog Ra) (prog.foldl (stepL O) Rl)
  | [], _, _, hR, _ => hR
  | op :: prog, Ra, Rl, hR, hp => by
    rw [List.all_cons, Bool.and_eq_true] at hp
    change Rel H (O₀.run prog (O₀.step Ra op)) (prog.foldl (stepL O) (stepL O Rl op))
    refine rel_run prog (rel_step H hR op hp.1) ?_
    rw [length_stepL]
    exact hp.2

theorem length_initN (A B n : Nat) : (initN O A B n).length = n := by simp [initN]

theorem rel_init {A B : Nat} (hA : H.P A) (hB : H.P B) (n : Nat) :
    Rel H (O₀.initRegs (H.U A) (H.U B) n) (initN O A B n) := by
  refine ⟨by simp [Ops.initRegs, initN], fun r hr => ?_⟩
  rw [length_initN] at hr
  have hr' : r < (O₀.initRegs (H.U A) (H.U B) n).size := by simpa [Ops.initRegs] using hr
  rw [getElem!_pos _ r hr']
  simp only [Ops.initRegs, Array.getElem_ofFn, getN, initN, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hr, Option.map_some, Option.getD_some]
  by_cases h0 : r = 0
  · simp [h0, hA]
  · by_cases h1 : r = 1
    · simp [h1, hB]
    · simp only [h0, h1, ↓reduceIte]
      exact H.one

theorem rel_regsOf {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {n : Nat} {prog : List Op}
    (hp : prog.all (Op.lt n) = true) :
    Rel H (O₀.regsOf sA sB n prog) (prog.foldl (stepL O) (initN O A B n)) := by
  unfold Ops.regsOf
  rw [eA, eB]
  exact rel_run H prog (rel_init H hA hB n) (by rw [length_initN]; exact hp)

theorem length_run (prog : List Op) (R : List Nat) :
    (prog.foldl (stepL O) R).length = R.length := by
  induction prog generalizing R with
  | nil => rfl
  | cons op prog ih => rw [List.foldl_cons, ih, length_stepL]

theorem regsN_eq (A B n : Nat) (prog : List Op) (k : List Nat → Bool) :
    regsN O A B n prog k = k (prog.foldl (stepL O) (initN O A B n)) :=
  runN_eq O prog _ k

theorem wordLt_cons {n r e : Nat} {w : Word} (h : wordLt n ((r, e) :: w) = true) :
    r < n ∧ wordLt n w = true := by
  unfold wordLt at h ⊢
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem evalW_U {Ra : Array M} {Rl : List Nat} (hR : Rel H Ra Rl) :
    ∀ w : Word, wordLt Rl.length w = true →
      evalW O₀ Ra w = H.U (evalWN O Rl w) ∧ H.P (evalWN O Rl w)
  | [], _ => H.one
  | (r, e) :: w, h => by
    obtain ⟨hr, hw⟩ := wordLt_cons h
    obtain ⟨er, pr⟩ := hR.2 r hr
    obtain ⟨ep, pp⟩ := H.pow_U e pr
    obtain ⟨ew, pw⟩ := evalW_U hR w hw
    change O₀.mul (O₀.pow Ra[r]! e) (evalW O₀ Ra w) =
      H.U (O.mul (powN O (Nat.succ e) (getN Rl r) e) (evalWN O Rl w)) ∧
        H.P (O.mul (powN O (Nat.succ e) (getN Rl r) e) (evalWN O Rl w))
    rw [powN_eq O _ _ _ (Nat.lt_succ_self e), er, ep, ew]
    exact H.mul pp pw

theorem factOK_eq {Ra : Array M} {Rl : List Nat} (hR : Rel H Ra Rl) (f : MFact) :
    factOK O₀ Ra Rl.length f = factN O Rl Rl.length f := by
  cases f with
  | ord r e =>
    simp only [factOK, factN]
    rw [powN_eq O _ _ _ (Nat.lt_succ_self e)]
    by_cases hr : r < Rl.length
    · obtain ⟨er, pr⟩ := hR.2 r hr
      obtain ⟨ep, pp⟩ := H.pow_U e pr
      rw [er, ep, H.one.1, H.eq pp H.one.2]
    · simp [hr]
  | conj h u w =>
    simp only [factOK, factN]
    by_cases hh : h < Rl.length
    · by_cases hu : wordLt Rl.length u = true
      · by_cases hw : wordLt Rl.length w = true
        · obtain ⟨eh, ph⟩ := hR.2 h hh
          obtain ⟨eu, pu⟩ := evalW_U H hR u hu
          obtain ⟨ew, pw⟩ := evalW_U H hR w hw
          obtain ⟨e1, p1⟩ := H.mul ph pu
          obtain ⟨e2, p2⟩ := H.mul pw ph
          rw [eh, eu, ew, e1, e2, H.eq p1 p2]
        · simp [hw]
      · simp [hu]
    · simp [hh]
  | ne w₁ w₂ t =>
    simp only [factOK, factN]
    by_cases h1 : wordLt Rl.length w₁ = true
    · by_cases h2 : wordLt Rl.length w₂ = true
      · obtain ⟨e1, p1⟩ := evalW_U H hR w₁ h1
        obtain ⟨e2, p2⟩ := evalW_U H hR w₂ h2
        obtain ⟨eu, pu⟩ := H.unit t
        obtain ⟨v1, q1⟩ := H.vmul pu p1
        obtain ⟨v2, q2⟩ := H.vmul pu p2
        rw [e1, e2, eu, v1, v2, H.vne q1 q2]
      · simp [h2]
    · simp [h1]
  | eq w₁ w₂ =>
    simp only [factOK, factN]
    by_cases h1 : wordLt Rl.length w₁ = true
    · by_cases h2 : wordLt Rl.length w₂ = true
      · obtain ⟨e1, p1⟩ := evalW_U H hR w₁ h1
        obtain ⟨e2, p2⟩ := evalW_U H hR w₂ h2
        rw [e1, e2, H.eq p1 p2]
      · simp [h2]
    · simp [h1]

theorem facts_eq {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {n : Nat} {prog : List Op}
    (hp : prog.all (Op.lt n) = true) (fs : List MFact) :
    fs.all (factOK O₀ (O₀.regsOf sA sB n prog) n) =
      fs.all (factN O (prog.foldl (stepL O) (initN O A B n)) n) := by
  have hR := rel_regsOf H eA eB hA hB hp
  have hl : (prog.foldl (stepL O) (initN O A B n)).length = n := by
    rw [length_run, length_initN]
  apply List.all_congr rfl
  intro f
  have := factOK_eq H hR f
  rw [hl] at this
  exact this

theorem eq_reg {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {n : Nat} {prog : List Op}
    (hp : prog.all (Op.lt n) = true) {r : Nat} (hr : r < n) {X : Nat} (hX : H.P X) :
    O₀.eq (O₀.regsOf sA sB n prog)[r]! (H.U X) =
      O.eq (getN (prog.foldl (stepL O) (initN O A B n)) r) X := by
  have hR := rel_regsOf H eA eB hA hB hp
  have hl : (prog.foldl (stepL O) (initN O A B n)).length = n := by
    rw [length_run, length_initN]
  obtain ⟨e, p⟩ := hR.2 r (by rw [hl]; exact hr)
  rw [e, H.eq p hX]

theorem mcertCheck_eq {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) (C : MCert) :
    mcertCheck O₀ sA sB C = mcertN O A B C := by
  unfold mcertCheck mcertN
  rw [regsN_eq]
  unfold certN
  simp only
  by_cases hp : C.prog.all (Op.lt C.nregs) = true
  · rw [facts_eq H eA eB hA hB hp]
  · simp [hp]

theorem mcertCheck_of_N {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {C : MCert}
    (h : mcertN O A B C = true) : mcertCheck O₀ sA sB C = true := by
  rw [mcertCheck_eq H eA eB hA hB]
  exact h

theorem regs_of_N {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {n : Nat} {prog : List Op}
    (hp : prog.all (Op.lt n) = true) {k : List Nat → Bool} (h : regsN O A B n prog k = true) :
    ∃ Rl : List Nat, k Rl = true ∧ Rl.length = n ∧ Rel H (O₀.regsOf sA sB n prog) Rl := by
  rw [regsN_eq] at h
  exact ⟨_, h, by rw [length_run, length_initN], rel_regsOf H eA eB hA hB hp⟩

theorem facts_of_rel {Ra : Array M} {Rl : List Nat} {n : Nat} (hR : Rel H Ra Rl)
    (hn : Rl.length = n) (fs : List MFact) :
    fs.all (factOK O₀ Ra n) = fs.all (factN O Rl n) := by
  subst hn
  exact List.all_congr rfl fun f => factOK_eq H hR f

theorem eq_of_rel {Ra : Array M} {Rl : List Nat} (hR : Rel H Ra Rl) {r : Nat}
    (hr : r < Rl.length) {X : Nat} (hX : H.P X) :
    O₀.eq Ra[r]! (H.U X) = O.eq (getN Rl r) X := by
  obtain ⟨e, p⟩ := hR.2 r hr
  rw [e, H.eq p hX]

theorem mcertN_of_chunks {A B : Nat} {C : MCert} {k m : Nat} (hn : 2 ≤ C.nregs)
    (hp : C.prog.all (Op.lt C.nregs) = true) (hm : C.facts.length ≤ m * k)
    (h : ∀ i < m, chunkN O A B C k i = true) : mcertN O A B C = true := by
  unfold mcertN
  rw [regsN_eq]
  unfold certN
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨hn, by simpa [List.all_eq_true] using hp⟩, fun f hf => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [Nat.mul_zero] at hm
      omega
    · exact h0
  have hi : j / k < m := by
    rw [Nat.div_lt_iff_lt_mul hk]
    omega
  have hc := h (j / k) hi
  unfold chunkN at hc
  rw [regsN_eq, List.all_eq_true] at hc
  apply hc
  have h1 : j / k * k ≤ j := Nat.div_mul_le_self j k
  have h2 : j - j / k * k < k := by
    have := Nat.lt_div_mul_add (a := j) hk
    omega
  have hmem : (C.facts.drop (j / k * k))[j - j / k * k]'(by simp; omega) = C.facts[j] := by
    rw [List.getElem_drop]
    congr 1
    omega
  rw [← hmem]
  apply List.mem_iff_getElem.2
  exact ⟨j - j / k * k, by simp; omega, by rw [List.getElem_take]⟩

theorem seeds_of_N {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {n : Nat} {prog : List Op}
    {fs : List MFact} {rA rB : Nat} (hrA : rA < n) (hrB : rB < n)
    (h : regsN O A B n prog (fun R => certN O R ⟨n, prog, fs⟩ && O.eq (getN R rA) A &&
      O.eq (getN R rB) B) = true) :
    mcertCheck O₀ sA sB ⟨n, prog, fs⟩ = true ∧
      O₀.eq (O₀.regsOf sA sB n prog)[rA]! (O₀.decode sA) = true ∧
      O₀.eq (O₀.regsOf sA sB n prog)[rB]! (O₀.decode sB) = true := by
  rw [regsN_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, ha⟩, hb⟩ := h
  have hp : prog.all (Op.lt n) = true := by
    unfold certN at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1.2
  refine ⟨?_, ?_, ?_⟩
  · rw [mcertCheck_eq H eA eB hA hB, mcertN, regsN_eq]
    exact hc
  · rw [eA, eq_reg H eA eB hA hB hp hrA hA]
    exact ha
  · rw [eB, eq_reg H eA eB hA hB hp hrB hB]
    exact hb

end CFSG.KC.OpsMN

end
