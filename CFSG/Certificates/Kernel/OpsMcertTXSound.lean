module

public import Certificates.Data.Kernel.OpsMcertTX
public import CFSG.Certificates.Kernel.OpsMcertTSound

public section

namespace CFSG.KC.OpsMT

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC.OpsMN

variable {V : Type} (O : Ops Nat V)

theorem seedsXT_spec {A B : Nat} {C : MCert} {rA rB : Nat} {C' : MCert} {xs : List (Nat × Word)}
    (h : seedsXT O A B C rA rB C' xs = true) :
    C'.prog.all (Op.lt C'.nregs) = true ∧
      (∀ q ∈ xs, q.1 < C.nregs ∧ wordLt C'.nregs q.2 = true) ∧
      regsN O A B C.nregs C.prog (fun R => certN O R C && O.eq (getN R rA) A &&
        O.eq (getN R rB) B) = true ∧
      ∀ q ∈ xs, O.eq (getN (C.prog.foldl (stepL O) (initN O A B C.nregs)) q.1)
        (evalWN O (C'.prog.foldl (stepL O) (initN O A B C'.nregs)) q.2) = true := by
  unfold seedsXT at h
  rw [regsT_eq O A B C.nregs C.prog (fun g => certG O g C && O.eq (g rA) A && O.eq (g rB) B &&
    regsT O A B C'.nregs C'.prog fun T' =>
      xs.all fun q => O.eq (g q.1) (evalWG O (getR T') q.2))] at h
  simp only [regsN_eq, Bool.and_eq_true, certG_getN] at h
  obtain ⟨⟨hp, hxs⟩, ⟨⟨hc, ha⟩, hb⟩, hx⟩ := h
  rw [regsT_eq O A B C'.nregs C'.prog (fun g' => xs.all fun q =>
    O.eq (getN (C.prog.foldl (stepL O) (initN O A B C.nregs)) q.1) (evalWG O g' q.2))] at hx
  simp only [regsN_eq, evalWG_getN] at hx
  refine ⟨hp, fun q hq => ?_, ?_, fun q hq => List.all_eq_true.1 hx q hq⟩
  · have := List.all_eq_true.1 hxs q hq
    rw [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · rw [regsN_eq]
    simp only [hc, ha, hb, Bool.and_self]

theorem cross_of {M V₀ : Type} [Inhabited M] {O₀ : Ops M V₀} (H : CFSG.KC.OpsHom.Hom O₀ O)
    {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A) (eB : O₀.decode sB = H.U B)
    (hA : H.P A) (hB : H.P B) {n : Nat} {prog : List Op} {n' : Nat} {prog' : List Op}
    (hp : prog.all (Op.lt n) = true) (hp' : prog'.all (Op.lt n') = true) {r : Nat} {w : Word}
    (hr : r < n) (hw : wordLt n' w = true)
    (h : O.eq (getN (prog.foldl (stepL O) (initN O A B n)) r)
      (evalWN O (prog'.foldl (stepL O) (initN O A B n')) w) = true) :
    O₀.eq (O₀.regsOf sA sB n prog)[r]! (evalW O₀ (O₀.regsOf sA sB n' prog') w) = true := by
  have hR := rel_regsOf H eA eB hA hB hp
  have hR' := rel_regsOf H eA eB hA hB hp'
  obtain ⟨u, pu⟩ := hR.2 r (by rw [length_run, length_initN]; exact hr)
  obtain ⟨v, pv⟩ := evalW_U H hR' w (by rw [length_run, length_initN]; exact hw)
  rw [u, v, H.eq pu pv]
  exact h

theorem seedsXT_sound {M V₀ : Type} [Inhabited M] {O₀ : Ops M V₀} (H : CFSG.KC.OpsHom.Hom O₀ O)
    {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A) (eB : O₀.decode sB = H.U B)
    (hA : H.P A) (hB : H.P B) {n : Nat} {prog : List Op} {fs : List MFact} {rA rB : Nat}
    {n' : Nat} {prog' : List Op} {fs' : List MFact} {xs : List (Nat × Word)}
    (hrA : rA < n) (hrB : rB < n)
    (h : seedsXT O A B ⟨n, prog, fs⟩ rA rB ⟨n', prog', fs'⟩ xs = true) :
    mcertCheck O₀ sA sB ⟨n, prog, fs⟩ = true ∧
      O₀.eq (O₀.regsOf sA sB n prog)[rA]! (O₀.decode sA) = true ∧
      O₀.eq (O₀.regsOf sA sB n prog)[rB]! (O₀.decode sB) = true ∧
      ∀ q ∈ xs, O₀.eq (O₀.regsOf sA sB n prog)[q.1]! (evalW O₀ (O₀.regsOf sA sB n' prog') q.2) =
        true := by
  obtain ⟨hp', hxs, hseeds, hx⟩ := seedsXT_spec O h
  obtain ⟨hm, h0, h1⟩ := seeds_of_N H eA eB hA hB hrA hrB hseeds
  have hp : prog.all (Op.lt n) = true := by
    unfold mcertCheck at hm
    simp only [Bool.and_eq_true] at hm
    exact hm.1.2
  exact ⟨hm, h0, h1, fun q hq =>
    cross_of O H eA eB hA hB hp hp' (hxs q hq).1 (hxs q hq).2 (hx q hq)⟩

end CFSG.KC.OpsMT

end
