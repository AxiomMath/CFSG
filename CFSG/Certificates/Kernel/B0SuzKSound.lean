module

public import Certificates.Data.Kernel.B0SuzK
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Q0SuzTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatTypeInputs
import CFSG.Certificates.Kernel.B0SuzK.Glue
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

namespace CFSG.KC.B0SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

@[expose] def qProdG (qA : Nat → Array Nat) (v : Nat) : Array Nat :=
  (List.range 6).foldl (fun r i => if v.testBit i then compA 1782 r (qA i) else r) (idTab 1782)

@[expose] def qProdsG (qA : Nat → Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 64) fun v => qProdG qA v.val

@[expose] def tPowG (tT : Array Nat) (b : Nat) : Array Nat := if b == 1 then tT else idTab 1782

@[expose] def qEltsG (tT : Array Nat) (qA : Nat → Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 128) fun j => compA 1782 (qProdsG qA)[j.val / 2]! (tPowG tT (j.val % 2))

@[expose] def b0SuzCheckG (tT : Array Nat) (qA cT : Nat → Array Nat) : Bool :=
  permOK 1782 tT && eqA 1782 (compA 1782 tT tT) (idTab 1782) &&
  !(eqA 1782 tT (idTab 1782)) &&
  (allBelow 6 fun i => permOK 1782 (qA i) && inM (qA i) && commutesA (qA i) tT) &&
  (allBelow 64 fun v => allBelow 64 fun w =>
    eqA 1782 (compA 1782 (qProdsG qA)[v]! (qProdsG qA)[w]!)
      (compA 1782 (qProdsG qA)[v ^^^ w]! (tPowG tT (gammaBit v w)))) &&
  (allBelow 128 fun j => allBelow 128 fun j' => j == j' ||
    !(eqA 1782 (qEltsG tT qA)[j]! (qEltsG tT qA)[j']!)) &&
  (allBelow 10 fun k => permOK 1782 (cT k) && allBelow 6 fun i =>
    eqA 1782 (compA 1782 (compA 1782 (cT k) (qA i)) (invCand 1782 (cT k)))
      (compA 1782 (qProdsG qA)[(act k i).1]! (tPowG tT (act k i).2))) &&
  CFSG.PSL3Four.Native.enumOK 64 matTabs matEnum && matEnum.tabs.size == 25920 && noTS3

theorem b0SuzCheck_eq : b0SuzCheck = b0SuzCheckG tTab qArr cTab := rfl

private theorem act_lt : ∀ k < 10, ∀ i < 6, (act k i).1 < 64 := by decide +kernel

private theorem oact_lt : ∀ i < 6, (oact i).1 < 64 := by decide +kernel

open CFSG.KC.BfsPin in
private theorem qProdsG_get {Q : Nat → Nat} {qA : Nat → Array Nat}
    (hP : ∀ i < 6, PP 1782 11 (Q i)) (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i)) {v : Nat}
    (hv : v < 64) : (qProdsG qA)[v]! = unpack 1782 11 (qProdK Q v) := by
  unfold qProdsG
  rw [getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn]
  exact (qProdK_spec hP hq v).2

open CFSG.KC.BfsPin in
private theorem qProdsG_facts {T : Nat} {Q QP QE : Nat → Nat} {qA : Nat → Array Nat}
    (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i)) (hB : baseK T Q QP QE = true) :
    ∀ v < 64, PP 1782 11 (QP v) ∧ (qProdsG qA)[v]! = unpack 1782 11 (QP v) := by
  obtain ⟨-, -, -, hQ, hQP, -⟩ := baseK_facts hB
  intro v hv
  have hP : ∀ i < 6, PP 1782 11 (Q i) := fun i hi => (hQ i hi).1
  rw [hQP v hv]
  exact ⟨(qProdK_spec hP hq v).1, qProdsG_get hP hq hv⟩

theorem b0SuzK_sound {tT : Array Nat} {qA cT : Nat → Array Nat} {T : Nat} {Q C QP QE : Nat → Nat}
    (ht : tT = unpack 1782 11 T) (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i))
    (hc : ∀ k < 10, cT k = unpack 1782 11 (C k)) (hin : ∀ i < 6, inM (qA i) = true)
    (hB : baseK T Q QP QE = true) (hR : ∀ v < 64, ruleK T QP gammaBit v = true)
    (hD : distK QE = true) (hC : conjK T Q C QP act = true)
    (hM : (CFSG.PSL3Four.Native.enumOK 64 matTabs matEnum && matEnum.tabs.size == 25920) = true)
    (hN : noTS3 = true) :
    b0SuzCheckG tT qA cT = true := by
  open CFSG.KC.BfsPin in
  obtain ⟨hT, hsq, hne, hQ, -, hQE⟩ := baseK_facts hB
  have hPQP : ∀ v < 64, PP 1782 11 (QP v) := fun v hv => (qProdsG_facts hq hB v hv).1
  have hqs : ∀ v < 64, (qProdsG qA)[v]! = unpack 1782 11 (QP v) := fun v hv =>
    (qProdsG_facts hq hB v hv).2
  have htp : ∀ b, tPowG tT b = unpack 1782 11 (tPowK T b) := tPow_unpack ht
  have hPQE : ∀ j < 128, PP 1782 11 (QE j) := fun j hj => by
    rw [hQE j hj, shiftRight_one_eq]
    exact (hPQP _ (by omega)).mul (PP_tPowK hT _)
  have hqe : ∀ j < 128, (qEltsG tT qA)[j]! = unpack 1782 11 (QE j) := fun j hj => by
    have hj2 : j / 2 < 64 := by omega
    unfold qEltsG
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    dsimp only
    rw [hqs _ hj2, htp, compA_PP (hPQP _ hj2) (PP_tPowK hT _), hQE j hj, shiftRight_one_eq,
      land_one_eq]
    rfl
  have hid : PP 1782 11 (pidn 1782 11) := PP.id szOK_1782
  simp only [Bool.and_eq_true] at hM
  unfold b0SuzCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [ht]
    exact permOK_unpack hT
  · rw [ht, compA_PP hT hT, idTab_unpack, eqA_PP (hT.mul hT) hid]
    exact hsq
  · rw [ht, idTab_unpack, eqA_PP hT hid, hne]
    rfl
  · refine allBelow_iff.2 fun i hi => ?_
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, hin i hi⟩, ?_⟩
    · rw [hq i hi]
      exact permOK_unpack (hQ i hi).1
    · unfold CFSG.Sporadic.SuzOddCore.commutesA
      rw [ht, hq i hi, compA_PP (hQ i hi).1 hT, compA_PP hT (hQ i hi).1,
        eqA_PP ((hQ i hi).1.mul hT) (hT.mul (hQ i hi).1)]
      exact (hQ i hi).2
  · refine allBelow_iff.2 fun v hv => allBelow_iff.2 fun w hw => ?_
    have hvw : v ^^^ w < 64 := Nat.xor_lt_two_pow (n := 6) hv hw
    rw [hqs v hv, hqs w hw, hqs _ hvw, htp, compA_PP (hPQP v hv) (hPQP w hw),
      compA_PP (hPQP _ hvw) (PP_tPowK hT _),
      eqA_PP ((hPQP v hv).mul (hPQP w hw)) ((hPQP _ hvw).mul (PP_tPowK hT _))]
    exact allN_spec (hR v hv) w hw
  · refine allBelow_iff.2 fun j hj => allBelow_iff.2 fun j' hj' => ?_
    by_cases hjj : j = j'
    · subst hjj
      simp
    · rw [hqe j hj, hqe j' hj', eqA_PP (hPQE j hj) (hPQE j' hj')]
      have hb : Nat.beq (QE j) (QE j') = false := by
        rcases Nat.lt_or_gt_of_ne hjj with h | h
        · exact beq_symm_false (beq_false_of_notB (allN_spec (allN_spec hD j' hj') j h))
        · exact beq_false_of_notB (allN_spec (allN_spec hD j hj) j' h)
      rw [hb]
      simp
  · refine allBelow_iff.2 fun k hk => ?_
    obtain ⟨hCk, hact⟩ := conjK_facts hC k hk
    simp only [Bool.and_eq_true]
    refine ⟨?_, allBelow_iff.2 fun i hi => ?_⟩
    · rw [hc k hk]
      exact permOK_unpack hCk
    · have ha : (act k i).1 < 64 := act_lt k hk i hi
      rw [hc k hk, hq i hi, conj_unpack hCk (hQ i hi).1, hqs _ ha, htp,
        compA_PP (hPQP _ ha) (PP_tPowK hT _),
        eqA_PP (hCk.conjK (hQ i hi).1) ((hPQP _ ha).mul (PP_tPowK hT _))]
      exact hact i hi
  · exact hM.1
  · exact hM.2
  · exact hN

@[expose] def q0SuzCheckG (oT tT : Array Nat) (qA : Nat → Array Nat) : Bool :=
  permOK 1782 oT && !(inM oT) &&
  (allBelow 6 fun i =>
    eqA 1782 (compA 1782 (compA 1782 oT (qA i)) (invCand 1782 oT))
      (compA 1782 (qProdsG qA)[(oact i).1]! (tPowG tT (oact i).2))) &&
  (allBelow matEnum.tabs.size fun j => !(matEnum.tabs[j]! == outerMat))

theorem q0SuzCheck_eq : q0SuzCheck = q0SuzCheckG outerTab tTab qArr := rfl

theorem q0SuzK_sound {oT tT : Array Nat} {qA : Nat → Array Nat} {OT T OM NM : Nat}
    {Q QP QE TM : Nat → Nat}
    (ho : oT = unpack 1782 11 OT) (ht : tT = unpack 1782 11 T)
    (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i)) (hin : inM oT = false)
    (hB : baseK T Q QP QE = true) (hK : q0K T OT Q QP oact NM TM OM = true)
    (hM : matEnum.tabs = Array.ofFn (n := NM) fun j => unpack 64 7 (TM j.val))
    (hcM : ∀ j < NM, canonK 64 7 (mask 7) (64 * 7) (TM j) = true)
    (hOM : outerMat = unpack 64 7 OM) (hcOM : canonK 64 7 (mask 7) (64 * 7) OM = true) :
    q0SuzCheckG oT tT qA = true := by
  open CFSG.KC.BfsPin in
  obtain ⟨hT, -, -, hQ, -, -⟩ := baseK_facts hB
  obtain ⟨hO, hact, hTM⟩ := q0K_facts hK
  have hPQP : ∀ v < 64, PP 1782 11 (QP v) := fun v hv => (qProdsG_facts hq hB v hv).1
  have hqs : ∀ v < 64, (qProdsG qA)[v]! = unpack 1782 11 (QP v) := fun v hv =>
    (qProdsG_facts hq hB v hv).2
  have htp : ∀ b, tPowG tT b = unpack 1782 11 (tPowK T b) := tPow_unpack ht
  unfold q0SuzCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [ho]
    exact permOK_unpack hO
  · rw [hin]
    rfl
  · refine allBelow_iff.2 fun i hi => ?_
    have ha : (oact i).1 < 64 := oact_lt i hi
    rw [ho, hq i hi, conj_unpack hO (hQ i hi).1, hqs _ ha, htp,
      compA_PP (hPQP _ ha) (PP_tPowK hT _),
      eqA_PP (hO.conjK (hQ i hi).1) ((hPQP _ ha).mul (PP_tPowK hT _))]
    exact hact i hi
  · rw [hM, Array.size_ofFn]
    refine allBelow_iff.2 fun j hj => ?_
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, hOM]
    have hne : (unpack 64 7 (TM j) == unpack 64 7 OM) = false := by
      cases h : (unpack 64 7 (TM j) == unpack 64 7 OM)
      · rfl
      · have heq : unpack 64 7 (TM j) = unpack 64 7 OM := beq_iff_eq.1 h
        have := eqA_unpack (hcM j hj) hcOM
        rw [heq, eqA_self, hTM j hj] at this
        exact absurd this (by decide)
    dsimp only
    rw [hne]
    rfl

@[expose] def wordTabG (cT : Nat → Array Nat) (w : List Nat) : Array Nat :=
  w.foldl (fun r k => compA 1782 r (cT k)) (idTab 1782)

@[expose] def transOKG (tT : Array Nat) (qA cT : Nat → Array Nat) (w : List Nat) (x : Array Nat)
    (v : Nat) : Bool :=
  let c := wordTabG cT w
  eqA 1782 (compA 1782 c x) (compA 1782 (qProdsG qA)[v]! c) ||
    eqA 1782 (compA 1782 c x) (compA 1782 (compA 1782 (qProdsG qA)[v]! tT) c)

@[expose] def commQOKG (qA : Nat → Array Nat) (g : Array Nat) : Bool :=
  allBelow 64 fun u => polarBit u typeA0 == 1 ||
    commIs g (qProdsG qA)[u]! (idTab 1782) || commIs g (qProdsG qA)[u]! (qProdsG qA)[typeA0]!

@[expose] def shatTypeCheckG (tT : Array Nat) (qA cT : Nat → Array Nat) : Bool :=
  let y := wordTabG cT typeYWord
  let y' := wordTabG cT typeY'Word
  let qa := (qProdsG qA)[typeA0]!
  typeA0 != 0 && qMinusBit typeA0 == 0 && typeA0 < 64 &&
  (typeYWord.all fun k => k < 10) && (typeY'Word.all fun k => k < 10) &&
  eqA 1782 (compA 1782 y y) (idTab 1782) && eqA 1782 (compA 1782 y' y') (idTab 1782) &&
  commutesA y qa && commutesA y' qa && commQOKG qA y && commQOKG qA y' &&
  commIs y y' (compA 1782 qa tT) &&
  (allBelow 64 fun v => v == 0 || qMinusBit v == 1 ||
    match typeTrans.lookup v with
    | some w => (w.all fun k => k < 10) && transOKG tT qA cT w qa v
    | none => false)

theorem shatTypeCheck_eq : shatTypeCheck = shatTypeCheckG tTab qArr cTab := rfl

@[expose] def shatConstOK : Bool :=
  typeA0 != 0 && qMinusBit typeA0 == 0 && typeA0 < 64 &&
  (typeYWord.all fun k => k < 10) && (typeY'Word.all fun k => k < 10)

theorem shatConstOK_true : shatConstOK = true := by decide +kernel

open CFSG.KC.BfsPin in
private theorem commQOKG_of {qA : Nat → Array Nat} {QP : Nat → Nat} {g : Nat}
    (hg : PP 1782 11 g) (hPQP : ∀ v < 64, PP 1782 11 (QP v))
    (hqs : ∀ v < 64, (qProdsG qA)[v]! = unpack 1782 11 (QP v)) (ha : typeA0 < 64)
    (h : commQK QP polarBit typeA0 g = true) : commQOKG qA (unpack 1782 11 g) = true := by
  unfold commQOKG
  refine allBelow_iff.2 fun u hu => ?_
  have h1 := allN_spec h u hu
  rw [hqs u hu, hqs typeA0 ha, idTab_unpack, commIs_unpack hg (hPQP u hu) (PP.id szOK_1782),
    commIs_unpack hg (hPQP u hu) (hPQP typeA0 ha), beq_nat]
  simp only [CFSG.KC.HexaK.orB_eq, Bool.or_assoc] at h1 ⊢
  exact h1

theorem shatK_sound {tT : Array Nat} {qA cT : Nat → Array Nat} {T : Nat} {Q C QP QE : Nat → Nat}
    (ht : tT = unpack 1782 11 T) (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i))
    (hc : ∀ k < 10, cT k = unpack 1782 11 (C k))
    (hB : baseK T Q QP QE = true) (hC : conjK T Q C QP act = true) (hF : shatConstOK = true)
    (hS : shatK T C QP typeYWord typeY'Word typeA0 polarBit qMinusBit (fun v => typeTrans.lookup v) =
      true) :
    shatTypeCheckG tT qA cT = true := by
  open CFSG.KC.BfsPin in
  obtain ⟨hT, -⟩ := baseK_facts hB
  have hPC : ∀ k < 10, PP 1782 11 (C k) := fun k hk => (conjK_facts hC k hk).1
  have hPQP : ∀ v < 64, PP 1782 11 (QP v) := fun v hv => (qProdsG_facts hq hB v hv).1
  have hqs : ∀ v < 64, (qProdsG qA)[v]! = unpack 1782 11 (QP v) := fun v hv =>
    (qProdsG_facts hq hB v hv).2
  have hF' := hF
  unfold shatConstOK at hF'
  simp only [Bool.and_eq_true] at hF'
  have hA0 : typeA0 < 64 := of_decide_eq_true hF'.1.1.2
  have hYw : ∀ k ∈ typeYWord, k < 10 := fun k hk =>
    of_decide_eq_true (List.all_eq_true.1 hF'.1.2 k hk)
  have hY'w : ∀ k ∈ typeY'Word, k < 10 := fun k hk =>
    of_decide_eq_true (List.all_eq_true.1 hF'.2 k hk)
  obtain ⟨hyP, hy0⟩ := wordC_unpack hPC hc hYw
  obtain ⟨hy'P, hy'0⟩ := wordC_unpack hPC hc hY'w
  have hy : wordTabG cT typeYWord = unpack 1782 11 (wordC C typeYWord) := hy0
  have hy' : wordTabG cT typeY'Word = unpack 1782 11 (wordC C typeY'Word) := hy'0
  have hqaP := hPQP typeA0 hA0
  have hqa := hqs typeA0 hA0
  have hid : PP 1782 11 (pidn 1782 11) := PP.id szOK_1782
  unfold shatK at hS
  simp only [strictB_eq', andB_eq, Bool.and_eq_true] at hS
  obtain ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8⟩ := hS
  unfold shatTypeCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hF', ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hy, compA_PP hyP hyP, idTab_unpack, eqA_PP (hyP.mul hyP) hid]
    exact hS1
  · rw [hy', compA_PP hy'P hy'P, idTab_unpack, eqA_PP (hy'P.mul hy'P) hid]
    exact hS2
  · rw [hy, hqa, commutesA_unpack hyP hqaP]
    exact hS3
  · rw [hy', hqa, commutesA_unpack hy'P hqaP]
    exact hS4
  · rw [hy]
    exact commQOKG_of hyP hPQP hqs hA0 hS5
  · rw [hy']
    exact commQOKG_of hy'P hPQP hqs hA0 hS6
  · rw [hy, hy', hqa, ht, compA_PP hqaP hT, commIs_unpack hyP hy'P (hqaP.mul hT)]
    exact hS7
  · refine allBelow_iff.2 fun v hv => ?_
    have hl := allN_spec hS8 v hv
    simp only [CFSG.KC.HexaK.orB_eq, Bool.or_eq_true] at hl
    simp only [Bool.or_eq_true, beq_nat]
    rcases hl with h0 | h1 | htr
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr h1)
    · refine Or.inr ?_
      unfold transK at htr
      cases hlk : List.lookup v typeTrans with
      | none =>
        simp only [hlk] at htr
        exact absurd htr (by decide)
      | some w =>
        simp only [hlk, andB_eq, strictB_eq', Bool.and_eq_true] at htr
        obtain ⟨hw', htr'⟩ := htr
        have hw'' : ∀ k ∈ w, k < 10 := fun k hk => Nat.blt_eq.mp (List.all_eq_true.1 hw' k hk)
        obtain ⟨hcP, hc0⟩ := wordC_unpack hPC hc hw''
        have hcw : wordTabG cT w = unpack 1782 11 (wordC C w) := hc0
        have hvP := hPQP v hv
        dsimp only
        rw [Bool.and_eq_true]
        refine ⟨List.all_eq_true.2 fun k hk => decide_eq_true (hw'' k hk), ?_⟩
        unfold transOKG
        dsimp only
        rw [hcw, hqa, hqs v hv, ht, compA_PP hcP hqaP, compA_PP hvP hcP, compA_PP hvP hT,
          compA_PP (hvP.mul hT) hcP, eqA_PP (hcP.mul hqaP) (hvP.mul hcP),
          eqA_PP (hcP.mul hqaP) ((hvP.mul hT).mul hcP)]
        simp only [CFSG.KC.HexaK.orB_eq] at htr'
        exact htr'

end CFSG.KC.B0SuzK

end
