module

public import Certificates.Data.Kernel.CF23L34.RegRun1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs

public section

namespace CFSG.KC.CF23L34

open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeGS

abbrev RegRel (φ : Nat → Tab) (C : Nat → Prop) (R : List (Nat × Nat)) (A : Array HeGSReg) : Prop :=
  A.size = R.length ∧
    ∀ i (h : i < R.length), A[i]! = (φ R[i].1, φ R[i].2) ∧ C R[i].1 ∧ C R[i].2

theorem getD_lt {α : Type} {R : List α} {i : Nat} (h : i < R.length) (d : α) :
    R.getD i d = R[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

variable {n : Nat} {φ : Nat → Tab} {m : Nat → Nat → Nat} {e : Nat} {C : Nat → Prop}

theorem letter_rel {R : List (Nat × Nat)} {A : Array HeGSReg} (hR : RegRel φ C R A) {l : Int}
    (h0 : l ≠ 0) (hl : l.natAbs ≤ R.length) :
    heGSLetter A l = (φ (rL R l).1, φ (rL R l).2) ∧ C (rL R l).1 ∧ C (rL R l).2 := by
  unfold heGSLetter rL
  by_cases hp : 0 < l
  · have hi : l.toNat - 1 < R.length := by omega
    rw [if_pos hp, if_pos hp, getD_lt hi]
    exact hR.2 _ hi
  · have hi : (-l).toNat - 1 < R.length := by omega
    rw [if_neg hp, if_neg hp, getD_lt hi]
    obtain ⟨h1, h2, h3⟩ := hR.2 _ hi
    rw [h1]
    exact ⟨rfl, h3, h2⟩

theorem word_rel (hm : ∀ p q, C p → C q → comp n (φ p) (φ q) = φ (m p q))
    (hmC : ∀ p q, C p → C q → C (m p q)) (he : idTab n = φ e) (heC : C e)
    (hr : ∀ p, C p → m p e = p) (hl : ∀ p, C p → m e p = p)
    {R : List (Nat × Nat)} {A : Array HeGSReg} (hR : RegRel φ C R A) :
    ∀ w : List Int, CFSG.Monster.B.Co2.Native.lettersOK R.length w = true →
      heGSWord n A w = (φ (rW1 m e R w).1, φ (rW1 m e R w).2) ∧ C (rW1 m e R w).1 ∧
        C (rW1 m e R w).2
  | [], _ => by
    unfold heGSWord
    rw [List.foldr_nil, he]
    exact ⟨rfl, heC, heC⟩
  | l :: w, hw => by
    unfold CFSG.Monster.B.Co2.Native.lettersOK at hw
    rw [List.all_cons, Bool.and_eq_true] at hw
    have hl0 : l ≠ 0 ∧ l.natAbs ≤ R.length := by
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hw
      exact hw.1
    obtain ⟨hL, c1, c2⟩ := letter_rel hR hl0.1 hl0.2
    have hfold : heGSWord n A (l :: w) =
        (comp n (heGSLetter A l).1 (heGSWord n A w).1,
          comp n (heGSWord n A w).2 (heGSLetter A l).2) := by
      unfold heGSWord
      rw [List.foldr_cons]
    cases w with
    | nil =>
      have h0 : heGSWord n A [] = (idTab n, idTab n) := by
        unfold heGSWord
        rw [List.foldr_nil]
      have h1 : rW1 m e R [l] = rL R l := rfl
      rw [hfold, h0, h1, hL, he]
      refine ⟨Prod.ext ?_ ?_, c1, c2⟩
      · exact (hm _ _ c1 heC).trans (congrArg φ (hr _ c1))
      · exact (hm _ _ heC c2).trans (congrArg φ (hl _ c2))
    | cons l' w' =>
      have ih := word_rel hm hmC he heC hr hl hR (l' :: w') hw.2
      have h1 : rW1 m e R (l :: l' :: w') =
          (m (rL R l).1 (rW1 m e R (l' :: w')).1, m (rW1 m e R (l' :: w')).2 (rL R l).2) := rfl
      rw [hfold, h1, ih.1, hL]
      exact ⟨Prod.ext (hm _ _ c1 ih.2.1) (hm _ _ ih.2.2 c2), hmC _ _ c1 ih.2.1,
        hmC _ _ ih.2.2 c2⟩

theorem push_rel {R : List (Nat × Nat)} {A : Array HeGSReg} (hR : RegRel φ C R A)
    {x : Nat × Nat} {y : HeGSReg} (hy : y = (φ x.1, φ x.2)) (c1 : C x.1) (c2 : C x.2) :
    RegRel φ C (R ++ [x]) (A.push y) := by
  refine ⟨by simp [hR.1], fun i hi => ?_⟩
  have hiA : i < (A.push y).size := by
    rw [Array.size_push, hR.1]
    simpa using hi
  rw [getElem!_pos (A.push y) i hiA, Array.getElem_push, List.getElem_append]
  by_cases h : i < R.length
  · have h' : i < A.size := hR.1 ▸ h
    rw [dif_pos h', dif_pos h, ← getElem!_pos A i h']
    exact hR.2 i h
  · have h' : ¬ i < A.size := hR.1 ▸ h
    rw [dif_neg h', dif_neg h]
    have hi1 : i - R.length = 0 := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    simp only [hi1, List.getElem_singleton]
    exact ⟨hy, c1, c2⟩

theorem run_rel (hm : ∀ p q, C p → C q → comp n (φ p) (φ q) = φ (m p q))
    (hmC : ∀ p q, C p → C q → C (m p q)) (he : idTab n = φ e) (heC : C e)
    (hr : ∀ p, C p → m p e = p) (hl : ∀ p, C p → m e p = p) :
    ∀ (prog : List (List Int)) {R : List (Nat × Nat)} {A : Array HeGSReg}, RegRel φ C R A →
      heGSOK R.length prog = true → RegRel φ C (rRun1 m e R prog) (heGSRun n A prog)
  | [], _, _, hR, _ => hR
  | w :: prog, R, A, hR, hp => by
    unfold heGSOK at hp
    rw [Bool.and_eq_true] at hp
    obtain ⟨hW, c1, c2⟩ := word_rel hm hmC he heC hr hl hR w hp.1
    have hR' := push_rel hR hW c1 c2
    have hlen : (R ++ [rW1 m e R w]).length = R.length + 1 := by
      rw [List.length_append, List.length_singleton]
    have hp2 : heGSOK (R ++ [rW1 m e R w]).length prog = true := by
      rw [hlen]
      exact hp.2
    have ih := run_rel hm hmC he heC hr hl prog hR' hp2
    have e1 : heGSRun n A (w :: prog) = heGSRun n (A.push (heGSWord n A w)) prog := by
      unfold heGSRun
      rw [List.foldl_cons]
    have e2 : rRun1 m e R (w :: prog) = rRun1 m e (R ++ [rW1 m e R w]) prog := by
      unfold rRun1
      rw [List.foldl_cons]
    rw [e1, e2]
    exact ih

theorem rRun_length (m : Nat → Nat → Nat) (e : Nat) :
    ∀ (prog : List (List Int)) (R : List (Nat × Nat)),
      (rRun1 m e R prog).length = R.length + prog.length
  | [], R => by
    unfold rRun1
    rw [List.foldl_nil, List.length_nil, Nat.add_zero]
  | w :: prog, R => by
    have e2 : rRun1 m e R (w :: prog) = rRun1 m e (R ++ [rW1 m e R w]) prog := by
      unfold rRun1
      rw [List.foldl_cons]
    rw [e2, rRun_length m e prog, List.length_append, List.length_singleton, List.length_cons]
    omega

end CFSG.KC.CF23L34

end
