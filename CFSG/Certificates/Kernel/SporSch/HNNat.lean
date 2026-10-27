
module

public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public import CFSG.Certificates.Kernel.SporSch.HNArr

public section

namespace CFSG.KS.HNNat

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.KS.PW CFSG.KS.TW CFSG.KS.HNArr

theorem peq_maps {n : ℕ} {t u : Array ℕ} (h : ∀ x < n, t[x]! = u[x]!) : peq n t u = true :=
  CFSG.ONSchreier.allBelowN_iff.2 fun x hx => by rw [h x hx]; exact beq_self_eq_true _

theorem strongOK_maps {n s : ℕ} {S : Array (Array ℕ)} {W : Array (List ℤ)} {F FI : ℕ → ℕ → ℕ}
    {a0 a1 : Array ℕ} (hsz : S.size = s) (hWs : W.size = s) (h2 : 2 ≤ s)
    (hS : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x)
    (hSi : ∀ j < s, ∀ x < n, ((pinvs n S)[j]!)[x]! = FI j x)
    (hinv : ∀ j < s, ∀ x < n, F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (h0 : ∀ x < n, a0[x]! = F 0 x) (h1 : ∀ x < n, a1[x]! = F 1 x)
    (hW : ∀ j, 2 ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (GZ F FI) x) :
    strongOK n a0 a1 S W = true := by
  have hL : LettersOK n s S (pinvs n S) F FI := fun j hj x hx =>
    ⟨hS j hj x hx, hSi j hj x hx, (hinv j hj x hx).1, (hinv j hj x hx).2.1⟩
  unfold strongOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨h2.trans_eq hWs.symm, hsz.trans hWs.symm⟩,
    peq_maps fun x hx => by rw [hS 0 (by omega) x hx, h0 x hx]⟩,
    peq_maps fun x hx => by rw [hS 1 (by omega) x hx, h1 x hx]⟩, ?_⟩, ?_⟩
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => CFSG.ONSchreier.allBelowN_iff.2
      fun x hx => ?_
    rw [hsz] at hj
    rw [hS j hj x hx, hSi j hj _ (hinv j hj x hx).1, (hinv j hj x hx).2.2]
    simp [(hinv j hj x hx).1]
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rw [hsz] at hj
    rcases Nat.lt_or_ge j 2 with h | h
    · simp [h]
    · obtain ⟨hl, hf⟩ := hW j h hj
      have hl' : ∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ s := fun l hm =>
        ⟨(hl l hm).1, by have := (hl l hm).2; omega⟩
      rw [plettersOK_iff.2 hl, peq_maps fun x hx => by
        rw [hS j hj x hx, (pword_get hL _ hl' x hx).1, hf x hx]]
      simp

@[expose] def natF (j x : ℕ) : ℕ := (natArr LocalData.strongImages[j]!)[x]!

@[expose] def natFI (j x : ℕ) : ℕ := LocalData.strongImages[j]!.idxOf x

theorem natS_facts : (∀ j < 17, ∀ x < 12, natF j x < 12 ∧ natFI j x < 12 ∧ natFI j (natF j x) = x) ∧
    (∀ x < 12, (natArr LocalData.natGen1)[x]! = natF 0 x ∧ (natArr LocalData.natGen2)[x]! = natF 1 x) ∧
    (natArr LocalData.natGen1).size = 12 ∧ (natArr LocalData.natGen2).size = 12 ∧
    (∀ j, 2 ≤ j → j < 17 → (∀ l ∈ LocalData.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < 12, natF j x = LocalData.strongWords[j]!.foldr (GZ natF natFI) x) ∧
    LocalData.strongWords.size = 17 := by
  decide +kernel

abbrev natS : Array (Array ℕ) :=
  extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2] LocalData.strongWords

theorem natS_get : natS.size = 17 ∧ ∀ j < 17, natS[j]! = Array.ofFn (n := 12) fun i => natF j i.val := by
  obtain ⟨hinv, h01, hs1, hs2, hW, hsz⟩ := natS_facts
  exact extendStrong_get (n := 12) (m := 2) (F := natF) (FI := natFI) rfl hsz (by omega)
    (fun j hj => by
      interval_cases j
      · exact arr_ext hs1 fun x hx => (h01 x hx).1
      · exact arr_ext hs2 fun x hx => (h01 x hx).2) hW (fun j hj x hx => hinv j hj x hx)

theorem natS_pt {j x : ℕ} (hj : j < 17) (hx : x < 12) : (natS[j]!)[x]! = natF j x := by
  rw [natS_get.2 j hj, ofFn_get' hx]

theorem natSi_pt {j x : ℕ} (hj : j < 17) (hx : x < 12) : ((pinvs 12 natS)[j]!)[x]! = natFI j x := by
  rw [pinvs_get (by rw [natS_get.1]; exact hj), natS_get.2 j hj]
  exact CFSG.KS.CB.pinvCand_get (fun y hy => (natS_facts.1 j hj y hy).1)
    (fun y hy => (natS_facts.1 j hj y hy).2.2) hx

theorem natLetters : LettersOK 12 17 natS (pinvs 12 natS) natF natFI := fun j hj x hx =>
  ⟨natS_pt hj hx, natSi_pt hj hx, (natS_facts.1 j hj x hx).1, (natS_facts.1 j hj x hx).2.1⟩

theorem natWord_pt {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) {x : ℕ} (hx : x < 12) :
    (pword 12 natS (pinvs 12 natS) w)[x]! = w.foldr (GZ natF natFI) x :=
  (pword_get natLetters w hw x hx).1

theorem natStrongOK : strongOK 12 (natArr LocalData.natGen1) (natArr LocalData.natGen2) natS
    LocalData.strongWords = true := by
  obtain ⟨hinv, h01, -, -, hW, hsz⟩ := natS_facts
  exact strongOK_maps natS_get.1 hsz (by omega) (fun j hj x hx => natS_pt hj hx)
    (fun j hj x hx => natSi_pt hj hx) hinv (fun x hx => (h01 x hx).1) (fun x hx => (h01 x hx).2) hW

end CFSG.KS.HNNat

end
