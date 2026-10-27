module

public import CFSG.GH74.GLS.NT44.PermutationInputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash

public noncomputable section

namespace CFSG.GH74.GLS.NT44.PermutationActions

open PermutationInputs
open CFSG.GH74.GLS.NT44.PermutationNative
open CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native

private def D : PermutationNative.NT44Inputs := PermutationNative.inputs ()

private abbrev KI : Array (Array Nat) := D.ks.map (invCand 2688)

private abbrev LI : Array (Array Nat) := D.lifts.map (invCand 2688)

private abbrev B : Array (Array Nat) := D.ag.map fun i => D.lifts[i]!

private abbrev BI : Array (Array Nat) := D.ag.map fun i => LI[i]!

private abbrev U : Array (Array Nat) :=
  D.parent.map fun w => wordA 2688 B BI w

private abbrev UI : Array (Array Nat) :=
  D.parent.map fun w => wordA 2688 B BI (w.reverse.map fun l => -l)

private abbrev sig : Array (Array (Array Nat)) :=
  Array.ofFn (n := 256) fun i =>
    Array.ofFn (n := 2) fun j =>
      compA 2688 (compA 2688 D.lifts[i.val]! D.ks[j.val]!) LI[i.val]!

@[expose] def liftPerm (i : Fin 256) : Equiv.Perm (Fin 2688) :=
  CFSG.Monster.B.Co2.permOfArr 2688
    (PermutationNative.inputs ()).lifts[i.val]!

@[expose] def selectedLiftIndex (k : Fin 4) : Fin 256 :=
  ⟨k.val + 1, Nat.lt_trans (Nat.succ_lt_succ k.isLt) (by decide)⟩

private theorem bridge_shape
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    PermutationNative.shapeOK D = true := by
  have h := hcheck
  dsimp only [D]
  simp only [PermutationNative.bridgeCheck] at h
  split_ifs at h with hs
  exact hs

private theorem bridge_checks
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    allLt 2 (fun i => isInvA 2688 D.ks[i]! KI[i]!) = true ∧
    allLt 256 (fun i => isInvA 2688 D.lifts[i]! LI[i]!) = true ∧
    normalizerCheck D KI B BI = true ∧
    parentCheck D LI U UI = true ∧
    transitionCheck D LI sig = true := by
  have h := hcheck
  dsimp only [D, KI, LI, B, BI, U, UI, sig]
  simp only [PermutationNative.bridgeCheck] at h
  split_ifs at h with hs
  · simp only [Bool.and_eq_true, and_assoc] at h
    obtain ⟨hks, -, hlifts, -, -, hnorm, hparent, htrans, -⟩ := h
    exact ⟨hks, hlifts, hnorm, hparent, htrans⟩

private theorem shape_facts
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    D.ks.size = 2 ∧ D.lifts.size = 256 ∧ D.ag.size = 4 ∧
    D.ag[0]! = 1 ∧ D.ag[1]! = 2 ∧ D.ag[2]! = 3 ∧ D.ag[3]! = 4 ∧
    D.nw.size = 4 ∧
    (∀ k < 4, D.nw[k]!.liftIndex = D.ag[k]! ∧
      D.nw[k]!.left.size = 2 ∧ D.nw[k]!.inverse.size = 2 ∧
      wordsLettersOK 2 D.nw[k]!.left = true ∧
      wordsLettersOK 2 D.nw[k]!.inverse = true) ∧
    D.tr.size = 256 ∧
    (∀ i < 256, D.tr[i]!.size = 4 ∧ ∀ k < 4, (D.tr[i]!)[k]! < 256) ∧
    D.parent.size = 256 ∧ positiveWordsOK D.parent = true := by
  have hs := bridge_shape hcheck
  have h := hs
  unfold PermutationNative.shapeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hks, -, hlifts, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hnorm, htrSize, htrAll, -, -, hpar, hparpos, -⟩ := h
  have hnorm' := hnorm
  unfold normalizerShapeOK at hnorm'
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hnorm'
  obtain ⟨hag, hag0, hag1, hag2, hag3, hnw, hnwAll⟩ := hnorm'
  have hnwSpec (k : ℕ) (hk : k < 4) :
      D.nw[k]!.liftIndex = D.ag[k]! ∧
      D.nw[k]!.left.size = 2 ∧ D.nw[k]!.inverse.size = 2 ∧
      wordsLettersOK 2 D.nw[k]!.left = true ∧
      wordsLettersOK 2 D.nw[k]!.inverse = true := by
    have := allLt_spec hnwAll hk
    simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using this
  have htrSpec (i : ℕ) (hi : i < 256) :
      D.tr[i]!.size = 4 ∧ ∀ k < 4, (D.tr[i]!)[k]! < 256 := by
    have h1 := allLt_spec htrAll hi
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨h1.1, fun k hk => by simpa using allLt_spec h1.2 hk⟩
  exact ⟨hks, hlifts, hag, hag0, hag1, hag2, hag3, hnw, hnwSpec, htrSize, htrSpec,
    hpar, hparpos⟩

private theorem parent_letters
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) : lettersOK 4 D.parent[i.val]! = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpar, hparpos⟩ := shape_facts hcheck
  have hall : allLt D.parent.size
      (fun i => D.parent[i]!.all (fun l => l == 1 || l == 2 || l == 3 || l == 4)) = true := by
    simpa [positiveWordsOK] using hparpos
  have hpos := allLt_spec hall (by rw [hpar]; exact i.isLt)
  rw [lettersOK, List.all_eq_true]
  intro l hl
  have hp := List.all_eq_true.mp hpos l hl
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with ((rfl | rfl) | rfl) | rfl <;> simp

private theorem selected_ag
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (k : Fin 4) : D.ag[k.val]! = (selectedLiftIndex k).val := by
  obtain ⟨-, -, -, hag0, hag1, hag2, hag3, -, -, -, -, -, -⟩ := shape_facts hcheck
  have hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
  rcases hk with h | h | h | h <;>
    simp [selectedLiftIndex, h, hag0, hag1, hag2, hag3]

private theorem rep_ks
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (j : Fin 2) :
    CFSG.Monster.B.Co2.Rep 2688 D.ks[j.val]! (ksPerm j) ∧
    CFSG.Monster.B.Co2.Rep 2688 KI[j.val]! (ksPerm j)⁻¹ := by
  obtain ⟨hks, -, -, -, -⟩ := bridge_checks hcheck
  have h := allLt_spec hks j.isLt
  exact CFSG.Monster.B.Co2.rep_permOfArr h

private theorem rep_lift
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) :
    CFSG.Monster.B.Co2.Rep 2688 D.lifts[i.val]! (liftPerm i) ∧
    CFSG.Monster.B.Co2.Rep 2688 LI[i.val]! (liftPerm i)⁻¹ := by
  obtain ⟨-, hlifts, -, -, -⟩ := bridge_checks hcheck
  have h := allLt_spec hlifts i.isLt
  exact CFSG.Monster.B.Co2.rep_permOfArr h

private theorem rep_B
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (k : Fin 4) :
    CFSG.Monster.B.Co2.Rep 2688 B[k.val]! (liftPerm (selectedLiftIndex k)) := by
  obtain ⟨-, -, hagSize, -, -, -, -, -, -, -, -, -, -⟩ := shape_facts hcheck
  have hB : B[k.val]! = D.lifts[(selectedLiftIndex k).val]! := by
    rw [B, getElem!_pos (D.ag.map fun i => D.lifts[i]!) k.val
      (by rw [Array.size_map, hagSize]; exact k.isLt)]
    rw [Array.getElem_map]
    rw [← getElem!_pos D.ag k.val (by rw [hagSize]; exact k.isLt), selected_ag hcheck k]
  rw [hB]
  exact (rep_lift hcheck (selectedLiftIndex k)).1

private theorem rep_BI
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (k : Fin 4) :
    CFSG.Monster.B.Co2.Rep 2688 BI[k.val]! (liftPerm (selectedLiftIndex k))⁻¹ := by
  obtain ⟨-, -, hagSize, -, -, -, -, -, -, -, -, -, -⟩ := shape_facts hcheck
  have hB : BI[k.val]! = LI[(selectedLiftIndex k).val]! := by
    rw [BI, getElem!_pos (D.ag.map fun i => LI[i]!) k.val
      (by rw [Array.size_map, hagSize]; exact k.isLt)]
    rw [Array.getElem_map]
    rw [← getElem!_pos D.ag k.val (by rw [hagSize]; exact k.isLt), selected_ag hcheck k]
  rw [hB]
  exact (rep_lift hcheck (selectedLiftIndex k)).2

private def ksFam : ℕ → Equiv.Perm (Fin 2688) :=
  fun h => if hh : h ≤ 1 then ksPerm ⟨h, Nat.lt_succ_iff.mpr hh⟩ else 1

private theorem ksFam_rep
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ h < 2, CFSG.Monster.B.Co2.Rep 2688 D.ks[h]! (ksFam h) := by
  intro h hh
  have h1 := (rep_ks hcheck ⟨h, hh⟩).1
  rw [ksFam, dif_pos (Nat.lt_succ_iff.mp hh)]
  simpa using h1

private theorem ksFam_inv_rep
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ h < 2, CFSG.Monster.B.Co2.Rep 2688 KI[h]! ((ksFam h)⁻¹) := by
  intro h hh
  have h1 := (rep_ks hcheck ⟨h, hh⟩).2
  rw [ksFam, dif_pos (Nat.lt_succ_iff.mp hh)]
  simpa using h1

private theorem ksFam_eq (j : Fin 2) : ksFam j.val = ksPerm j := by
  rw [ksFam, dif_pos (Nat.lt_succ_iff.mp j.isLt)]

private theorem rep_word_ks
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (w : List ℤ) (hw : lettersOK 2 w = true) :
    CFSG.Monster.B.Co2.Rep 2688 (wordA 2688 D.ks KI w)
      (Quiver.SchreierGraph.evalWord (fun j : Fin 2 => ksPerm j) (toLetters 2 w)) := by
  have h := rep_wordA (n := 2688) (S := D.ks) (Sinv := KI) (gs := ksFam) (j := 2)
    (ksFam_rep hcheck) (ksFam_inv_rep hcheck) w hw
  have hfun : (fun j : Fin 2 => ksFam j.val) = fun j : Fin 2 => ksPerm j :=
    funext ksFam_eq
  rwa [hfun] at h

private def selFam : ℕ → Equiv.Perm (Fin 2688) :=
  fun h => if hh : h ≤ 3 then liftPerm (selectedLiftIndex ⟨h, Nat.lt_succ_iff.mpr hh⟩) else 1

private theorem selFam_rep
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ h < 4, CFSG.Monster.B.Co2.Rep 2688 B[h]! (selFam h) := by
  intro h hh
  have h1 := rep_B hcheck ⟨h, hh⟩
  rw [selFam, dif_pos (Nat.lt_succ_iff.mp hh)]
  simpa using h1

private theorem selFam_inv_rep
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ h < 4, CFSG.Monster.B.Co2.Rep 2688 BI[h]! ((selFam h)⁻¹) := by
  intro h hh
  have h1 := rep_BI hcheck ⟨h, hh⟩
  rw [selFam, dif_pos (Nat.lt_succ_iff.mp hh)]
  simpa using h1

private theorem selFam_eq (k : Fin 4) : selFam k.val = liftPerm (selectedLiftIndex k) := by
  rw [selFam, dif_pos (Nat.lt_succ_iff.mp k.isLt)]

private theorem rep_word_sel
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (w : List ℤ) (hw : lettersOK 4 w = true) :
    CFSG.Monster.B.Co2.Rep 2688 (wordA 2688 B BI w)
      (Quiver.SchreierGraph.evalWord
        (fun k : Fin 4 => liftPerm (selectedLiftIndex k)) (toLetters 4 w)) := by
  have h := rep_wordA (n := 2688) (S := B) (Sinv := BI) (gs := selFam) (j := 4)
    (selFam_rep hcheck) (selFam_inv_rep hcheck) w hw
  have hfun : (fun k : Fin 4 => selFam k.val) =
      fun k : Fin 4 => liftPerm (selectedLiftIndex k) :=
    funext selFam_eq
  rwa [hfun] at h

private theorem toLetters_reverse_neg (n : ℕ) (w : List ℤ) :
    CFSG.Monster.B.Co2.toLetters n (w.reverse.map fun l => -l) =
      FreeGroup.invRev (CFSG.Monster.B.Co2.toLetters n w) := by
  have hmap : CFSG.Monster.B.Co2.toLetters n (w.map fun l => -l) =
      (CFSG.Monster.B.Co2.toLetters n w).map (fun a => (a.1, !a.2)) := by
    rw [CFSG.Monster.B.Co2.toLetters, CFSG.Monster.B.Co2.toLetters,
      List.filterMap_map, List.map_filterMap]
    congr 1
    funext l
    by_cases h0 : l = 0
    · subst l
      simp
    · by_cases hb : l.natAbs ≤ n
      · by_cases hp : 0 < l
        · have hn : ¬ 0 < -l := by omega
          have hne : -l ≠ 0 := by omega
          have hle : 0 ≤ l := by omega
          simp [h0, hb, hne, hp, hle, Int.natAbs_neg]
        · have hn : 0 < -l := by omega
          have hne : -l ≠ 0 := by omega
          have hlt : l < 0 := by omega
          simp [h0, hb, hne, hp, hlt, Int.natAbs_neg]
      · have hnb : ¬ (-l).natAbs ≤ n := by simpa [Int.natAbs_neg] using hb
        have hne : -l ≠ 0 := by omega
        simp [h0, hb, hne, Int.natAbs_neg]
  rw [CFSG.Monster.B.Co2.toLetters, List.map_reverse, List.filterMap_reverse,
    ← CFSG.Monster.B.Co2.toLetters, hmap]
  rfl

private def ksWord (w : List ℤ) : Khat :=
  (FreeGroup.lift ksIn)
    (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2 w))

private theorem ksWord_coe (w : List ℤ) :
    (ksWord w : Equiv.Perm (Fin 2688)) =
      Quiver.SchreierGraph.evalWord (fun j : Fin 2 => ksPerm j)
        (CFSG.Monster.B.Co2.toLetters 2 w) := by
  unfold ksWord
  exact FreeGroup.lift_unique
    (f := fun j : Fin 2 => ksPerm j)
    (Khat.subtype.comp (FreeGroup.lift ksIn)) (fun j => rfl)

private theorem selected_words
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (k : Fin 4) (j : Fin 2) :
    (D.ag[k.val]! = (selectedLiftIndex k).val) ∧
    (D.nw[k.val]!.liftIndex = (selectedLiftIndex k).val) ∧
    (ksWord (D.nw[k.val]!.left[j.val]!) : Equiv.Perm (Fin 2688)) =
      liftPerm (selectedLiftIndex k) * ksPerm j * (liftPerm (selectedLiftIndex k))⁻¹ ∧
    (ksWord (D.nw[k.val]!.inverse[j.val]!) : Equiv.Perm (Fin 2688)) =
      (liftPerm (selectedLiftIndex k))⁻¹ * ksPerm j * liftPerm (selectedLiftIndex k) := by
  obtain ⟨-, -, hnorm, -, -⟩ := bridge_checks hcheck
  obtain ⟨-, -, -, -, -, -, -, -, hnwAll, -, -, -, -⟩ := shape_facts hcheck
  refine ⟨selected_ag hcheck k, ?_, ?_, ?_⟩
  · have hnw := hnwAll k.val k.isLt
    rw [hnw.1, selected_ag hcheck k]
  · have hnw := hnwAll k.val k.isLt
    have hletters : lettersOK 2 (D.nw[k.val]!.left[j.val]!) = true := by
      have hall : allLt (D.nw[k.val]!.left).size
          (fun i => lettersOK 2 (D.nw[k.val]!.left[i]!)) = true := by
        simpa [wordsLettersOK] using hnw.2.2.2.1
      exact allLt_spec hall (by rw [hnw.2.1]; exact j.isLt)
    have hnorm' := hnorm
    unfold normalizerCheck at hnorm'
    have hkj := allLt_spec (allLt_spec hnorm' k.isLt) j.isLt
    simp only [Bool.and_eq_true] at hkj
    have hL := rep_word_ks hcheck (D.nw[k.val]!.left[j.val]!) hletters
    have hR := rep_compA (rep_compA (rep_B hcheck k) (rep_ks hcheck j).1) (rep_BI hcheck k)
    have heq := eq_of_eqA hL hR hkj.1
    rw [ksWord_coe]
    exact heq
  · have hnw := hnwAll k.val k.isLt
    have hletters : lettersOK 2 (D.nw[k.val]!.inverse[j.val]!) = true := by
      have hall : allLt (D.nw[k.val]!.inverse).size
          (fun i => lettersOK 2 (D.nw[k.val]!.inverse[i]!)) = true := by
        simpa [wordsLettersOK] using hnw.2.2.2.2
      exact allLt_spec hall (by rw [hnw.2.2.1]; exact j.isLt)
    have hnorm' := hnorm
    unfold normalizerCheck at hnorm'
    have hkj := allLt_spec (allLt_spec hnorm' k.isLt) j.isLt
    simp only [Bool.and_eq_true] at hkj
    have hL := rep_word_ks hcheck (D.nw[k.val]!.inverse[j.val]!) hletters
    have hR := rep_compA (rep_compA (rep_BI hcheck k) (rep_ks hcheck j).1) (rep_B hcheck k)
    have heq := eq_of_eqA hL hR hkj.2
    rw [ksWord_coe]
    exact heq

private theorem selected_mem_normalizer
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (k : Fin 4) :
    liftPerm (selectedLiftIndex k) ∈
      Subgroup.normalizer (Khat : Set (Equiv.Perm (Fin 2688))) := by
  let b := liftPerm (selectedLiftIndex k)
  have hleft (j : Fin 2) : b * ksPerm j * b⁻¹ ∈ Khat := by
    have h := (selected_words hcheck k j).2.2.1
    rw [← h]
    exact (ksWord (D.nw[k.val]!.left[j.val]!)).2
  have hright (j : Fin 2) : b⁻¹ * ksPerm j * b ∈ Khat := by
    have h := (selected_words hcheck k j).2.2.2
    rw [← h]
    exact (ksWord (D.nw[k.val]!.inverse[j.val]!)).2
  have hmap : Khat.map (MulAut.conj b).toMonoidHom ≤ Khat := by
    rw [Khat, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, rfl⟩ := hx
    simpa [MulAut.conj_apply, Khat] using hleft j
  have hmapInv : Khat.map (MulAut.conj b⁻¹).toMonoidHom ≤ Khat := by
    rw [Khat, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, rfl⟩ := hx
    simpa [MulAut.conj_apply, Khat] using hright j
  have hconj (x : Equiv.Perm (Fin 2688)) (hx : x ∈ Khat) : b * x * b⁻¹ ∈ Khat := by
    have hmem := hmap (Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hx)
    simpa [MulAut.conj_apply] using hmem
  have hconjInv (x : Equiv.Perm (Fin 2688)) (hx : x ∈ Khat) : b⁻¹ * x * b ∈ Khat := by
    have hmem := hmapInv (Subgroup.mem_map_of_mem (MulAut.conj b⁻¹).toMonoidHom hx)
    simpa [MulAut.conj_apply] using hmem
  change b ∈ Subgroup.normalizer (Khat : Set (Equiv.Perm (Fin 2688)))
  refine (Subgroup.mem_normalizer_iff'').mpr ?_
  intro x
  constructor
  · exact hconjInv x
  · intro hx
    have h := hconj (b⁻¹ * x * b) hx
    have hcalc : b * (b⁻¹ * x * b) * b⁻¹ = x := by
      calc
        b * (b⁻¹ * x * b) * b⁻¹ = b * (b⁻¹ * (x * b)) * b⁻¹ := by
          rw [mul_assoc (b⁻¹) x b]
        _ = (x * b) * b⁻¹ := by rw [mul_inv_cancel_left]
        _ = x := mul_inv_cancel_right x b
    rwa [hcalc] at h

private def parentLift (i : Fin 256) : Equiv.Perm (Fin 2688) :=
  (FreeGroup.lift (fun k : Fin 4 => liftPerm (selectedLiftIndex k)))
    (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 4 D.parent[i.val]!))

private abbrev N : Subgroup (Equiv.Perm (Fin 2688)) :=
  Subgroup.normalizer (Khat : Set (Equiv.Perm (Fin 2688)))

private def selN (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Fin 4 → N :=
  fun k => ⟨liftPerm (selectedLiftIndex k), selected_mem_normalizer hcheck k⟩

private theorem selN_coe
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (x : FreeGroup (Fin 4)) :
    ((FreeGroup.lift (selN hcheck) x : N) : Equiv.Perm (Fin 2688)) =
      (FreeGroup.lift (fun k : Fin 4 => liftPerm (selectedLiftIndex k)) x) := by
  exact FreeGroup.lift_unique
    (f := fun k : Fin 4 => liftPerm (selectedLiftIndex k))
    (N.subtype.comp (FreeGroup.lift (selN hcheck))) (fun _ => rfl)

private theorem U_get
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) :
    U[i.val]! = wordA 2688 B BI D.parent[i.val]! := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpar, -⟩ := shape_facts hcheck
  rw [U, getElem!_pos (D.parent.map fun w => wordA 2688 B BI w) i.val
      (by rw [Array.size_map, hpar]; exact i.isLt), Array.getElem_map]
  rw [getElem!_pos D.parent i.val (by rw [hpar]; exact i.isLt)]

private theorem UI_get
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) :
    UI[i.val]! = wordA 2688 B BI (D.parent[i.val]!.reverse.map fun l => -l) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpar, -⟩ := shape_facts hcheck
  rw [UI, getElem!_pos
      (D.parent.map fun w => wordA 2688 B BI (w.reverse.map fun l => -l)) i.val
      (by rw [Array.size_map, hpar]; exact i.isLt), Array.getElem_map]
  rw [getElem!_pos D.parent i.val (by rw [hpar]; exact i.isLt)]

private theorem parent_mem_normalizer
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) : parentLift i ∈ N := by
  let x := FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 4 D.parent[i.val]!)
  have hcoe := selN_coe hcheck x
  rw [parentLift]
  rw [← hcoe]
  exact (FreeGroup.lift (selN hcheck) x).2

private theorem parent_conj
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) (j : Fin 2) :
    liftPerm i * ksPerm j * (liftPerm i)⁻¹ =
      parentLift i * ksPerm j * (parentLift i)⁻¹ := by
  obtain ⟨-, -, -, hparent, -⟩ := bridge_checks hcheck
  let w := D.parent[i.val]!
  have hw : lettersOK 4 w = true := parent_letters hcheck i
  have hwr : lettersOK 4 (w.reverse.map fun l => -l) = true := by
    rw [lettersOK, List.all_eq_true] at hw ⊢
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
    have hlw : l0 ∈ w := List.mem_reverse.mp hl0
    simpa [Int.natAbs_neg, neg_eq_zero] using hw l0 hlw
  have hparent' := hparent
  unfold parentCheck at hparent'
  have h := allLt_spec (allLt_spec hparent' i.isLt) j.isLt
  have hUrep : CFSG.Monster.B.Co2.Rep 2688 U[i.val]!
      (Quiver.SchreierGraph.evalWord
        (fun k : Fin 4 => liftPerm (selectedLiftIndex k))
        (CFSG.Monster.B.Co2.toLetters 4 w)) := by
    rw [U_get hcheck i]
    exact rep_word_sel hcheck w hw
  have hUIrep : CFSG.Monster.B.Co2.Rep 2688 UI[i.val]!
      ((Quiver.SchreierGraph.evalWord
        (fun k : Fin 4 => liftPerm (selectedLiftIndex k))
        (CFSG.Monster.B.Co2.toLetters 4 w))⁻¹) := by
    rw [UI_get hcheck i]
    have hrep := rep_word_sel hcheck (w.reverse.map fun l => -l) hwr
    have hneg : Quiver.SchreierGraph.evalWord
        (fun k : Fin 4 => liftPerm (selectedLiftIndex k))
        (CFSG.Monster.B.Co2.toLetters 4 (w.reverse.map fun l => -l)) =
        (Quiver.SchreierGraph.evalWord
          (fun k : Fin 4 => liftPerm (selectedLiftIndex k))
          (CFSG.Monster.B.Co2.toLetters 4 w))⁻¹ := by
      rw [Quiver.SchreierGraph.evalWord, toLetters_reverse_neg, ← FreeGroup.inv_mk,
        map_inv]
      rfl
    rwa [hneg] at hrep
  have hleft : CFSG.Monster.B.Co2.Rep 2688
      (compA 2688 (compA 2688 D.lifts[i.val]! D.ks[j.val]!) LI[i.val]!)
      (liftPerm i * ksPerm j * (liftPerm i)⁻¹) :=
    rep_compA (rep_compA (rep_lift hcheck i).1 (rep_ks hcheck j).1) (rep_lift hcheck i).2
  have hright : CFSG.Monster.B.Co2.Rep 2688
      (compA 2688 (compA 2688 U[i.val]! D.ks[j.val]!) UI[i.val]!)
      (Quiver.SchreierGraph.evalWord
          (fun k : Fin 4 => liftPerm (selectedLiftIndex k))
          (CFSG.Monster.B.Co2.toLetters 4 w) * ksPerm j *
        (Quiver.SchreierGraph.evalWord
          (fun k : Fin 4 => liftPerm (selectedLiftIndex k))
          (CFSG.Monster.B.Co2.toLetters 4 w))⁻¹) :=
    rep_compA (rep_compA hUrep (rep_ks hcheck j).1) hUIrep
  have heq := eq_of_eqA hleft hright h
  rw [parentLift]
  simpa only [Quiver.SchreierGraph.evalWord] using heq

private theorem conj_eq_on_Khat
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) :
    Set.EqOn (MulAut.conj (liftPerm i)).toMonoidHom
      (MulAut.conj (parentLift i)).toMonoidHom (Khat : Set (Equiv.Perm (Fin 2688))) := by
  change Set.EqOn (MulAut.conj (liftPerm i)).toMonoidHom
    (MulAut.conj (parentLift i)).toMonoidHom
    (Subgroup.closure (Set.range ksPerm) : Set (Equiv.Perm (Fin 2688)))
  refine MonoidHom.eqOn_closure (s := Set.range ksPerm) ?_
  rintro x ⟨j, rfl⟩
  simpa [MulAut.conj_apply] using parent_conj hcheck i j

theorem lift_mem_normalizer
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) :
    liftPerm i ∈ Subgroup.normalizer (Khat : Set (Equiv.Perm (Fin 2688))) := by
  have hmap : Khat.map (MulAut.conj (liftPerm i)).toMonoidHom =
      Khat.map (MulAut.conj (parentLift i)).toMonoidHom := by
    apply le_antisymm
    · rintro x hx
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, (conj_eq_on_Khat hcheck i hy).symm⟩
    · rintro x hx
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, conj_eq_on_Khat hcheck i hy⟩
  have hp : Khat.map (MulAut.conj (parentLift i)).toMonoidHom = Khat := by
    simpa using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (parent_mem_normalizer hcheck i))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Khat.map (MulAut.conj (liftPerm i)).toMonoidHom = Khat
  rw [hmap, hp]

@[expose] def alpha
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) : MulAut Khat :=
  Khat.normalizerMonoidHom ⟨liftPerm i, lift_mem_normalizer hcheck i⟩

@[expose] def T
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Subgroup (MulAut Khat) :=
  Subgroup.closure (Set.range (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k)))

private theorem alpha_apply_coe
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) (x : Khat) :
    (alpha hcheck i x : Equiv.Perm (Fin 2688)) =
      liftPerm i * (x : Equiv.Perm (Fin 2688)) * (liftPerm i)⁻¹ := by
  simp [alpha]

private theorem alpha_parent_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) :
    alpha hcheck i =
      Khat.normalizerMonoidHom
        ⟨parentLift i, parent_mem_normalizer hcheck i⟩ := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [alpha_apply_coe, Subgroup.normalizerMonoidHom_apply_apply_coe]
  simpa [MulAut.conj_apply] using conj_eq_on_Khat hcheck i x.2

private theorem alpha_eq_lift_parent
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) :
    alpha hcheck i =
      (FreeGroup.lift (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k)))
        (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 4 D.parent[i.val]!)) := by
  let x := FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 4 D.parent[i.val]!)
  let bN := selN hcheck
  have hsub : (FreeGroup.lift bN x : N) =
      ⟨parentLift i, parent_mem_normalizer hcheck i⟩ := by
    apply Subtype.ext
    rw [selN_coe]
    rfl
  have hcomp : (Khat.normalizerMonoidHom.comp (FreeGroup.lift bN)) x =
      (FreeGroup.lift (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k))) x :=
    FreeGroup.lift_unique
      (f := fun k : Fin 4 => alpha hcheck (selectedLiftIndex k))
      (g := Khat.normalizerMonoidHom.comp (FreeGroup.lift bN)) (fun k => rfl)
  calc
    alpha hcheck i =
        Khat.normalizerMonoidHom ⟨parentLift i, parent_mem_normalizer hcheck i⟩ :=
      alpha_parent_eq hcheck i
    _ = Khat.normalizerMonoidHom (FreeGroup.lift bN x) := by rw [← hsub]
    _ = (Khat.normalizerMonoidHom.comp (FreeGroup.lift bN)) x := rfl
    _ = (FreeGroup.lift (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k))) x := hcomp

private theorem alpha_mem_T
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) : alpha hcheck i ∈ T hcheck := by
  rw [alpha_eq_lift_parent]
  have hmem : (FreeGroup.lift (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k)))
      (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 4 D.parent[i.val]!)) ∈
      (FreeGroup.lift (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k))).range :=
    ⟨_, rfl⟩
  rw [FreeGroup.range_lift_eq_closure] at hmem
  simpa [T] using hmem

private theorem sig_get (i j : ℕ) (hi : i < 256) (hj : j < 2) :
    (sig[i]!)[j]! = compA 2688 (compA 2688 D.lifts[i]! D.ks[j]!) LI[i]! := by
  rw [sig]
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  rw [getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj), Array.getElem_ofFn]

private theorem sig_rep
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) (j : Fin 2) :
    CFSG.Monster.B.Co2.Rep 2688 ((sig[i.val]!)[j.val]!)
      (liftPerm i * ksPerm j * (liftPerm i)⁻¹) := by
  rw [sig_get i.val j.val i.isLt j.isLt]
  exact rep_compA (rep_compA (rep_lift hcheck i).1 (rep_ks hcheck j).1) (rep_lift hcheck i).2

private theorem alpha_zero
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    alpha hcheck 0 = 1 := by
  obtain ⟨-, -, -, -, htrans⟩ := bridge_checks hcheck
  have htrans' := htrans
  unfold transitionCheck at htrans'
  simp only [Bool.and_eq_true, and_assoc] at htrans'
  have hfirst := htrans'.1
  have hgen (j : Fin 2) : (MulAut.conj (liftPerm 0)) (ksPerm j) = ksPerm j := by
    have h := allLt_spec hfirst j.isLt
    have heq := eq_of_eqA (sig_rep hcheck 0 j) (rep_ks hcheck j).1 h
    simpa [MulAut.conj_apply] using heq
  have heqOn : Set.EqOn (MulAut.conj (liftPerm 0)).toMonoidHom
      (MonoidHom.id (Equiv.Perm (Fin 2688))) (Khat : Set (Equiv.Perm (Fin 2688))) := by
    change Set.EqOn (MulAut.conj (liftPerm 0)).toMonoidHom
      (MonoidHom.id (Equiv.Perm (Fin 2688)))
      (Subgroup.closure (Set.range ksPerm) : Set (Equiv.Perm (Fin 2688)))
    refine MonoidHom.eqOn_closure (s := Set.range ksPerm) ?_
    rintro x ⟨j, rfl⟩
    simpa using hgen j
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [alpha_apply_coe]
  rw [MulAut.one_apply]
  simpa [MulAut.conj_apply] using heqOn x.2

private theorem transition_lt
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) (k : Fin 4) :
    (D.tr[i.val]!)[k.val]! < 256 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, htr, htrSpec, -, -⟩ := shape_facts hcheck
  exact (htrSpec i.val i.isLt).2 k.val k.isLt

private def transitionIndex
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) (k : Fin 4) : Fin 256 :=
  ⟨(D.tr[i.val]!)[k.val]!, transition_lt hcheck i k⟩

private theorem alpha_mul_of_conj
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (a b c : Fin 256)
    (h : Set.EqOn (MulAut.conj (liftPerm a)).toMonoidHom
      (MulAut.conj (liftPerm b * liftPerm c)).toMonoidHom
      (Khat : Set (Equiv.Perm (Fin 2688)))) :
    alpha hcheck a = alpha hcheck b * alpha hcheck c := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hx := h (x := x) x.2
  change (MulAut.conj (liftPerm a)) (x : Equiv.Perm (Fin 2688)) =
    (MulAut.conj (liftPerm b * liftPerm c)) (x : Equiv.Perm (Fin 2688)) at hx
  simp only [MulAut.conj_apply] at hx
  rw [alpha_apply_coe, MulAut.mul_apply, alpha_apply_coe, alpha_apply_coe]
  rw [hx]
  simp only [mul_inv_rev, mul_assoc]

private theorem transition_action
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 256) (k : Fin 4) :
    alpha hcheck (transitionIndex hcheck i k) =
      alpha hcheck i * alpha hcheck (selectedLiftIndex k) := by
  obtain ⟨-, -, -, -, htrans⟩ := bridge_checks hcheck
  have htrans' := htrans
  unfold transitionCheck at htrans'
  simp only [Bool.and_eq_true, and_assoc] at htrans'
  have hrow := htrans'.2.1
  refine alpha_mul_of_conj hcheck (transitionIndex hcheck i k) i (selectedLiftIndex k) ?_
  change Set.EqOn
    (MulAut.conj (liftPerm (transitionIndex hcheck i k))).toMonoidHom
    (MulAut.conj (liftPerm i * liftPerm (selectedLiftIndex k))).toMonoidHom
    (Subgroup.closure (Set.range ksPerm) : Set (Equiv.Perm (Fin 2688)))
  refine MonoidHom.eqOn_closure (s := Set.range ksPerm) ?_
  rintro x ⟨j, rfl⟩
  have hkj := allLt_spec (allLt_spec hrow i.isLt) k.isLt
  have hsigk : (sig[D.ag[k.val]!]!)[j.val]! =
      (sig[(selectedLiftIndex k).val]!)[j.val]! := by
    rw [selected_ag hcheck k]
  have hRrep : CFSG.Monster.B.Co2.Rep 2688
      (compA 2688 (compA 2688 D.lifts[i.val]! (sig[D.ag[k.val]!]!)[j.val]!) LI[i.val]!)
      (liftPerm i * (liftPerm (selectedLiftIndex k) * ksPerm j *
        (liftPerm (selectedLiftIndex k))⁻¹) * (liftPerm i)⁻¹) := by
    rw [hsigk]
    exact rep_compA
      (rep_compA (rep_lift hcheck i).1 (sig_rep hcheck (selectedLiftIndex k) j))
      (rep_lift hcheck i).2
  have heq := eq_of_eqA (sig_rep hcheck (transitionIndex hcheck i k) j) hRrep
    (allLt_spec hkj j.isLt)
  show (MulAut.conj (liftPerm (transitionIndex hcheck i k))) (ksPerm j) =
    (MulAut.conj (liftPerm i * liftPerm (selectedLiftIndex k))) (ksPerm j)
  rw [MulAut.conj_apply, MulAut.conj_apply]
  rw [heq]
  rw [mul_inv_rev]
  simp only [mul_assoc]

private theorem separation
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i j : Fin 256) (hij : i.val < j.val) :
    (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) 0 ≠
        (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) 0 ∨
      (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) 217 ≠
        (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) 217 := by
  obtain ⟨-, -, -, -, htrans⟩ := bridge_checks hcheck
  have htrans' := htrans
  unfold transitionCheck at htrans'
  simp only [Bool.and_eq_true, and_assoc] at htrans'
  have hsep := allLt_spec (allLt_spec htrans'.2.2 i.isLt) j.isLt
  have hlt : decide (i.val < j.val) = true := decide_eq_true hij
  simp only [hlt, Bool.not_true, Bool.false_or, Bool.or_eq_true, bne_iff_ne] at hsep
  have hci : (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) =
      liftPerm i * ksPerm 0 * (liftPerm i)⁻¹ := by
    simpa only [ksIn] using alpha_apply_coe hcheck i (ksIn 0)
  have hcj : (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) =
      liftPerm j * ksPerm 0 * (liftPerm j)⁻¹ := by
    simpa only [ksIn] using alpha_apply_coe hcheck j (ksIn 0)
  rcases hsep with h0 | h217
  · left
    intro heq
    apply h0
    have hval : (((alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688))) 0).val =
        (((alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688))) 0).val := congrArg Fin.val heq
    rw [show (((alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688))) 0).val =
        (((liftPerm i * ksPerm 0 * (liftPerm i)⁻¹) : Equiv.Perm (Fin 2688)) 0).val
      from congrArg (fun p : Equiv.Perm (Fin 2688) => (p 0).val) hci] at hval
    rw [show (((alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688))) 0).val =
        (((liftPerm j * ksPerm 0 * (liftPerm j)⁻¹) : Equiv.Perm (Fin 2688)) 0).val
      from congrArg (fun p : Equiv.Perm (Fin 2688) => (p 0).val) hcj] at hval
    have h0i : ((sig[i.val]!)[0]!)[(0 : Fin 2688).val]! =
        (((liftPerm i * ksPerm 0 * (liftPerm i)⁻¹) : Equiv.Perm (Fin 2688)) 0 : ℕ) :=
      (sig_rep hcheck i 0) (0 : Fin 2688)
    have h0j : ((sig[j.val]!)[0]!)[(0 : Fin 2688).val]! =
        (((liftPerm j * ksPerm 0 * (liftPerm j)⁻¹) : Equiv.Perm (Fin 2688)) 0 : ℕ) :=
      (sig_rep hcheck j 0) (0 : Fin 2688)
    exact h0i.trans (hval.trans h0j.symm)
  · right
    intro heq
    apply h217
    have hval : (((alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688))) 217).val =
        (((alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688))) 217).val := congrArg Fin.val heq
    rw [show (((alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688))) 217).val =
        (((liftPerm i * ksPerm 0 * (liftPerm i)⁻¹) : Equiv.Perm (Fin 2688)) 217).val
      from congrArg (fun p : Equiv.Perm (Fin 2688) => (p 217).val) hci] at hval
    rw [show (((alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688))) 217).val =
        (((liftPerm j * ksPerm 0 * (liftPerm j)⁻¹) : Equiv.Perm (Fin 2688)) 217).val
      from congrArg (fun p : Equiv.Perm (Fin 2688) => (p 217).val) hcj] at hval
    have h1i : ((sig[i.val]!)[0]!)[(217 : Fin 2688).val]! =
        (((liftPerm i * ksPerm 0 * (liftPerm i)⁻¹) : Equiv.Perm (Fin 2688)) 217 : ℕ) :=
      (sig_rep hcheck i 0) (217 : Fin 2688)
    have h1j : ((sig[j.val]!)[0]!)[(217 : Fin 2688).val]! =
        (((liftPerm j * ksPerm 0 * (liftPerm j)⁻¹) : Equiv.Perm (Fin 2688)) 217 : ℕ) :=
      (sig_rep hcheck j 0) (217 : Fin 2688)
    exact h1i.trans (hval.trans h1j.symm)

private theorem alpha_injective
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Function.Injective (alpha hcheck) := by
  intro i j hij
  by_contra hne
  have hvalne : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have hlt : i.val < j.val ∨ j.val < i.val := by omega
  rcases hlt with h | h
  · rcases separation hcheck i j h with h0 | h217
    · apply h0
      have hperm : (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) =
          (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) :=
        congrArg (fun f : MulAut Khat => (f (ksIn 0) : Equiv.Perm (Fin 2688))) hij
      simpa using congrArg (fun p : Equiv.Perm (Fin 2688) => p 0) hperm
    · apply h217
      have hperm : (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) =
          (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) :=
        congrArg (fun f : MulAut Khat => (f (ksIn 0) : Equiv.Perm (Fin 2688))) hij
      simpa using congrArg (fun p : Equiv.Perm (Fin 2688) => p 217) hperm
  · rcases separation hcheck j i h with h0 | h217
    · apply h0
      have hperm : (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) =
          (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) :=
        congrArg (fun f : MulAut Khat => (f (ksIn 0) : Equiv.Perm (Fin 2688))) hij.symm
      simpa using congrArg (fun p : Equiv.Perm (Fin 2688) => p 0) hperm
    · apply h217
      have hperm : (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) =
          (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) :=
        congrArg (fun f : MulAut Khat => (f (ksIn 0) : Equiv.Perm (Fin 2688))) hij.symm
      simpa using congrArg (fun p : Equiv.Perm (Fin 2688) => p 217) hperm

private theorem coverage
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ a : MulAut Khat, a ∈ T hcheck ↔ ∃ i : Fin 256, alpha hcheck i = a := by
  let rg : List (MulAut Khat) :=
    List.ofFn (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k))
  let Rl : List (MulAut Khat) := List.ofFn (alpha hcheck)
  have hclosure : Subgroup.closure {g | g ∈ rg} = T hcheck := by
    rw [T]
    apply congrArg Subgroup.closure
    ext a
    change a ∈ List.ofFn (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k)) ↔
      a ∈ Set.range (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k))
    rw [List.mem_ofFn, Set.mem_range]
  have hRl : ∀ x ∈ Rl, x ∈ Subgroup.closure {g | g ∈ rg} := by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hclosure]
    exact alpha_mem_T hcheck i
  have h1 : (1 : MulAut Khat) ∈ Rl := by
    rw [List.mem_ofFn]
    exact ⟨0, alpha_zero hcheck⟩
  have hgen : ∀ x ∈ Rl, ∀ g ∈ rg, x * g ∈ Rl := by
    intro x hx g hg
    rw [List.mem_ofFn] at hx hg
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := hg
    rw [List.mem_ofFn]
    exact ⟨transitionIndex hcheck i k, transition_action hcheck i k⟩
  have hcov := @CFSG.QuasithinUnique.Vol2Native.L239.subgroupOfGens_exists
    (MulAut Khat) inferInstance (MulEquiv.finite_left) rg Rl hRl h1 hgen
  intro a
  constructor
  · intro ha
    rw [← hclosure] at ha
    exact List.mem_ofFn.mp ((hcov a).1 ha)
  · rintro ⟨i, rfl⟩
    exact alpha_mem_T hcheck i

private theorem card_T
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card (T hcheck) = 256 := by
  let f : Fin 256 → T hcheck := fun i => ⟨alpha hcheck i, alpha_mem_T hcheck i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply alpha_injective hcheck
      exact congrArg Subtype.val hij
    · intro a
      obtain ⟨i, hi⟩ := (coverage hcheck a).1 a.2
      exact ⟨i, Subtype.ext hi⟩
  have hcard : Nat.card (Fin 256) = Nat.card (T hcheck) :=
    Nat.card_congr (Equiv.ofBijective f hf)
  simpa using hcard.symm

theorem original_actions_spec
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (∀ (i : Fin 256) (x : Khat),
      (alpha hcheck i x : Equiv.Perm (Fin 2688)) =
        liftPerm i * (x : Equiv.Perm (Fin 2688)) * (liftPerm i)⁻¹) ∧
    (∀ i : Fin 256,
      alpha hcheck i =
        (FreeGroup.lift (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k)))
          (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 4
            (PermutationNative.inputs ()).parent[i.val]!))) ∧
    (∀ i : Fin 256, alpha hcheck i ∈ T hcheck) ∧
    alpha hcheck 0 = 1 ∧
    (∀ (i : Fin 256) (k : Fin 4), ∃ q : Fin 256,
      q.val = ((PermutationNative.inputs ()).tr[i.val]!)[k.val]! ∧
      alpha hcheck q = alpha hcheck i * alpha hcheck (selectedLiftIndex k)) ∧
    (∀ i j : Fin 256, i.val < j.val →
      (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) 0 ≠
          (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) 0 ∨
        (alpha hcheck i (ksIn 0) : Equiv.Perm (Fin 2688)) 217 ≠
          (alpha hcheck j (ksIn 0) : Equiv.Perm (Fin 2688)) 217) ∧
    Function.Injective (alpha hcheck) ∧
    (∀ a : MulAut Khat, a ∈ T hcheck ↔ ∃ i : Fin 256, alpha hcheck i = a) ∧
    Nat.card (T hcheck) = 256 := by
  exact ⟨alpha_apply_coe hcheck, alpha_eq_lift_parent hcheck, alpha_mem_T hcheck,
    alpha_zero hcheck,
    fun i k => ⟨transitionIndex hcheck i k, rfl, transition_action hcheck i k⟩,
    separation hcheck, alpha_injective hcheck, coverage hcheck, card_T hcheck⟩

end CFSG.GH74.GLS.NT44.PermutationActions
