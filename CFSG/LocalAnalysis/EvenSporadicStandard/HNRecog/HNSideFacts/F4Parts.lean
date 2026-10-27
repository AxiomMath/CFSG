module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Inputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native

theorem sideF4QOK_parts (h : sideF4QOK = true) :
    qWordsJ.size = 8 ∧ InvData.qPerms.size = 8 ∧ s800.size = 11 ∧
      ∀ i < 8, plettersOK 10 qWordsJ[i]! = true ∧
        peq 800 (pword 800 s800 (pinvs 800 s800) qWordsJ[i]!) InvData.qPerms[i]! = true := by
  unfold sideF4QOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  have := allBelowN_spec h4 hi
  simpa only [Bool.and_eq_true] using this

theorem sideF4PlusOK_parts (h : sideF4PlusOK = true) :
    s12.size = 9 ∧ eWords.size = 5 ∧ eMasks.size = 5 ∧
      (∀ k < 9, pisInv 12 s12[k]! (pinvs 12 s12)[k]! = true) ∧
      (∀ i < 5, plettersOK 9 eWords[i]! = true ∧ eMasks[i]! < 256 ∧
        peq 800 (pword 800 s800 (pinvs 800 s800) eWords[i]!)
          (qbList 800 InvData.qPerms)[eMasks[i]!]! = true) ∧
      plettersOK 9 bWord = true ∧ bMask < 256 ∧
      peq 800 (pword 800 s800 (pinvs 800 s800) bWord) (qbList 800 InvData.qPerms)[bMask]! = true ∧
      (∀ i < 5, ∀ j < 5,
        peq 12 (pcomp 12 evArr[i]! evArr[j]!) (pcomp 12 evArr[j]! evArr[i]!) = true) ∧
      (∀ i < 5, peq 12 (pcomp 12 evArr[i]! evArr[i]!) (pid 12) = true) ∧
      (∀ a < 32, ∀ b < 32, b ≤ a ∨ peq 12 (subProd12 evArr a) (subProd12 evArr b) = false) ∧
      peq 12 (pcomp 12 evArr[3]! bvArr) (pcomp 12 bvArr evArr[3]!) = false := by
  unfold sideF4PlusOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, h2, h3, fun k hk => allBelowN_spec h4 hk, fun i hi => ?_, h6, h7, h8,
    fun i hi j hj => allBelowN_spec (allBelowN_spec h9 hi) hj,
    fun i hi => allBelowN_spec h10 hi, fun a ha b hb => ?_, h12⟩
  · have := allBelowN_spec h5 hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allBelowN_spec (allBelowN_spec h11 ha) hb
    simpa only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] using this

theorem sideF4FamOK_parts (h : sideF4FamOK = true) :
    subsData.size = 10 ∧ sigArrs.size = 10 ∧
      (∀ s < 10, ∀ i < 10, ∀ m < 256,
        inV ((sigArrs[s]!)[i]!) m = inV i ((colPerms[s]!)[m]!)) ∧
      (∀ i < 10, ∀ j < 10, j ≤ i ∨ ∃ m < 256, inV i m ≠ inV j m) ∧
      (∀ s < 10, pisInv 10 sigArrs[s]! (pinvCand 10 sigArrs[s]!) = true) ∧
      chainCheck 10 sigArrs sigWords sigBase sigSizes = true := by
  unfold sideF4FamOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, fun s hs i hi m hm => ?_, fun i hi j hj => ?_, fun s hs => allBelowN_spec h5 hs, h6⟩
  · have := allBelowN_spec (allBelowN_spec (allBelowN_spec h3 hs) hi) hm
    simpa only [beq_iff_eq] using this
  · have := allBelowN_spec (allBelowN_spec h4 hi) hj
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      bne_iff_ne, ne_eq] at this
    exact this

end CFSG.EvenSporadicStandard.HNRecog.SideF4
