module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28TCheck

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem semiComm_iff {a b : Array ℕ × ℕ} : semiComm a b = true ↔ semi a b = semi b a := by
  simp [semiComm]

theorem frobStable_spec {L : Array (Array ℕ)} (h : frobStable L = true) :
    ∀ n < L.size, ∃ m < L.size, frobCode L[n]! = L[m]! := by
  simp only [frobStable, List.all_eq_true, List.mem_range, Array.contains_iff_mem] at h
  intro n hn
  obtain ⟨m, hm, hm'⟩ := Array.mem_iff_getElem.mp (h n hn)
  exact ⟨m, hm, by rw [getElem!_pos L m hm, hm']⟩

theorem centerOK_spec {L : Array (Array ℕ)} {gens : List (Array ℕ × ℕ)} {zc : Array ℕ}
    (h : centerOK L gens zc = true) : ∀ n < 243, ∀ s < 3,
    (∀ g ∈ gens, semi (L[n]!, s) g = semi g (L[n]!, s)) →
      s = 0 ∧ (L[n]! = idCode ∨ L[n]! = zc ∨ L[n]! = mulCode zc zc) := by
  simp only [centerOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq] at h
  intro n hn s hs hg
  rcases h n hn s hs with h1 | ⟨h2, h3⟩
  · exfalso
    have : gens.all (fun g => semiComm (L[n]!, s) g) = true := by
      simp only [List.all_eq_true]
      intro g hg'
      exact semiComm_iff.mpr (hg g hg')
    rw [this] at h1
    exact absurd h1 (by simp)
  · refine ⟨h2, ?_⟩
    simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using h3

theorem zOKc_spec {L : Array (Array ℕ)} {zc : Array ℕ} {gens : List (Array ℕ × ℕ)}
    (h : zOKc L zc gens = true) : zc ≠ idCode ∧ powCode zc 3 = idCode ∧ frobCode zc = zc ∧
      L[81]! = zc ∧ ∀ g ∈ gens, semi (zc, 0) g = semi g (zc, 0) := by
  simp only [zOKc, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun g hg => semiComm_iff.mp (h5 g hg)⟩

theorem getElem!_aList (U Z : Array ℕ) {t : ℕ} (ht : t < 81) :
    (aList U Z)[t]! = mulCode (powCode U (t / 9)) (powCode Z (t % 9)) := by
  rw [aList, getElem!_ofFn_nat' _ ht]

theorem getElem!_qList (zc b : Array ℕ) {t : ℕ} (ht : t < 9) :
    (qList zc b)[t]! = mulCode (powCode zc (t / 3)) (powCode b (t % 3)) := by
  rw [qList, getElem!_ofFn_nat' _ ht]

theorem size_aList (U Z : Array ℕ) : (aList U Z).size = 81 := by simp [aList]

theorem size_qList (zc b : Array ℕ) : (qList zc b).size = 9 := by simp [qList]

theorem aOK_spec {L : Array (Array ℕ)} {U Z : Array ℕ} (h : aOK L U Z = true) :
    (aList U Z)[0]! = idCode ∧
    (∀ i < 81, ∀ j < 81, ∃ k < 81, mulCode (aList U Z)[i]! (aList U Z)[j]! = (aList U Z)[k]!) ∧
    (∀ i < 81, ∃ j < 81, mulCode (aList U Z)[i]! (aList U Z)[j]! = idCode) ∧
    (∀ i < 81, ∀ j < i, (aList U Z)[i]! ≠ (aList U Z)[j]!) ∧
    (∀ i < 81, ∃ n < L.size, (aList U Z)[i]! = L[n]!) := by
  simp only [aOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, List.any_eq_true, Array.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h0, hm⟩, hi⟩, hd⟩, hl⟩ := h
  refine ⟨h0, fun i hi' j hj => ?_, fun i hi' => ?_, fun i hi' j hj => hd i hi' j hj,
    fun i hi' => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Array.mem_iff_getElem.mp (hm i hi' j hj)
    rw [size_aList] at hk
    exact ⟨k, hk, by rw [getElem!_pos _ k (by rw [size_aList]; exact hk), hk']⟩
  · obtain ⟨j, hj, hj'⟩ := hi i hi'
    exact ⟨j, hj, hj'⟩
  · obtain ⟨n, hn, hn'⟩ := Array.mem_iff_getElem.mp (hl i hi')
    exact ⟨n, hn, by rw [getElem!_pos L n hn, hn']⟩

theorem omegaOK_spec {U Z : Array ℕ} (h : omegaOK U Z = true) :
    ∀ t < 81, powCode (aList U Z)[t]! 3 = idCode → t / 9 % 3 = 0 ∧ t % 9 % 3 = 0 := by
  simp only [omegaOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, beq_iff_eq] at h
  intro t ht hpow
  rcases h t ht with h1 | h2
  · exact absurd hpow h1
  · exact h2

theorem compOK_spec {L : Array (Array ℕ)} {U Z : Array ℕ} (h : compOK L U Z = true) :
    ∀ n < 243, (¬ ∃ t < 81, (aList U Z)[t]! = L[n]!) → powCode L[n]! 3 = idCode →
      mulCode L[n]! (powCode U 3) = mulCode (powCode U 3) L[n]! →
      mulCode L[n]! (powCode Z 3) = mulCode (powCode Z 3) L[n]! → False := by
  simp only [compOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Array.contains_iff_mem] at h
  intro n hn hna hp ha hb
  rcases h n hn with ((h1 | h2) | h3) | h4
  · obtain ⟨t, ht, ht'⟩ := Array.mem_iff_getElem.mp h1
    rw [size_aList] at ht
    exact hna ⟨t, ht, by rw [getElem!_pos _ t (by rw [size_aList]; exact ht), ht']⟩
  · exact h2 hp
  · exact h3 ha
  · exact h4 hb

theorem qOK_spec {L : Array (Array ℕ)} {zc : Array ℕ} {bi yi : ℕ} (h : qOK L zc bi yi = true) :
    bi < 243 ∧ yi < 243 ∧ L[bi]! ≠ idCode ∧ L[bi]! ≠ zc ∧ L[bi]! ≠ mulCode zc zc ∧
    powCode L[bi]! 3 = idCode ∧ mulCode zc L[bi]! = mulCode L[bi]! zc ∧
    semi (L[yi]!, 1) (semi (L[yi]!, 1) (L[yi]!, 1)) = semiOne ∧
    semi (L[yi]!, 1) (zc, 0) = semi (zc, 0) (L[yi]!, 1) ∧
    semi (L[yi]!, 1) (L[bi]!, 0) = semi (L[bi]!, 0) (L[yi]!, 1) := by
  simp only [qOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hy⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨hb, hy, h1, h2, h3, h4, h5, h6, semiComm_iff.mp h7, semiComm_iff.mp h8⟩

theorem gOK_spec {zc b1 b2 : Array ℕ} {gw : List (List ℕ)} (h : gOK zc b1 b2 gw = true) :
    gw.length = 4 ∧ ∀ j < 4,
      mulCode (wordCode gw[j]!) (wordCode (gw[j]!).reverse) = idCode ∧
      mulCode (wordCode (gw[j]!).reverse) (wordCode gw[j]!) = idCode ∧
      (mulCode (mulCode (wordCode gw[j]!) zc) (wordCode (gw[j]!).reverse) = zc ∨
        mulCode (mulCode (wordCode gw[j]!) zc) (wordCode (gw[j]!).reverse) = mulCode zc zc) ∧
      ∃ t < 9, mulCode (mulCode (wordCode gw[j]!) (if j < 2 then b1 else b2))
        (wordCode (gw[j]!).reverse) =
          mulCode (powCode zc (t / 3)) (powCode (if j < 2 then b1 else b2) (t % 3)) := by
  simp only [gOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Array.contains_iff_mem] at h
  obtain ⟨hl, hj⟩ := h
  refine ⟨hl, fun j hj' => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj j hj'
  refine ⟨h1, h2, h3, ?_⟩
  obtain ⟨t, ht, ht'⟩ := Array.mem_iff_getElem.mp h4
  rw [size_qList] at ht
  refine ⟨t, ht, ?_⟩
  rw [← getElem!_qList _ _ ht, getElem!_pos _ t (by rw [size_qList]; exact ht), ht']

end CFSG.AGLEmbedding.KFactProofs.G28
