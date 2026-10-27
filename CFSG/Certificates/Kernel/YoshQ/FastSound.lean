module

public import Certificates.Data.Kernel.YoshQ.Fast

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.M12Std.Yosh

private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem testBit_hmaskF (P : Nat) (L : List Nat) (M j : Nat) :
    (hmaskF P L M).testBit j = (M.testBit j || L.any fun x => hN P x == j) := by
  induction L generalizing M with
  | nil => simp [hmaskF]
  | cons x L ih =>
    rw [show hmaskF P (x :: L) M = strictN (M ||| (1 <<< hN P x)) (hmaskF P L) from rfl,
      strictN_eq', ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.any_cons]
    by_cases e : hN P x = j
    · subst e
      simp
    · have e' : (hN P x == j) = false := by simpa using e
      simp [e, e']

theorem memH_of_memN {P : Nat} {L : List Nat} {x : Nat} (h : memN 16 5 L x = true) :
    memH P L x = true := by
  unfold memN at h
  obtain ⟨s, hs, e⟩ := List.any_eq_true.1 h
  unfold eqN at e
  rw [Nat.beq_eq] at e
  unfold memH hmask
  rw [testBit_hmaskF, Bool.or_eq_true]
  refine Or.inr (List.any_eq_true.2 ⟨s, hs, ?_⟩)
  unfold hN
  rw [e]
  exact beq_self_eq_true _

theorem conjToN_of_cjW {cnt EP : Nat} {NL : List Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL)
    {t₁ t₂ j : Nat} (h : cjW cnt EP t₁ t₂ j = true) : conjToN NL t₁ t₂ = true := by
  unfold cjW at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  unfold conjToN
  rw [List.any_eq_true]
  exact ⟨fldN EP (16 * 5) j, hNL ▸ List.mem_map.2 ⟨j, List.mem_range.2 h.1, rfl⟩, h.2⟩

theorem memN_of_posW {cnt EP : Nat} {GS NL : List Nat} {reps : List (List (Fin 9 × Bool))}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL) {T c : Nat}
    (h : posW cnt EP GS reps T c = true) :
    memN 16 5 (reps.flatMap fun w => classN NL (nTN GS w)) T = true := by
  unfold posW at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hr, hw⟩ := h
  unfold cjW at hw
  rw [Bool.and_eq_true, Nat.blt_eq] at hw
  unfold memN
  rw [List.any_eq_true]
  refine ⟨cjN 16 5 (fldN EP (16 * 5) (c % 4096)) (nTN GS (reps.getD (c / 4096) [])), ?_, hw.2⟩
  rw [List.mem_flatMap]
  refine ⟨reps.getD (c / 4096) [], ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  · unfold classN
    exact List.mem_map.2 ⟨_, hNL ▸ List.mem_map.2 ⟨_, List.mem_range.2 hw.1, rfl⟩, rfl⟩

theorem memN_good_of_posW {cnt EP : Nat} {GS NL : List Nat} {α k : Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL) {T c : Nat}
    (h : posW cnt EP GS (goodRepsN GS NL α k) T c = true) :
    memN 16 5 (goodTabsN GS NL α k) T = true :=
  memN_of_posW hNL h

theorem memN_bad_of_posW {cnt EP : Nat} {GS NL : List Nat} {α k : Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL) {T c : Nat}
    (h : posW cnt EP GS (badRepsN GS NL α k) T c = true) :
    memN 16 5 (badTabsN GS NL α k) T = true :=
  memN_of_posW hNL h

theorem zip_all_of {LE W : List Nat} {F : Nat × Nat → Bool} (hl : LE.length ≤ W.length)
    (h : (LE.zip W).all F = true) {T : Nat} (hT : T ∈ LE) : ∃ c, F (T, c) = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
  have hz : i < (LE.zip W).length := by rw [List.length_zip]; omega
  refine ⟨W[i]'(by omega), ?_⟩
  have := List.all_eq_true.1 h _ (List.getElem_mem hz)
  rwa [List.getElem_zip] at this

theorem memN_eq_memH_of_goodV {cnt EP P : Nat} {GS NL : List Nat} {α k : Nat} {L V : List Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL)
    (hV : goodV cnt EP P GS NL α k L V = true) {T : Nat} (hT : T ∈ L) :
    memN 16 5 (goodTabsN GS NL α k) T = memH P (goodTabsN GS NL α k) T := by
  unfold goodV at hV
  rw [Bool.and_eq_true, Nat.ble_eq] at hV
  obtain ⟨c, hc⟩ := zip_all_of hV.1 hV.2 hT
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hc
  cases hm : memH P (goodTabsN GS NL α k) T
  · cases hn : memN 16 5 (goodTabsN GS NL α k) T
    · rfl
    · rw [memH_of_memN hn] at hm
      exact absurd hm (by decide)
  · rcases hc with hc | hc
    · rw [hm] at hc
      exact absurd hc (by decide)
    · exact memN_good_of_posW hNL hc

theorem filter_memN_good_of_V {cnt EP P : Nat} {GS NL : List Nat} {α k : Nat} {L V : List Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL)
    (hV : goodV cnt EP P GS NL α k L V = true) :
    L.filter (memN 16 5 (goodTabsN GS NL α k)) = L.filter (memH P (goodTabsN GS NL α k)) :=
  List.filter_congr fun _ hT => memN_eq_memH_of_goodV hNL hV hT

theorem l6N_of_V {cnt EP P : Nat} {NL good LE W : List Nat} {e j : Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL)
    (hW : l6V cnt EP P NL good e LE j W = true) : l6N NL good e LE = true := by
  unfold l6V at hW
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hW
  obtain ⟨⟨⟨hj, hcnt⟩, hlen⟩, hall⟩ := hW
  have hy : LE.getD j 0 = LE[j] := List.getD_eq_getElem _ _ hj
  unfold l6N
  rw [List.any_eq_true]
  refine ⟨LE[j], List.getElem_mem hj, ?_⟩
  rw [Bool.and_eq_true, ← hy, List.all_eq_true]
  refine ⟨by rw [Nat.beq_eq] at hcnt; rw [hcnt]; rfl, fun T hT => ?_⟩
  obtain ⟨c, hcT⟩ := zip_all_of hlen hall hT
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcT
  cases hm : memN 16 5 good T
  · rfl
  · rcases hcT with hc | hw
    · rw [memH_of_memN hm] at hc
      exact absurd hc (by decide)
    · cases hb : Nat.beq (c % 2) 0
      · rw [hb, Bool.cond_false] at hw
        rw [conjToN_of_cjW hNL hw]
        simp
      · rw [hb, Bool.cond_true] at hw
        rw [conjToN_of_cjW hNL hw]
        simp

theorem goodV_of_l7fV {cnt EP P : Nat} {GS NL LE W V : List Nat} {α k e u cu cue : Nat}
    (hW : l7fV cnt EP P GS NL α k e u LE W V cu cue = true) :
    goodV cnt EP P GS NL α k LE V = true := by
  unfold l7fV at hW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hW
  unfold goodV
  rw [Bool.and_eq_true, Nat.ble_eq]
  exact ⟨hW.1.1.1.1.1.1.1.1.2, hW.1.1.1.1.1.1.1.2⟩

theorem l7FusionN_of_V {cnt EP P : Nat} {GS NL LE W V : List Nat} {α k e u cu cue : Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL)
    (hW : l7fV cnt EP P GS NL α k e u LE W V cu cue = true) :
    l7FusionN NL (goodTabsN GS NL α k) e u LE = true := by
  unfold l7fV at hW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hW
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlW, hlV⟩, hV⟩, h56⟩, hu⟩, hue⟩, hLu⟩, hLue⟩, hc⟩, hall⟩ :=
    hW
  have hg : goodV cnt EP P GS NL α k LE V = true := by
    unfold goodV
    rw [Bool.and_eq_true, Nat.ble_eq]
    exact ⟨hlV, hV⟩
  unfold l7FusionN
  rw [filter_memN_good_of_V hNL hg]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨h56, memN_good_of_posW hNL hu⟩, memN_good_of_posW hNL hue⟩, hLu⟩, hLue⟩,
    hc⟩, List.all_eq_true.2 fun T hT => ?_⟩
  obtain ⟨c, hcT⟩ := zip_all_of hlW hall hT
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcT
  cases hm : memN 16 5 (goodTabsN GS NL α k) T
  · rfl
  · rcases hcT with hc | hw
    · rw [memH_of_memN hm] at hc
      exact absurd hc (by decide)
    · cases h0 : Nat.beq (c % 3) 0
      · rw [h0, Bool.cond_false] at hw
        cases h1 : Nat.beq (c % 3) 1
        · rw [h1, Bool.cond_false] at hw
          rw [conjToN_of_cjW hNL hw]
          simp
        · rw [h1, Bool.cond_true] at hw
          rw [conjToN_of_cjW hNL hw]
          simp
      · rw [h0, Bool.cond_true] at hw
        rw [conjToN_of_cjW hNL hw]
        simp

theorem l7AN_of_V {cnt EP P : Nat} {GS NL GA LA LE LS V : List Nat} {α k c : Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL)
    (hW : l7AV cnt EP P GS NL α k c GA LA LE LS V = true) :
    l7AN (badTabsN GS NL α k) c GA LA LE LS = true := by
  unfold l7AV at hW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hW
  obtain ⟨⟨⟨⟨⟨⟨⟨hl, hV⟩, h1⟩, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩ := hW
  unfold l7AN
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, List.all_eq_true.2 fun T hT => ?_⟩,
    List.all_eq_true.2 fun y hy => ?_⟩, h6⟩, h7⟩
  · obtain ⟨c, hcT⟩ := zip_all_of hl hV hT
    exact memN_bad_of_posW hNL hcT
  · have := List.all_eq_true.1 h5 y hy
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this ⊢
    rcases this with h | h
    · left
      cases hm : memN 16 5 (badTabsN GS NL α k) y
      · rfl
      · rw [memH_of_memN hm] at h
        exact absurd h (by decide)
    · exact Or.inr h

theorem fusionCoverN_of_V {cnt EP P : Nat} {GS NL V : List Nat} {α k : Nat}
    (hNL : (List.range cnt).map (fldN EP (16 * 5)) = NL)
    (hW : fusionCoverV cnt EP P GS NL α k V = true) : fusionCoverN GS NL α k = true := by
  unfold fusionCoverV at hW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hW
  obtain ⟨⟨hl, hall⟩, hcount⟩ := hW
  have hg : goodV cnt EP P GS NL α k NL V = true := by
    unfold goodV
    rw [Bool.and_eq_true, Nat.ble_eq]
    refine ⟨hl, ?_⟩
    rw [List.all_eq_true] at hall ⊢
    intro p hp
    exact (Bool.and_eq_true _ _ ▸ hall p hp).1
  unfold fusionCoverN
  rw [filter_memN_good_of_V hNL hg]
  simp only [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun y hy => ?_, hcount⟩
  obtain ⟨c, hcT⟩ := zip_all_of hl hall hy
  rw [Bool.and_eq_true] at hcT
  have hb := hcT.2
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hb ⊢
  rw [memN_eq_memH_of_goodV hNL hg hy]
  rcases hb with (hb | hb) | hb
  · exact Or.inl (Or.inl hb)
  · exact Or.inl (Or.inr hb)
  · exact Or.inr (memN_bad_of_posW hNL hb)

end CFSG.KC.YoshQ

end
