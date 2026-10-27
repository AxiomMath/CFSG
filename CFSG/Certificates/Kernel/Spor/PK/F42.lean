module

public import CFSG.Certificates.Kernel.Spor.PK.F42Slp
public import CFSG.Certificates.Kernel.Spor.PK.F42Roots

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.F3.Native CFSG.Blueprint.Chevalley
open CFSG.LieType.Multipliers.F42 (Pair eqPM commutes matOf invOf commArr liftOK)

section Checks

variable {L : Array Pair} {LF LI RC : List ℕ} {RL : List (List ℕ)} {R : List (List ℤ)}

private theorem chkBoolRec_nat (b : Bool) (e t : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t b = if b = true then t else e := by
  cases b <;> rfl

private theorem chkBeq_false_iff {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

private theorem chkWfM_of_can52 {X : Array V} (hX : Can52 X) : wfM X = true := by
  have hw := RowsWF.of_canonM hX
  unfold wfM
  rw [Array.all_eq_true]
  intro i hi
  have := hw i
  rwa [getElem!_pos X i hi] at this

theorem liftRel_get (hL : F42LiftRel LF LI L) {k : ℕ} (hk : k < 48) :
    Can52 (matOf L k) ∧ Can52 (invOf L k) ∧ nthV LF k = pk52 (matOf L k) ∧
      nthV LI k = pk52 (invOf L k) := by
  refine ⟨hL.can_fst k hk, hL.can_snd k hk, ?_, ?_⟩
  · rw [nthV_eq]; exact hL.fst_pk k hk
  · rw [nthV_eq]; exact hL.snd_pk k hk

theorem liftK_sound (hL : F42LiftRel LF LI L) {k : ℕ} (hk : k < 48) (h : liftK LF LI k = true) :
    liftOK L k = true := by
  obtain ⟨hX, hY, hFX, hFY⟩ := liftRel_get hL hk
  unfold liftK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true] at h
  rw [hFX, hFY] at h
  obtain ⟨-, -, h1, h2, h3⟩ := h
  rw [mulS_pk52 hX hY, idS_eq, beq_pk52 (can52_mul hX hY) can52_idM] at h1
  rw [mulS_pk52 hY hX, idS_eq, beq_pk52 (can52_mul hY hX) can52_idM] at h2
  rw [mulS_pk52 hX hX, idS_eq, eqPMS_pk52 (can52_mul hX hX) can52_idM] at h3
  simp only [liftOK, Bool.and_eq_true, beq_iff_eq, and_assoc]
  exact ⟨(canonM_spec hX).1, chkWfM_of_can52 hX, (canonM_spec hY).1, chkWfM_of_can52 hY, h1, h2, h3⟩

theorem commArrK_pk52 (hL : F42LiftRel LF LI L) {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    Can52 (commArr L i j) ∧ commArrK LF LI i j = pk52 (commArr L i j) := by
  obtain ⟨hXi, hYi, hFi, hIi⟩ := liftRel_get hL hi
  obtain ⟨hXj, hYj, hFj, hIj⟩ := liftRel_get hL hj
  have c1 := can52_mul hXi hXj
  have c2 := can52_mul c1 hYi
  have c3 := can52_mul c2 hYj
  refine ⟨c3, ?_⟩
  unfold commArrK commArr
  rw [hFi, hFj, hIi, hIj, mulS_pk52 hXi hXj, mulS_pk52 c1 hYi, mulS_pk52 c2 hYj]

private theorem chkBound_add {a b : Fin Tag.F4.rank → ℤ} (ha : ∀ t, -8 ≤ a t ∧ a t ≤ 8)
    (hb : ∀ t, -8 ≤ b t ∧ b t ≤ 8) : ∀ t, -32 ≤ (a + b) t ∧ (a + b) t ≤ 31 := by
  intro t
  have h1 := ha t
  have h2 := hb t
  simp only [Pi.add_apply]
  omega

private theorem chkBound_sub {a b : Fin Tag.F4.rank → ℤ} (ha : ∀ t, -8 ≤ a t ∧ a t ≤ 8)
    (hb : ∀ t, -8 ≤ b t ∧ b t ≤ 8) : ∀ t, -32 ≤ (a - b) t ∧ (a - b) t ≤ 31 := by
  intro t
  have h1 := ha t
  have h2 := hb t
  simp only [Pi.sub_apply]
  omega

private theorem chkBound_add2 {a b : Fin Tag.F4.rank → ℤ} (ha : ∀ t, -8 ≤ a t ∧ a t ≤ 8)
    (hb : ∀ t, -8 ≤ b t ∧ b t ≤ 8) : ∀ t, -32 ≤ (a + 2 • b) t ∧ (a + 2 • b) t ≤ 31 := by
  intro t
  have h1 := ha t
  have h2 := hb t
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  omega

private theorem chkBound_two_add {a b : Fin Tag.F4.rank → ℤ} (ha : ∀ t, -8 ≤ a t ∧ a t ≤ 8)
    (hb : ∀ t, -8 ≤ b t ∧ b t ≤ 8) : ∀ t, -32 ≤ (2 • a + b) t ∧ (2 • a + b) t ≤ 31 := by
  intro t
  have h1 := ha t
  have h2 := hb t
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  omega

theorem factorK_pk52 (hL : F42LiftRel LF LI L) (hr : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) (c : Bool)
    {w : Fin Tag.F4.rank → ℤ} (hw : ∀ t, -32 ≤ w t ∧ w t ≤ 31) :
    Can52 (factorG R L c w) ∧ factorK LF RC c (vecCode w) = pk52 (factorG R L c w) := by
  have hidx := idxR_vecCode hr hR hw
  have hlt := rootIdxG_lt_iff (roots_length hr hR) w
  unfold factorK factorG
  simp only [letN_eq, andB_eq, chkBoolRec_nat, hidx, Bool.and_eq_true, Nat.blt_eq]
  by_cases hc : c = true ∧ isRootBG R w = true
  · have hlt' : rootIdxG R w < 48 := hlt.2 hc.2
    obtain ⟨hX, -, hF, -⟩ := liftRel_get hL hlt'
    rw [if_pos hc, if_pos ⟨hc.1, hlt'⟩]
    exact ⟨hX, hF⟩
  · have hc' : ¬ (c = true ∧ rootIdxG R w < 48) := fun h => hc ⟨h.1, hlt.1 h.2⟩
    rw [if_neg hc, if_neg hc', idS_eq]
    exact ⟨can52_idM, rfl⟩

private theorem chkFactorsK_pk52 (hL : F42LiftRel LF LI L) (hr : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    Can52 (factorG R L (!isRootBG R (rootAtG R j - rootAtG R i)) (rootAtG R i + rootAtG R j)) ∧
      Can52 (factorG R L true (rootAtG R i + 2 • rootAtG R j)) ∧
      Can52 (factorG R L true (2 • rootAtG R i + rootAtG R j)) ∧
      ∀ k : ℕ → ℕ → ℕ → Bool, factorsK LF RC i j k =
        k (pk52 (factorG R L (!isRootBG R (rootAtG R j - rootAtG R i))
            (rootAtG R i + rootAtG R j)))
          (pk52 (factorG R L true (rootAtG R i + 2 • rootAtG R j)))
          (pk52 (factorG R L true (2 • rootAtG R i + rootAtG R j))) := by
  have bi := rootAtG_bound hr hR hi
  have bj := rootAtG_bound hr hR hj
  obtain ⟨c11, e11⟩ :=
    factorK_pk52 hL hr hR (!isRootBG R (rootAtG R j - rootAtG R i)) (chkBound_add bi bj)
  obtain ⟨c12, e12⟩ := factorK_pk52 hL hr hR true (chkBound_add2 bi bj)
  obtain ⟨c21, e21⟩ := factorK_pk52 hL hr hR true (chkBound_two_add bi bj)
  refine ⟨c11, c12, c21, fun k => ?_⟩
  unfold factorsK
  simp only [letB_eq]
  rw [rootsK_diff hr hR hi hj, rootsK_sum hr hR hi hj, rootsK_sum12 hr hR hi hj,
    rootsK_sum21 hr hR hi hj, idxR_gt_47_iff hr hR (chkBound_sub bj bi), e11, e12, e21]

theorem pairK_sound (hL : F42LiftRel LF LI L) (hr : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ} (hi : i < 48) (hj : j < 48)
    (h : pairK LF LI RC i j = true) : pairOKG R L i j = true := by
  obtain ⟨c11, c12, c21, hf⟩ := chkFactorsK_pk52 hL hr hR hi hj
  obtain ⟨c0, e0⟩ := commArrK_pk52 hL hi hj
  unfold pairK at h
  rw [hf] at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [e0, mulI_pk52 c11 c12, mulI_pk52 (can52_mul c11 c12) c21,
    eqPMS_pk52 c0 (can52_mul (can52_mul c11 c12) c21)] at h1
  rw [commS_pk52 c11 c12] at h2
  rw [commS_pk52 c11 c21] at h3
  rw [commS_pk52 c12 c21] at h4
  unfold pairOKG prodArrG
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem pairsOKG_sound (hL : F42LiftRel LF LI L) (hr : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32))
    (hp : ∀ c < 48, pairsChunk LF LI RC c 1 = true) : pairsOKG R L = true := by
  unfold pairsOKG
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have h := hp i hi
  unfold pairsChunk at h
  rw [allN_lqt_iff] at h
  have h0 := h 0 (by omega)
  simp only [letB_eq, impB_eq] at h0
  have h0' : (!Nat.blt i 48 || allN 48 fun j =>
      orB (Nat.beq i j) (orB (oppK RC i j) (pairK LF LI RC i j))) = true := h0
  have hb : Nat.blt i 48 = true := by rw [Nat.blt_eq]; exact hi
  rw [hb, Bool.not_true, Bool.false_or, allN_lqt_iff] at h0'
  have h1 := h0' j hj
  simp only [orB_eq, Bool.or_eq_true, Nat.beq_eq] at h1
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  rcases h1 with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr ((oppK_iff hr hR hi hj).1 h1))
  · exact Or.inr (pairK_sound hL hr hR hi hj h1)

theorem wordK_sound {CP : List (ℕ × ℕ)} (hL : F42LiftRel LF LI L) (hr : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {k : ℕ} (hk : k < 48)
    (h : wordK LF LI RC k (CP.getD k (0, 0)).1 (CP.getD k (0, 0)).2 = true) :
    wordOKG R CP L k = true := by
  unfold wordOKG
  dsimp only
  generalize CP.getD k (0, 0) = pq at h ⊢
  obtain ⟨p, q⟩ := pq
  dsimp only at h ⊢
  unfold wordK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨hp48, hq48, hpq, hopp, hsum, h12, h21, hd, hcomm⟩ := h
  have hp' : p < 48 := by rwa [Nat.blt_eq] at hp48
  have hq' : q < 48 := by rwa [Nat.blt_eq] at hq48
  have bp := rootAtG_bound hr hR hp'
  have bq := rootAtG_bound hr hR hq'
  have hne : p ≠ q := by
    rw [notB_eq, Bool.not_eq_true', chkBeq_false_iff] at hpq
    exact hpq
  have hopp' : oppK RC p q = false := by
    rw [notB_eq, Bool.not_eq_true'] at hopp
    exact hopp
  have hopp'' : ¬ (rootAtG R p + rootAtG R q = 0) := fun e =>
    absurd ((oppK_iff hr hR hp' hq').2 e) (by rw [hopp']; decide)
  have hsum' := (rootsK_sum_eq_iff hr hR hp' hq' hk).1 hsum
  rw [rootsK_sum12 hr hR hp' hq', idxR_eq_48_iff hr hR (chkBound_add2 bp bq)] at h12
  rw [rootsK_sum21 hr hR hp' hq', idxR_eq_48_iff hr hR (chkBound_two_add bp bq)] at h21
  rw [rootsK_diff hr hR hp' hq', idxR_eq_48_iff hr hR (chkBound_sub bq bp)] at hd
  obtain ⟨c0, e0⟩ := commArrK_pk52 hL hp' hq'
  obtain ⟨hXk, -, hFk, -⟩ := liftRel_get hL hk
  rw [e0, hFk, beq_pk52 c0 hXk] at hcomm
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, and_assoc]
  exact ⟨hp', hq', hne, hopp'', hsum', h12, h21, hd, hcomm⟩

theorem negK_sound (hL : F42LiftRel LF LI L) (hr : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ}
    (h : negK LF LI RC i j = true) : negOKG R L i j = true := by
  unfold negK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hi, hj, hij, hopp, h⟩ := h
  have hi' : i < 48 := by rwa [Nat.blt_eq] at hi
  have hj' : j < 48 := by rwa [Nat.blt_eq] at hj
  have hne : i ≠ j := by
    rw [notB_eq, Bool.not_eq_true', chkBeq_false_iff] at hij
    exact hij
  have hopp' : oppK RC i j = false := by
    rw [notB_eq, Bool.not_eq_true'] at hopp
    exact hopp
  have hopp'' : ¬ (rootAtG R i + rootAtG R j = 0) := fun e =>
    absurd ((oppK_iff hr hR hi' hj').2 e) (by rw [hopp']; decide)
  obtain ⟨c11, c12, c21, hf⟩ := chkFactorsK_pk52 hL hr hR hi' hj'
  obtain ⟨c0, e0⟩ := commArrK_pk52 hL hi' hj'
  have c3 := can52_mul (can52_mul c11 c12) c21
  rw [hf] at h
  rw [e0, mulI_pk52 c11 c12, mulI_pk52 (can52_mul c11 c12) c21, negS_pk52 c3,
    beq_pk52 c0 (can52_negM c3)] at h
  unfold negOKG prodArrG
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, and_assoc]
  exact ⟨hi', hj', hne, hopp'', h⟩

end Checks

theorem f42_sound_wf {pA pB slp : String} {refs : List ℤ} {R : List (List ℤ)} {CP : List (ℕ × ℕ)}
    {cA cB cS Rc LR RC F I LF LI : List ℕ} {RL : List (List ℕ)} {nI nP : ℕ}
    (hA : pA = strOf cA) (hB : pB = strOf cB) (hS : slp = strOf cS)
    (hrefs : refs = LR.map refOfCode) (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32))
    (hfmt : fmtK cS = true) (hints : eqLN (intsK cS) Rc = true)
    (hst : startK cA cB F I = true)
    (hnI : nI = lenN Rc / 2) (hF : Nat.beq (lenN F) (nI + 2) = true)
    (hins : ∀ c < nP, insChunk F I Rc nI (16 * c) 16 = true) (hnP : nI ≤ 16 * nP)
    (hl : liftsK F I LR LF LI (nI + 2) = true) (hr : rootsK RL RC = true)
    (hlk : ∀ k < 48, liftK LF LI k = true)
    (hp : ∀ c < 48, pairsChunk LF LI RC c 1 = true)
    (hw : ∀ k < 48, wordK LF LI RC k (CP.getD k (0, 0)).1 (CP.getD k (0, 0)).2 = true)
    (hn : negK LF LI RC 0 35 = true)
    (hwI : ∀ k < nI + 2, wfS (nthV I k) = true) :
    (List.range 48).all (liftOK (liftsOf pA pB slp refs)) = true ∧
      pairsOKG R (liftsOf pA pB slp refs) = true ∧
      (List.range 48).all (wordOKG R CP (liftsOf pA pB slp refs)) = true ∧
      negOKG R (liftsOf pA pB slp refs) 0 35 = true := by
  have hwI' : ∀ k < nI + 2, wfS (I.getD k 0) = true := fun k hk => by
    rw [← nthV_eq]
    exact hwI k hk
  have hN := slpVals_nodeRel hA hB hS hfmt hints hst hnI (ins_all hins hnP) hwI'
  subst hrefs
  have hL := liftRel_of_liftsK hN hl
  refine ⟨?_, pairsOKG_sound hL hr hR hp, ?_, negK_sound hL hr hR hn⟩
  · rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    exact liftK_sound hL hk (hlk k hk)
  · rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    exact wordK_sound hL hr hR hk (hw k hk)

end CFSG.KS.PK

end
