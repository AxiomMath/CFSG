module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28OmCheck

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem subsetOK_spec {N : ℕ} {sz : ℕ → ℕ} (h : subsetOK N sz = true) :
    ∀ a b c d : Bool, N % (1 + (if a then sz 1 else 0) + (if b then sz 2 else 0) +
      (if c then sz 3 else 0) + (if d then sz 4 else 0)) = 0 →
      (a = false ∧ b = false ∧ c = false ∧ d = false) ∨
        (a = true ∧ b = true ∧ c = true ∧ d = true) := by
  simp only [subsetOK, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  intro a b c d hdiv
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem treeSize_eq (pts : Array (Array ℕ × ℕ)) (k : ℕ) :
    treeSize pts k = ((Finset.range pts.size).filter fun n => (pts[n]!).2 = k).card := by
  unfold treeSize
  rw [← Multiset.coe_card]
  simp [Finset.card, Finset.filter, Finset.range, Multiset.range, beq_eq_decide]

theorem treeSizes_getElem (pts : Array (Array ℕ × ℕ)) {k : ℕ} (hk : k < 5) :
    (treeSizes pts)[k]! = treeSize pts k := by
  interval_cases k <;> rfl

theorem epsOK_spec {zc : Array ℕ} {gw : List (List ℕ)} (h : epsOK zc gw = true) :
    ∀ j < 4, mulCode (mulCode (wordCode gw[j]!) zc) (wordCode (gw[j]!).reverse) =
      (if j % 2 = 1 then mulCode zc zc else zc) := by
  simp only [epsOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem revInvOK_spec {w : List ℕ} (h : revInvOK w = true) :
    mulCode (wordCode w) (wordCode w.reverse) = idCode ∧
      mulCode (wordCode w.reverse) (wordCode w) = idCode := by
  simpa [revInvOK] using h

theorem quadOK_spec {zc : Array ℕ} (h : quadOK zc = true) :
    ∀ t < 36, (mulCode zc zc)[t]! ^^^ zc[t]! ^^^ idCode[t]! = 0 := by
  simp only [quadOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem OmData.check_spec {D : OmData} (h : D.check = true) :
    D.forest.ok = true ∧ (D.hTree D.sc D.sic D.forest.build).ok = true ∧
    D.forest.build.size = D.N ∧ D.N = 130816 ∧ D.hN = 1024 ∧ D.gw.length = 4 ∧
    D.seedW.length = 4 ∧ D.schW.length = 8 ∧ D.cIdx < D.N ∧
    (∀ w ∈ D.gw, revInvOK w = true) ∧ (∀ w ∈ D.seedW, revInvOK w = true) ∧ quadOK D.zc = true ∧
    epsOK D.zc D.gw = true ∧
    (∀ w ∈ D.schW, ∀ s ∈ w, s < 8) ∧
    (∀ i < D.N, ∀ j < D.N, (D.forest.build[i]!).1 = (D.forest.build[j]!).1 → i = j) ∧
    (∀ i < D.hN, ∀ j < D.hN, ((D.hTree D.sc D.sic D.forest.build).build[i]!).1 =
      ((D.hTree D.sc D.sic D.forest.build).build[j]!).1 → i = j) ∧
    subsetOK D.N (fun k => (treeSizes D.forest.build)[k]!) = true ∧
    (treeSizes D.forest.build)[0]! = 1 ∧ 32319 ≤ (treeSizes D.forest.build)[1]! ∧
    ∀ w ∈ D.schW, canonCode (conjCode (schCode D.sc w) (schInv D.sic w)
      (D.forest.build[1]!).1) = (D.forest.build[1]!).1 := by
  simp only [OmData.check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h12e, h12', h13, h14, h15, h16, h17,
    h18⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun w hw => h10 w hw, fun w hw => h11 w hw, h12,
    h12e, fun w hw s hs => ?_, ?_, ?_, h15, h16, h17, fun w hw => ?_⟩
  · simpa using h12' w hw s hs
  · intro i hi j hj hij
    have hl : D.forest.build.size = D.N := h3
    have := distinctOK_spec h13 i (by simpa [hl] using hi) j (by simpa [hl] using hj)
    exact this (by simpa [getElem!_pos, hi, hj, hl] using hij)
  · intro i hi j hj hij
    have hl : ((D.hTree D.sc D.sic D.forest.build).build).size = D.hN :=
      TreeData.pre_size _ _
    have := distinctOK_spec h14 i (by simpa [hl] using hi) j (by simpa [hl] using hj)
    exact this (by simpa [getElem!_pos, hi, hj, hl] using hij)
  · simpa using h18 w hw

end CFSG.AGLEmbedding.KFactProofs.G28
