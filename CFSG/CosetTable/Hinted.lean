module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.CosetTable.HintedEnum

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G] {gen : ℕ → G} {H : Subgroup G} {P : Params}

theorem defStep_inv (hP : Good gen H P) (fuel c x : ℕ) {st : St} (h : SInv P.L gen H st) :
    SInv P.L gen H (defStep P fuel c x st) := by
  unfold defStep
  split
  · exact processDed_inv hP fuel _ (define_inv hP h _ _)
  · exact h

theorem defPath_inv (hP : Good gen H P) (fuel : ℕ) :
    ∀ (w : List ℕ) (c : ℕ) (st : St), SInv P.L gen H st →
      SInv P.L gen H (defPath P fuel c w st).1 := by
  intro w
  induction w with
  | nil => intro c st h; simpa [defPath] using h
  | cons x w ih =>
    intro c st h
    simp only [defPath]
    have h1 := defStep_inv hP fuel (find st.fwd st.next c) x h
    generalize defStep P fuel (find st.fwd st.next c) x st = s1 at h1 ⊢
    split
    · exact h1
    · exact ih _ _ h1

theorem hltHint_inv (hP : Good gen H P) (fuel : ℕ) (p : List ℕ × List ℕ) {st : St}
    (h : SInv P.L gen H st) : SInv P.L gen H (hltHint P fuel p st) := by
  unfold hltHint
  split
  · rename_i hp
    obtain ⟨h1, h2, h3⟩ := hP.rels p hp
    apply processDed_inv hP
    rw [h1]
    exact hltWord_inv hP 1 p.1 h2 h3 _ _ h
  · exact h

theorem fillRowLim_inv (hP : Good gen H P) (fuel c lim : ℕ) :
    ∀ (n : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (fillRowLim P fuel c lim n st) := by
  intro n
  induction n with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    simp only [fillRowLim]
    split
    · exact h
    · split
      · exact ih _ (processDed_inv hP _ _ (define_inv hP h _ _))
      · exact ih _ h

theorem felschLim_inv (hP : Good gen H P) (fuel lim : ℕ) :
    ∀ (n c : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (felschLim P fuel lim n c st) := by
  intro n
  induction n with
  | zero => intro c st h; exact h
  | succ n ih =>
    intro c st h
    simp only [felschLim]
    split
    · exact ih _ _ (fillRowLim_inv hP fuel c lim lim st h)
    · exact h

theorem good_restrict (hP : Good gen H P) (idx : List ℕ) : Good gen H (P.restrict idx) := by
  unfold Params.restrict
  split
  · exact hP
  · rename_i hidx
    set sel : List (List ℕ) := idx.map fun i => (P.rels.getD i ([], [])).1 with hsel
    have hrel : ∀ r ∈ sel, (∀ y ∈ r, y < P.L) ∧ evalWord gen r = 1 := by
      intro r hr
      simp only [hsel, List.mem_map] at hr
      obtain ⟨i, -, rfl⟩ := hr
      by_cases hi : i < P.rels.length
      · rw [List.getD_eq_getElem _ _ hi]
        obtain ⟨-, h2, h3⟩ := hP.rels _ (List.getElem_mem hi)
        exact ⟨h2, h3⟩
      · rw [List.getD_eq_default _ _ (by omega)]
        simp [evalWord]
    refine ⟨hP.inv_lt, hP.gen_inv, ?_, hP.subs, hP.rels⟩
    intro x p hp
    obtain ⟨h1, r, hr, hpr⟩ := mem_scans (L := P.L) (inv := P.inv) (rels := sel) (subs := []) hp
    have hr' : (∀ y ∈ r, y < P.L) ∧ evalWord gen r = 1 := by
      rcases List.mem_append.mp hr with hr | hr
      · exact hrel r hr
      · simp only [List.mem_map] at hr
        obtain ⟨r0, hr0, rfl⟩ := hr
        obtain ⟨hl, he⟩ := hrel r0 hr0
        refine ⟨?_, ?_⟩
        · intro y hy
          simp only [invWord, List.mem_map, List.mem_reverse] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          exact hP.inv_lt z (hl z hz)
        · rw [evalWord_invWord (fun y hy => hP.gen_inv y (hl y hy)), he, inv_one]
    exact ⟨h1, letters_rotation hpr hr'.1, evalWord_rotation hpr hr'.2⟩

theorem runBlock_inv (hP : Good gen H P) (cap fuel : ℕ) (b : Block) {st : St}
    (h : SInv P.L gen H st) : SInv P.L gen H (runBlock P cap fuel b st) := by
  have hQ := good_restrict hP b.scan
  have hL : (P.restrict b.scan).L = P.L := by
    unfold Params.restrict; split <;> rfl
  rw [← hL] at h ⊢
  unfold runBlock
  dsimp only
  refine felschLim_inv hQ _ _ _ _ _ ?_
  have hrels : ∀ (l : List (List ℕ)) (s : St), SInv (P.restrict b.scan).L gen H s →
      SInv (P.restrict b.scan).L gen H (l.foldl (fun s w =>
        hltHint (P.restrict b.scan) fuel (w, invWord (P.restrict b.scan).inv w) s) s) := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons w l ih => intro s hs; exact ih _ (hltHint_inv hQ _ _ hs)
  exact hrels _ _ (defPath_inv hQ fuel _ _ _ h)

theorem pushColumn_inv (P : Params) (x : ℕ) :
    ∀ (n : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (pushColumn P x n st) := by
  intro n
  induction n with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    simp only [pushColumn]
    split
    · exact ih _ h
    · exact ih _ h

theorem restrict_L (P : Params) (idx : List ℕ) : (P.restrict idx).L = P.L := by
  unfold Params.restrict; split <;> rfl

theorem enumerateHinted_inv (hP : Good gen H P) (cap : ℕ) (T : Hints) :
    SInv P.L gen H (enumerateHinted P cap T) := by
  unfold enumerateHinted
  dsimp only
  set fuel := 64 * (cap + 1) * (P.L + 1) with hfuel
  have hblocks : ∀ (l : List Block) (s : St), SInv P.L gen H s →
      SInv P.L gen H (l.foldl (fun s b => runBlock P cap fuel b s) s) := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons b l ih => intro s hs; exact ih _ (runBlock_inv hP _ _ _ hs)
  set st1 := T.blocks.foldl (fun s b => runBlock P cap fuel b s)
    (fillSubs P fuel P.subs (St.init P.L cap)) with hst1
  have h1 : SInv P.L gen H st1 := hblocks _ _ (fillSubs_inv hP _ _ hP.subs _ (init_inv cap))
  set st2 := felschLim (P.restrict T.lateScan) fuel T.late (cap + 1) 1 st1 with hst2
  have h2 : SInv P.L gen H st2 := by
    have := felschLim_inv (good_restrict hP T.lateScan) fuel T.late (cap + 1) 1 st1
      (by rw [restrict_L]; exact h1)
    rwa [restrict_L] at this
  have h3 : SInv P.L gen H (pushColumn (P.restrict T.kScan) T.kCol st2.next st2) := by
    have := pushColumn_inv (gen := gen) (H := H) (P.restrict T.kScan) T.kCol st2.next st2
      (by rw [restrict_L]; exact h2)
    rwa [restrict_L] at this
  have h4 : SInv P.L gen H (processDed (P.restrict T.kScan) fuel
      (pushColumn (P.restrict T.kScan) T.kCol st2.next st2)) := by
    have := processDed_inv (good_restrict hP T.kScan) fuel
      (pushColumn (P.restrict T.kScan) T.kCol st2.next st2) (by rw [restrict_L]; exact h3)
    rwa [restrict_L] at this
  exact felsch_inv hP _ _ _ _ h4

theorem index_le_of_checkHinted (hP : Good gen H P)
    (hgen : Subgroup.closure (gen '' Set.Iio P.L) = ⊤) {T : Hints} {cap n : ℕ}
    (h : checkHinted P T cap n = true) : H.FiniteIndex ∧ H.index ≤ n := by
  unfold checkHinted at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨-, hc⟩, hn⟩ := h
  rw [← hn]
  exact index_le_of_complete hP hgen (enumerateHinted_inv hP cap T) hc

end CFSG.CosetTable
