module

public import CFSG.Certificates.CosetTableOrders

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

private abbrev cosetIdxGe_subWords (S : List ℕ) : List (List (Fin m × Bool)) :=
  (subsetOf m S).map fun x => [(x, true)]

private abbrev cosetIdxGe_params (ws : List (List (Fin m × Bool))) (S : List ℕ) (k : ℕ) : Params :=
  colParamsShort ws (cosetIdxGe_subWords (m := m) S) k

private abbrev cosetIdxGe_state (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap : ℕ) : St :=
  enumerateHLT (cosetIdxGe_params (m := m) ws S k) cap

private theorem cosetIdxGe_mem_block_fst {ws : List (List (Fin m × Bool))} {i : Fin m}
    {x : Fin m × Bool}
    (h : x ∈ (if isInvol ws i then [(i, true)] else [(i, true), (i, false)])) : x.1 = i := by
  by_cases hi : isInvol ws i
  · rw [if_pos hi] at h
    simp only [List.mem_singleton] at h
    exact congrArg Prod.fst h
  · rw [if_neg hi] at h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · exact congrArg Prod.fst h
    · simp at h
      exact congrArg Prod.fst h

private theorem cosetIdxGe_isInvol_false_of_mem {ws : List (List (Fin m × Bool))} {i : Fin m}
    (h : (i, false) ∈ cols ws) : isInvol ws i = false := by
  by_contra hne
  have hi : isInvol ws i = true := by
    cases hb : isInvol ws i
    · exact absurd hb hne
    · rfl
  simp only [cols, List.mem_flatMap, List.mem_finRange, true_and] at h
  obtain ⟨j, hj⟩ := h
  have hji : j = i := (cosetIdxGe_mem_block_fst (ws := ws) hj).symm
  subst hji
  rw [hi] at hj
  simp at hj

private theorem cosetIdxGe_colRep_cols (ws : List (List (Fin m × Bool))) {x : Fin m × Bool}
    (hx : x ∈ cols ws) : colRep ws x = x := by
  obtain ⟨i, b⟩ := x
  cases b with
  | false =>
    have hi : isInvol ws i = false := cosetIdxGe_isInvol_false_of_mem (ws := ws) hx
    show (if isInvol ws i then (i, true) else (i, false)) = (i, false)
    rw [hi]; rfl
  | true =>
    show (if isInvol ws i then (i, true) else (i, true)) = (i, true)
    by_cases h : isInvol ws i <;> simp [h]

private theorem cosetIdxGe_cols_nodup (ws : List (List (Fin m × Bool))) : (cols ws).Nodup := by
  unfold cols
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    by_cases h : isInvol ws i <;> simp [h]
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    change List.Disjoint
      ((fun i => if isInvol ws i then [(i, true)] else [(i, true), (i, false)]) (List.finRange m)[i])
      ((fun i => if isInvol ws i then [(i, true)] else [(i, true), (i, false)]) (List.finRange m)[j])
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    have ha1 : a.1 = (List.finRange m)[i] := cosetIdxGe_mem_block_fst (ws := ws) ha
    have hb1 : b.1 = (List.finRange m)[j] := cosetIdxGe_mem_block_fst (ws := ws) hb
    have hfst : ((List.finRange m)[i]).1 ≠ ((List.finRange m)[j]).1 := by
      simp only [List.getElem_finRange, Fin.val_cast]
      omega
    exact hfst (by rw [← ha1, ← hb1, hab])

private theorem cosetIdxGe_colCode_cols {ws : List (List (Fin m × Bool))} {y : ℕ}
    (hy : y < (cols ws).length) : colCode ws ((cols ws)[y]) = y := by
  have hnd := cosetIdxGe_cols_nodup ws
  have hrep : colRep ws ((cols ws)[y]) = (cols ws)[y] :=
    cosetIdxGe_colRep_cols ws (List.getElem_mem hy)
  unfold colCode
  rw [hrep]
  have hidx : (cols ws).idxOf ((cols ws)[y]) < (cols ws).length :=
    List.idxOf_lt_length_of_mem (List.getElem_mem hy)
  have h1 : (cols ws)[(cols ws).idxOf ((cols ws)[y])] = (cols ws)[y] :=
    List.getElem_idxOf (xs := cols ws) (x := (cols ws)[y]) hidx
  exact hnd.getElem_inj.mp h1

def basefixCheck (ws : List (List (Fin m × Bool))) (S : List ℕ) (k : ℕ) (st : St) : Bool :=
  (subsetOf m S).all fun x =>
    let y := colCode ws (x, true)
    let L := (cols ws).length
    st.tab.getD (1 * L + y) 0 == 1 &&
      st.tab.getD (1 * L + (colInv ws).getD y 0) 0 == 1

private def cosetIdxGe_reachProp (L : ℕ) (st : St) (c : ℕ) : Prop :=
  ∃ w : List ℕ, (∀ y ∈ w, y < L) ∧
    w.foldl (fun c x => st.tab.getD (c * L + x) 0) 1 = c

private def cosetIdxGe_reachBFS (L : ℕ) (st : St) : ℕ → List ℕ → Array Bool → Array Bool
  | 0, _, vis => vis
  | fuel + 1, [], vis => vis
  | fuel + 1, c :: q, vis =>
    if vis.getD c false then cosetIdxGe_reachBFS L st fuel q vis
    else
      let vis := vis.set! c true
      let row := (List.range L).map fun x => st.tab.getD (c * L + x) 0
      let q := row.filter (fun d => 0 < d && d < st.next) ++ q
      cosetIdxGe_reachBFS L st fuel q vis

def cosetReachCheck (ws : List (List (Fin m × Bool))) (S : List ℕ) (k : ℕ) (st : St) : Bool :=
  let L := (cols ws).length
  let vis := cosetIdxGe_reachBFS L st (st.next * L + 2) [1] (Array.replicate (st.next + 1) false)
  (List.range st.next).all fun c => !(st.live c) || vis.getD c false

def orderCheckLB (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ)
    (words : List (List (Fin m × Bool) × ℕ)) (fuel : ℕ) : Bool :=
  let P := colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k
  let st := enumerateHLT P cap
  orderCheck ws S k cap n words fuel && basefixCheck ws S k st && cosetReachCheck ws S k st

theorem orderCheck_of_orderCheckLB {ws : List (List (Fin m × Bool))} {S : List ℕ} {k cap n : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheckLB ws S k cap n words fuel = true) : orderCheck ws S k cap n words fuel = true := by
  unfold orderCheckLB at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

private theorem cosetIdxGe_basefixCheck_sound {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {k : ℕ} {st : St} (h : basefixCheck ws S k st = true) {x : Fin m}
    (hx : x ∈ subsetOf m S) :
    st.tab.getD (1 * (cols ws).length + colCode ws (x, true)) 0 = 1 := by
  unfold basefixCheck at h
  have h1 := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h1.1

private theorem cosetIdxGe_reachBFS_sound (L : ℕ) (st : St) :
    ∀ (fuel : ℕ) (q : List ℕ) (vis : Array Bool),
      (∀ c, vis.getD c false = true → cosetIdxGe_reachProp L st c) →
      (∀ c ∈ q, cosetIdxGe_reachProp L st c) →
      ∀ c, (cosetIdxGe_reachBFS L st fuel q vis).getD c false = true →
        cosetIdxGe_reachProp L st c := by
  intro fuel
  induction fuel with
  | zero =>
    intro q vis hv _ c hc
    rw [cosetIdxGe_reachBFS] at hc
    exact hv c hc
  | succ fuel ih =>
    intro q vis hv hq c hc
    cases q with
    | nil =>
      rw [cosetIdxGe_reachBFS] at hc
      exact hv c hc
    | cons hd q' =>
      have hhd : cosetIdxGe_reachProp L st hd := hq hd List.mem_cons_self
      have hq' : ∀ c ∈ q', cosetIdxGe_reachProp L st c := fun c hc => hq c (List.mem_cons_of_mem _ hc)
      rw [cosetIdxGe_reachBFS] at hc
      by_cases hvis : vis.getD hd false = true
      · rw [if_pos hvis] at hc
        exact ih q' vis hv hq' c hc
      · rw [if_neg hvis] at hc
        refine ih _ _ ?_ ?_ c hc
        · intro c' hc'
          by_cases hcc : hd = c'
          · subst hcc
            exact hhd
          · apply hv c'
            rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds_ne hcc] at hc'
            rwa [Array.getD_eq_getD_getElem?]
        · intro d hd'
          rw [List.mem_append] at hd'
          rcases hd' with hd' | hd'
          · rw [List.mem_filter] at hd'
            obtain ⟨hd1, -⟩ := hd'
            rw [List.mem_map] at hd1
            obtain ⟨x, hx, rfl⟩ := hd1
            obtain ⟨w, hw, hwc⟩ := hhd
            refine ⟨w ++ [x], ?_, ?_⟩
            · intro y hy
              rw [List.mem_append] at hy
              rcases hy with hy | hy
              · exact hw y hy
              · rw [List.mem_singleton] at hy
                subst hy
                exact List.mem_range.mp hx
            · rw [List.foldl_append]
              simp only [List.foldl_cons, List.foldl_nil, hwc]
          · exact hq' d hd'
private theorem cosetIdxGe_reachCheck_sound {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {k : ℕ} {st : St} (h : cosetReachCheck ws S k st = true) :
    ∀ c, st.live c = true → cosetIdxGe_reachProp (cols ws).length st c := by
  unfold cosetReachCheck at h
  have hall := List.all_eq_true.mp h
  intro c hc
  have hcrange : c ∈ List.range st.next := List.mem_range.mpr (St.live_lt hc).2
  have hcc := hall c hcrange
  rw [Bool.or_eq_true] at hcc
  rcases hcc with hcc | hcc
  · rw [hc] at hcc; simp at hcc
  · refine cosetIdxGe_reachBFS_sound (cols ws).length st _ [1]
      (Array.replicate (st.next + 1) false) ?_ ?_ c hcc
    · intro c' hc'
      rw [getD_replicate] at hc'
      simp at hc'
    · intro c' hc'
      simp only [List.mem_singleton] at hc'
      subst hc'
      exact ⟨[], by simp, rfl⟩

private theorem cosetIdxGe_card_live (st : St) :
    Nat.card (LiveNames st) = st.liveCount := by
  rw [St.liveCount, countBelow_eq]
  let s := (Finset.range st.next).filter fun c => st.live c = true
  have h1 : Nat.card (LiveNames st) = Nat.card {c // c ∈ s} := by
    refine Nat.card_congr ?_
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro c
      exact ⟨c.1, by
        simp only [s, Finset.mem_filter, Finset.mem_range]
        exact ⟨(St.live_lt c.2).2, c.2⟩⟩
    · intro c
      exact ⟨c.1, (Finset.mem_filter.mp c.2).2⟩
    · intro c; rfl
    · intro c; rfl
  have h2 : Nat.card {c // c ∈ s} = s.card := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_attach]
    rfl
  rw [h1, h2]

theorem le_index_of_orderCheckLB {ws : List (List (Fin m × Bool))} {S : List ℕ} {k cap n : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheckLB ws S k cap n words fuel = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
      n ≤ (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index := by
  let st : St := cosetIdxGe_state (m := m) ws S k cap
  let P : Params := cosetIdxGe_params (m := m) ws S k
  have hOC : orderCheck ws S k cap n words fuel = true := by
    have h' := h
    unfold orderCheckLB at h'
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
    exact h'.1.1
  have hbf : basefixCheck ws S k st = true := by
    have h' := h
    unfold orderCheckLB at h'
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
    simpa only [st, P, cosetIdxGe_state, cosetIdxGe_params, cosetIdxGe_subWords] using h'.1.2
  have hr : cosetReachCheck ws S k st = true := by
    have h' := h
    unfold orderCheckLB at h'
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
    simpa only [st, P, cosetIdxGe_state, cosetIdxGe_params, cosetIdxGe_subWords] using h'.2
  have hc : st.complete P.L = true := by
    have h' := hOC
    unfold orderCheck at h'
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨-, hc⟩, -⟩, -⟩, -⟩, -⟩ := h'
    simpa only [st, P, cosetIdxGe_state, cosetIdxGe_params, cosetIdxGe_subWords] using hc
  have hn : st.liveCount = n := by
    have h' := hOC
    unfold orderCheck at h'
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨-, -⟩, hn⟩, -⟩, -⟩, -⟩ := h'
    simpa only [st, P, cosetIdxGe_state, cosetIdxGe_params, cosetIdxGe_subWords] using hn
  have hi : invConsistent P.L (colInv ws) st = true := by
    have h' := hOC
    unfold orderCheck at h'
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hi⟩, -⟩, -⟩ := h'
    simpa only [st, P, cosetIdxGe_state, cosetIdxGe_params, cosetIdxGe_subWords,
      invConsistentNative_eq] using hi
  have hrel : relsClosed P.L st (colCodes ws ws) = true := by
    have h' := hOC
    unfold orderCheck at h'
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hrel⟩, -⟩ := h'
    simpa only [st, P, cosetIdxGe_state, cosetIdxGe_params, cosetIdxGe_subWords,
      relsClosedNative_eq] using hrel
  let H : Subgroup (PG m ws) := genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)
  have hfiH : H.FiniteIndex := by
    have hsubs : ∀ w ∈ cosetIdxGe_subWords (m := m) S,
        PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w) ∈ H := by
      change ∀ w ∈ cosetIdxGe_subWords (m := m) S,
        PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w) ∈
          genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)
      simpa only [cosetIdxGe_subWords] using genSub_words_mem ws (subsetOf m S)
    have hcheck : subsetCheckShortC ws S k cap n = true := subsetCheckShortC_of_orderCheck hOC
    exact (index_le_of_checkHLT
      (goodColParamsShort ws (cosetIdxGe_subWords (m := m) S) k H hsubs)
      (by simpa [colParamsShort, mkParams] using closure_colLetter ws) hcheck).1
  let δ : ℕ → ℕ → ℕ := fun c x => st.tab.getD (c * P.L + colOfCode ws x) 0
  have hlive : ∀ c, st.live c = true → ∀ x < 2 * m, st.live (δ c x) = true :=
    fun c hl x hx => St.complete_step (L := P.L) hc hl (colOfCode_lt ws hx)
  have hinv : ∀ c, st.live c = true → ∀ x < 2 * m, δ (δ c x) (invCode x) = c := by
    intro c hl x hx
    have hx' : colOfCode ws x < P.L := colOfCode_lt ws hx
    have := invConsistent_spec (inv := colInv ws) hi hl hx'
    simp only [δ, colOfCode_invCode ws hx]
    exact this
  have hrel' : ∀ c, st.live c = true → ∀ r ∈ codes ws, r.foldl δ c = c := by
    intro c hl r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    show (v.map letterCode).foldl (fun c x => st.tab.getD (c * P.L + colOfCode ws x) 0) c = c
    rw [foldl_colOfCode ws st P.L]
    exact relsClosed_spec hrel hl (List.mem_map_of_mem hv)
  obtain ⟨ψ, hψ⟩ := exists_action_step ws (fun c => st.live c = true) δ hlive hinv hrel'
  let base : LiveNames st := ⟨1, St.live_one hc⟩
  letI : SMul (PG m ws) (LiveNames st) := ⟨fun g c => (ψ g⁻¹).unop c⟩
  letI : MulAction (PG m ws) (LiveNames st) :=
    { one_smul := fun c => by
        change (ψ (1 : PG m ws)⁻¹).unop c = c
        rw [inv_one, map_one]; rfl
      mul_smul := fun g h c => by
        change (ψ (g * h)⁻¹).unop c = (ψ g⁻¹).unop ((ψ h⁻¹).unop c)
        rw [mul_inv_rev]; exact act_mul ψ h⁻¹ g⁻¹ c }
  have hof : ∀ x ∈ subsetOf m S, (ψ (PresentedGroup.of x : PG m ws)).unop base = base := by
    intro x hx
    apply Subtype.ext
    have hlt : letterCode (x, true) < 2 * m := by
      have hx' : letterCode (x, true) = 2 * x.val := rfl
      rw [hx']; have := x.isLt; omega
    have hop : (PresentedGroup.of x : PG m ws) = presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (letterCode (x, true)) :=
      (presLetter_letterCode {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (x, true)).symm
    rw [hop, hψ (letterCode (x, true)) hlt base]
    simp only [δ, base, colOfCode_letterCode]
    exact cosetIdxGe_basefixCheck_sound hbf hx
  have hHK : H ≤ MulAction.stabilizer (PG m ws) base := by
    change genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S) ≤
      MulAction.stabilizer (PG m ws) base
    unfold genSub
    rw [Subgroup.closure_le]
    rintro g ⟨x, hx, rfl⟩
    refine MulAction.mem_stabilizer_iff.2 ?_
    change (ψ (PresentedGroup.of x : PG m ws)⁻¹).unop base = base
    rw [map_inv, MulOpposite.unop_inv]
    conv_lhs => rw [← hof x hx]
    exact Equiv.symm_apply_apply _ _
  have horbit : MulAction.orbit (PG m ws) base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro c
    rw [MulAction.mem_orbit_iff]
    obtain ⟨w, hw, hwalk⟩ := cosetIdxGe_reachCheck_sound hr c.1 c.2
    have hwL : ∀ y ∈ w, y < P.L := hw
    have htab : ∀ y < P.L, ∀ d : LiveNames st,
        ((ψ (colLetter ws y)).unop d).1 = st.tab.getD (d.1 * P.L + y) 0 := by
      intro y hy d
      have hyL : y < (cols ws).length := hy
      have hlt : letterCode ((cols ws)[y]'hyL) < 2 * m := by
        obtain ⟨i, b⟩ := (cols ws)[y]'hyL
        simp only [letterCode]; split <;> omega
      rw [colLetter_of_lt (ws := ws) hyL]
      rw [show PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
            (FreeGroup.mk [((cols ws)[y]'hyL)]) =
          presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
            (letterCode ((cols ws)[y]'hyL)) from
        (presLetter_letterCode {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} _).symm]
      rw [hψ (letterCode ((cols ws)[y]'hyL)) hlt d]
      simp only [δ]
      rw [colOfCode_letterCode]
      rw [cosetIdxGe_colCode_cols (m := m) hyL]
    refine ⟨(evalWord (colLetter ws) w)⁻¹, ?_⟩
    change (ψ ((evalWord (colLetter ws) w)⁻¹)⁻¹).unop base = c
    rw [inv_inv]
    apply Subtype.ext
    rw [act_evalWord_step (δ := fun c x => st.tab.getD (c * P.L + x) 0)
      (gen := colLetter ws) ψ htab w hwL base]
    change w.foldl (fun c x => st.tab.getD (c * (cols ws).length + x) 0) 1 = c.1
    exact hwalk
  have hcard : Nat.card (LiveNames st) = n := by
    rw [cosetIdxGe_card_live, hn]
  have hKindex : (MulAction.stabilizer (PG m ws) base).index = n := by
    rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, hcard]
  have hdvd : (MulAction.stabilizer (PG m ws) base).index ∣ H.index :=
    Subgroup.index_dvd_of_le hHK
  have hHpos : 0 < H.index := Nat.pos_of_ne_zero hfiH.index_ne_zero
  exact ⟨hfiH, by rw [← hKindex]; exact Nat.le_of_dvd hHpos hdvd⟩

end CFSG.CosetTable

end
