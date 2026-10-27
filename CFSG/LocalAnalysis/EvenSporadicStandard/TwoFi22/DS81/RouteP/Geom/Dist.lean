module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.OrbitReps
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Graph
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Orders

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.CosetTable CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem geomReps_lt : ∀ i : Fin 7, geomReps[i.val]! < 920808 := by decide

@[expose] def repPt (i : Fin 7) : Ω := ⟨geomReps[i.val]!, geomReps_lt i⟩

theorem repPt_val (i : Fin 7) : (repPt i).val = geomReps[i.val]! := rfl

theorem repPt_zero : repPt 0 = x0 := Fin.ext (by decide)

theorem repPt_one : repPt 1 = x1 := Fin.ext (by decide)

@[expose] def y2 : Ω := repPt 2

@[expose] def y3a : Ω := repPt 3

@[expose] def y3b : Ω := repPt 4

@[expose] def y4a : Ω := repPt 5

@[expose] def y4b : Ω := repPt 6

@[expose] def reps : List Ω := [x0, x1, y2, y3a, y3b, y4a, y4b]

theorem mem_reps_iff {r : Ω} : r ∈ reps ↔ ∃ i : Fin 7, repPt i = r := by
  constructor
  · intro h
    simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, repPt_zero⟩
    · exact ⟨1, repPt_one⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · simp [reps, repPt_zero]
    · simp [reps, repPt_one]
    · simp [reps, y2]
    · simp [reps, y3a]
    · simp [reps, y3b]
    · simp [reps, y4a]
    · simp [reps, y4b]

section Extract

theorem zpTreesOK_spec {gs : Array Table} {trees : Array CFSG.Perm.Native.Tree}
    (h : zpTreesOK gs trees = true) : trees.size = 7 ∧ ∀ i < 7,
      trees[i]!.pts.size = geomSizes[i]! ∧
        CFSG.Perm.Native.treeOK degree geomReps[i]! trees[i]! gs zpLetters = true := by
  unfold zpTreesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have := allIn_zero_iff.1 h.2 i hi
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem labOK_spec {gs : Array Table} {trees : Array CFSG.Perm.Native.Tree} {lab : Table}
    (h : labOK gs trees lab = true) :
    (∀ i < 7, ap lab geomReps[i]! = i) ∧
      (∀ v < degree, ap lab v < 7 ∧ memTree trees[ap lab v]! v = true) ∧
      (∀ l ∈ zpLetters, ∀ v < degree, ap lab (ap gs[l]! v) = ap lab v) := by
  unfold labOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i hi => beq_iff_eq.1 (allIn_zero_iff.1 h1 i hi), fun v hv => ?_, fun l hl v hv => ?_⟩
  · have := allIn_zero_iff.1 h2 v hv
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  · obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hl
    have := allIn_zero_iff.1 ((Array.all_eq_true.1 h3) j hj) v hv
    simpa using this

theorem memTree_spec {T : CFSG.Perm.Native.Tree} {p : ℕ} (h : memTree T p = true) :
    ∃ k < T.pts.size, ap T.pts k = p := by
  simp only [memTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨ap T.pos p, h.1, h.2⟩

theorem distOK_spec {lab : Table} {tabs : Array Table} {gamma : Table}
    (h : distOK lab tabs gamma = true) :
    tabs.size = 7 ∧ (∀ i < 7, geomLevels[i]! = 0 → geomReps[i]! = 0) ∧
      ∀ i < 7, ap tabs[i]! 0 = geomReps[i]! ∧
        (geomLevels[i]! = 0 ∨
          ∃ c ∈ gamma, geomLevels[ap lab (ap tabs[i]! c.toNat)]! + 1 = geomLevels[i]!) ∧
        ∀ c ∈ gamma, geomLevels[ap lab (ap tabs[i]! c.toNat)]! ≤ geomLevels[i]! + 1 := by
  unfold distOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, -⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun i hi hz => ?_, fun i hi => ?_⟩
  · have := allIn_zero_iff.1 h3 i hi
    simpa [hz] using this
  · have := allIn_zero_iff.1 h4 i hi
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
      Array.any_eq_true, Array.all_eq_true] at this
    obtain ⟨⟨h5, h6⟩, h7⟩ := this
    refine ⟨h5, ?_, ?_⟩
    · rcases h6 with h6 | ⟨j, hj, h6⟩
      · exact Or.inl h6
      · exact Or.inr ⟨gamma[j], Array.getElem_mem hj, by simpa using h6⟩
    · intro c hc
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hc
      simpa using h7 j hj

end Extract

section Soundness


theorem rep_genQ_of_mem_zpLetters {l : ℕ} (hl : l ∈ zpLetters) :
    Rep 920808 (genTabs ())[l]! (genQ l) := by
  have hl' := mem_zpLetters_iff.1 hl
  exact rep_genQ (by simp [S0] at hl'; omega)

theorem treeFacts (i : Fin 7) :
    CFSG.Perm.TreeFacts 920808 gTrees[i.val]! zpLetters genQ geomReps[i.val]! :=
  CFSG.Perm.treeOK_facts (n := 920808) (fun _ hl => rep_genQ_of_mem_zpLetters hl)
    ((zpTreesOK_spec geomFacts.trees_ok).2 i.val i.isLt).2

theorem mem_orbit_repPt_iff (i : Fin 7) (v : Ω) :
    v ∈ MulAction.orbit Zp (repPt i) ↔
      ∃ k < gTrees[i.val]!.pts.size, ap gTrees[i.val]!.pts k = v.val := by
  have h := (treeFacts i).mem_orbit_iff v
  rw [lettersGroup_zpLetters] at h
  exact h

theorem card_orbit_repPt (i : Fin 7) :
    Nat.card (MulAction.orbit Zp (repPt i)) = geomSizes[i.val]! := by
  have h := (treeFacts i).card_orbit
  rw [lettersGroup_zpLetters, ((zpTreesOK_spec geomFacts.trees_ok).2 i.val i.isLt).1] at h
  exact h

@[expose] def orbLabel (v : Ω) : ℕ := ap gLab v.val

@[expose] def distLevel (v : Ω) : ℕ := geomLevels[orbLabel v]!

theorem orbLabel_repPt (i : Fin 7) : orbLabel (repPt i) = i.val :=
  (labOK_spec geomFacts.lab_ok).1 i.val i.isLt

theorem orbLabel_lt (v : Ω) : orbLabel v < 7 :=
  ((labOK_spec geomFacts.lab_ok).2.1 v.val v.isLt).1

theorem orbLabel_smul_genQ {l : ℕ} (hl : l ∈ zpLetters) (v : Ω) :
    orbLabel (genQ l • v) = orbLabel v := by
  unfold orbLabel
  rw [smul_val_of_rep (rep_genQ_of_mem_zpLetters hl) v]
  exact (labOK_spec geomFacts.lab_ok).2.2 l hl v.val v.isLt

theorem orbLabel_smul {k : Q3} (hk : k ∈ Zp) (v : Ω) : orbLabel (k • v) = orbLabel v := by
  have key : ∀ k ∈ Subgroup.closure {g : Q3 | ∃ l ∈ zpLetters, genQ l = g}, ∀ v : Ω,
      orbLabel (k • v) = orbLabel v :=
    smul_apply_eq_of_mem_closure fun s hs v => by
      obtain ⟨l, hl, rfl⟩ := hs
      exact orbLabel_smul_genQ hl v
  rw [← lettersGroup_zpLetters] at hk
  exact key k hk v

theorem distLevel_smul {k : Q3} (hk : k ∈ Zp) (v : Ω) : distLevel (k • v) = distLevel v := by
  simp only [distLevel, orbLabel_smul hk v]

theorem distLevel_repPt (i : Fin 7) : distLevel (repPt i) = geomLevels[i.val]! := by
  simp only [distLevel, orbLabel_repPt]

theorem distLevel_eq_of_mem_orbit {r v : Ω} (h : v ∈ MulAction.orbit Zp r) :
    distLevel v = distLevel r := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := h
  exact distLevel_smul hk r

theorem orbLabel_eq_of_mem_orbit {r v : Ω} (h : v ∈ MulAction.orbit Zp r) :
    orbLabel v = orbLabel r := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := h
  exact orbLabel_smul hk r

theorem exists_mem_orbit_repPt (v : Ω) : ∃ i : Fin 7, v ∈ MulAction.orbit Zp (repPt i) := by
  obtain ⟨hlt, hmem⟩ := (labOK_spec geomFacts.lab_ok).2.1 v.val v.isLt
  refine ⟨⟨ap gLab v.val, hlt⟩, ?_⟩
  rw [mem_orbit_repPt_iff]
  exact memTree_spec hmem

theorem exists_mem_reps (v : Ω) : ∃ r ∈ reps, ∃ k ∈ Zp, k • r = v := by
  obtain ⟨i, ⟨k, hk⟩, hkv⟩ := exists_mem_orbit_repPt v
  exact ⟨repPt i, mem_reps_iff.2 ⟨i, rfl⟩, k, hk, hkv⟩

theorem ap_getElem (a : Array UInt32) {k : ℕ} (hk : k < a.size) : ap a k = (a[k]).toNat := by
  simp only [ap, getElem!_pos a k hk]

theorem mem_orbit_x1_iff (v : Ω) :
    v ∈ MulAction.orbit Zp x1 ↔
      ∃ k < gTrees[1]!.pts.size, ap gTrees[1]!.pts k = v.val := by
  have := mem_orbit_repPt_iff 1 v
  rw [repPt_one] at this
  exact this

theorem mem_gamma_iff {c : UInt32} :
    c ∈ gTrees[1]!.pts ↔ ∃ h : c.toNat < 920808,
      (⟨c.toNat, h⟩ : Ω) ∈ MulAction.orbit Zp x1 := by
  constructor
  · intro hc
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hc
    have hlt : ap gTrees[1]!.pts k < 920808 := (treeFacts 1).pts_lt k hk
    rw [ap_getElem _ hk] at hlt
    refine ⟨hlt, ?_⟩
    exact (mem_orbit_x1_iff ⟨(gTrees[1]!.pts[k]).toNat, hlt⟩).2 ⟨k, hk, by rw [ap_getElem _ hk]⟩
  · rintro ⟨h, hmem⟩
    obtain ⟨k, hk, hkc⟩ := (mem_orbit_x1_iff _).1 hmem
    rw [ap_getElem _ hk] at hkc
    have : gTrees[1]!.pts[k] = c := UInt32.toNat_inj.1 hkc
    exact this ▸ Array.getElem_mem hk

@[expose] noncomputable def repElt (i : Fin 7) : Q3 :=
  wordG (letterPerm mQ 2) gWords[i.val]!

theorem rep_repElt (i : Fin 7) :
    Rep 920808 (repTabs (mTabs ()) gWords)[i.val]! (repElt i) := by
  have hw : i.val < gWords.size := by rw [geomFacts.words_size]; exact i.isLt
  have e : (repTabs (mTabs ()) gWords)[i.val]! =
      wordT 920808 (letterTab 920808 (mTabs ()) ((mTabs ()).map (invT 920808)))
        gWords[i.val]! := by
    simp only [repTabs]
    rw [getElem!_pos _ _ (by simpa using hw), Array.getElem_map, getElem!_pos gWords _ hw]
  rw [e]
  exact rep_wordT_m _

theorem repElt_smul_x0 (i : Fin 7) : repElt i • x0 = repPt i := by
  apply Fin.ext
  rw [smul_val_of_rep (rep_repElt i) x0, x0_val, repPt_val]
  exact ((distOK_spec geomFacts.dist_ok).2.2 i.val i.isLt).1

theorem Δ_adj_x0_iff_mem_gamma (v : Ω) :
    Δ.Adj x0 v ↔ ∃ c ∈ gTrees[1]!.pts, c.toNat = v.val := by
  rw [Δ_adj_x0_iff, mem_orbit_x1_iff]
  constructor
  · rintro ⟨k, hk, hkv⟩
    exact ⟨gTrees[1]!.pts[k], Array.getElem_mem hk, by rw [← ap_getElem _ hk, hkv]⟩
  · rintro ⟨c, hc, hcv⟩
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hc
    exact ⟨k, hk, by rw [ap_getElem _ hk, hcv]⟩

theorem Δ_adj_repPt_iff (i : Fin 7) (v : Ω) :
    Δ.Adj (repPt i) v ↔
      ∃ c ∈ gTrees[1]!.pts, ap (repTabs (mTabs ()) gWords)[i.val]! c.toNat = v.val := by
  rw [← repElt_smul_x0 i, Δ_adj_smul_x0_iff, mem_orbit_x1_iff]
  constructor
  · rintro ⟨k, hk, hkv⟩
    refine ⟨gTrees[1]!.pts[k], Array.getElem_mem hk, ?_⟩
    rw [← ap_getElem _ hk, hkv, ← smul_val_of_rep (rep_repElt i), smul_inv_smul]
  · rintro ⟨c, hc, hcv⟩
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hc
    have hlt : (gTrees[1]!.pts[k]).toNat < 920808 := by
      have : ap gTrees[1]!.pts k < 920808 := (treeFacts 1).pts_lt k hk
      rwa [ap_getElem _ hk] at this
    have hv : v = repElt i • (⟨(gTrees[1]!.pts[k]).toNat, hlt⟩ : Ω) :=
      Fin.ext (by rw [smul_val_of_rep (rep_repElt i), ← hcv])
    refine ⟨k, hk, ?_⟩
    rw [hv, inv_smul_smul, ap_getElem _ hk]

theorem distLevel_hdown (r : Ω) (hr : r ∈ reps) (k : ℕ) (hk : distLevel r = k + 1) :
    ∃ n, Δ.Adj r n ∧ distLevel n = k := by
  obtain ⟨i, rfl⟩ := mem_reps_iff.1 hr
  rw [distLevel_repPt] at hk
  obtain ⟨-, -, hi⟩ := distOK_spec geomFacts.dist_ok
  obtain ⟨-, h2, -⟩ := hi i.val i.isLt
  rcases h2 with h2 | ⟨c, hc, h2⟩
  · omega
  · obtain ⟨hlt, hmem⟩ := mem_gamma_iff.1 hc
    refine ⟨repElt i • ⟨c.toNat, hlt⟩, ?_, ?_⟩
    · rw [← repElt_smul_x0 i, Δ_adj_smul_x0_iff, inv_smul_smul]
      exact hmem
    · rw [distLevel, orbLabel, smul_val_of_rep (rep_repElt i) ⟨c.toNat, hlt⟩]
      show geomLevels[ap gLab (ap (repTabs (mTabs ()) gWords)[i.val]! c.toNat)]! = k
      omega

theorem distLevel_hlip (r : Ω) (hr : r ∈ reps) (v : Ω) (hv : Δ.Adj r v) :
    distLevel v ≤ distLevel r + 1 := by
  obtain ⟨i, rfl⟩ := mem_reps_iff.1 hr
  rw [distLevel_repPt]
  obtain ⟨-, -, hi⟩ := distOK_spec geomFacts.dist_ok
  obtain ⟨-, -, h3⟩ := hi i.val i.isLt
  rw [← repElt_smul_x0 i, Δ_adj_smul_x0_iff] at hv
  obtain ⟨k, hk, hkv⟩ := (mem_orbit_x1_iff _).1 hv
  have h1 : v.val = ap (repTabs (mTabs ()) gWords)[i.val]! (gTrees[1]!.pts[k]).toNat := by
    rw [← ap_getElem _ hk, hkv, ← smul_val_of_rep (rep_repElt i), smul_inv_smul]
  have h2 : distLevel v =
      geomLevels[ap gLab (ap (repTabs (mTabs ()) gWords)[i.val]! (gTrees[1]!.pts[k]).toNat)]! := by
    rw [← h1]
    rfl
  rw [h2]
  exact h3 _ (Array.getElem_mem hk)

theorem distLevel_huniq (r : Ω) (hr : r ∈ reps) (h : distLevel r = 0) : r = x0 := by
  obtain ⟨i, rfl⟩ := mem_reps_iff.1 hr
  rw [distLevel_repPt] at h
  apply Fin.ext
  rw [repPt_val, x0_val]
  exact (distOK_spec geomFacts.dist_ok).2.1 i.val i.isLt h

theorem reachable_and_dist_x0 :
    (∀ c, Δ.Reachable x0 c) ∧ ∀ c, Δ.dist x0 c = distLevel c := by
  refine dist_eq_of_level_of_reps Δ_adj_smul Zp (f := distLevel) (R := reps)
    (fun k hk => Zp_smul_x0 hk) (fun k hk v => distLevel_smul hk v) exists_mem_reps ?_
    distLevel_huniq distLevel_hdown distLevel_hlip
  rw [← repPt_zero, distLevel_repPt]
  rfl

theorem Δ_reachable_x0 (v : Ω) : Δ.Reachable x0 v := reachable_and_dist_x0.1 v

theorem Δ_dist_x0 (v : Ω) : Δ.dist x0 v = distLevel v := reachable_and_dist_x0.2 v

theorem Δ_connected : Δ.Connected := by
  haveI : Nonempty Ω := ⟨x0⟩
  exact ⟨fun u w => (Δ_reachable_x0 u).symm.trans (Δ_reachable_x0 w)⟩

theorem distLevel_le_four (v : Ω) : distLevel v ≤ 4 := by
  have h : ∀ i : Fin 7, geomLevels[i.val]! ≤ 4 := by decide
  exact h ⟨orbLabel v, orbLabel_lt v⟩

theorem Δ_dist_x0_le_four (v : Ω) : Δ.dist x0 v ≤ 4 := by
  rw [Δ_dist_x0]
  exact distLevel_le_four v

theorem Δ_dist_le_four (x y : Ω) : Δ.dist x y ≤ 4 :=
  dist_le_of_base Δ_adj_smul x0 Δ_dist_x0_le_four x y

end Soundness

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
