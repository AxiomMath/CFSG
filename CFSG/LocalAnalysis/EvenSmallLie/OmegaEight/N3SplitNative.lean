module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitFix

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {gs : Array (ℕ × ℕ)} {E : Enum}

theorem card_filter_eq (hE : enumOK gs E = true) (Q : ℕ → Prop) [DecidablePred Q]
    (P : GL12 → Prop) (hPQ : ∀ k x, Rep k x → k < 2 ^ 144 → (P x ↔ Q k)) :
    Nat.card {x : GL12 // x ∈ grpOf gs ∧ P x} =
      ((Finset.range E.keys.size).filter fun i => Q (E.keys.getD i 0)).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  choose f hf using fun i : ↥((Finset.range E.keys.size).filter fun i => Q (E.keys.getD i 0)) =>
    Enum.exists_mem hE i.1 (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1)
  choose g hg hgr using fun x : {x : GL12 // x ∈ grpOf gs ∧ P x} => Enum.exists_key hE x.2.1
  apply le_antisymm
  · refine Nat.card_le_card_of_injective (fun x => ⟨g x, Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hg x), (hPQ _ _ (hgr x) (Enum.key_lt hE (hg x))).1 x.2.2⟩⟩) ?_
    intro x y e
    have e' : g x = g y := congrArg Subtype.val e
    exact Subtype.ext ((hgr x).unique (e' ▸ hgr y))
  · refine Nat.card_le_card_of_injective (fun i => ⟨f i, (hf i).1, (hPQ _ _ (hf i).2
      (Enum.key_lt hE (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1))).2
        (Finset.mem_filter.1 i.2).2⟩) ?_
    intro i j e
    have e' : f i = f j := congrArg Subtype.val e
    have hi := Finset.mem_range.1 (Finset.mem_filter.1 i.2).1
    have hj := Finset.mem_range.1 (Finset.mem_filter.1 j.2).1
    exact Subtype.ext (Enum.index_unique hE hi hj ((hf i).2.key_unique (e' ▸ (hf j).2)
      (Enum.key_lt hE hi) (Enum.key_lt hE hj)))

theorem commute_iff_key {k sK : ℕ} {x s : GL12} (hx : Rep k x) (hs : Rep sK s) :
    x * s = s * x ↔ mulK k sK = mulK sK k := by
  refine ⟨fun e => key_eq_of_mul hx hs e, fun e => ?_⟩
  have h1 := hs.mul hx
  rw [← e] at h1
  exact (hx.mul hs).unique h1

theorem card_inf_centralizer_eq (hE : enumOK gs E = true) {s : GL12} {sK : ℕ} (hs : Rep sK s) :
    Nat.card ↥(grpOf gs ⊓ centralizer ({s} : Set GL12)) = commCount E sK := by
  have h1 := card_filter_eq hE (fun k => mulK k sK = mulK sK k) (fun x => x * s = s * x)
    (fun k x hx _ => commute_iff_key hx hs)
  rw [commCount, ← h1]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1, x.2.1, mem_centralizer_singleton_iff.1 x.2.2⟩
      invFun := fun x => ⟨x.1, x.2.1, mem_centralizer_singleton_iff.2 x.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem mulVecK_vecBits_iff {sK : ℕ} {s : GL12} (hs : Rep sK s) (v : Vec12) :
    mulVecK sK (vecBits v) = vecBits v ↔ (s : Mat12) *ᵥ v = v := by
  constructor
  · intro e
    have := congrArg (toVec 12) e
    rwa [toVec_mulVecK, toVec_vecBits, hs] at this
  · intro e
    apply toVec_injOn (mulVecK_lt _ _) (vecBits_lt _)
    rw [toVec_mulVecK, toVec_vecBits, hs, e]

theorem mulVecK_iff_toVec {sK : ℕ} {s : GL12} (hs : Rep sK s) {w : ℕ} (hw : w < 4096) :
    mulVecK sK w = w ↔ (s : Mat12) *ᵥ toVec 12 w = toVec 12 w := by
  rw [← mulVecK_vecBits_iff hs, vecBits_toVec hw]

@[expose] def fixesOn (vs : List ℕ) (c : ℕ) : Bool := vs.all fun v => mulVecK c v == v

theorem fixesOn_iff {sK cK : ℕ} {s c : GL12} (hs : Rep sK s) (hc : Rep cK c) :
    fixesOn (fixVecs sK) cK = true ↔ ∀ v, (s : Mat12) *ᵥ v = v → (c : Mat12) *ᵥ v = v := by
  simp only [fixesOn, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h v hv
    have hm : vecBits v ∈ fixVecs sK :=
      mem_fixVecs.2 ⟨vecBits_lt v, (mulVecK_vecBits_iff hs v).2 hv⟩
    exact (mulVecK_vecBits_iff hc v).1 (h _ hm)
  · intro h w hw
    obtain ⟨hw4, hfix⟩ := mem_fixVecs.1 hw
    exact (mulVecK_iff_toVec hc hw4).2 (h _ ((mulVecK_iff_toVec hs hw4).1 hfix))

@[expose] def kerOn (E : Enum) (s : ℕ) (vs : List ℕ) : ℕ :=
  ((Finset.range E.keys.size).filter fun i =>
    mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0) ∧ fixesOn vs (E.keys.getD i 0) = true).card

@[expose] def kerCount (E : Enum) (s : ℕ) : ℕ := kerOn E s (fixVecs s)

theorem card_kerSet_eq (hE : enumOK gs E = true) {s : GL12} {sK : ℕ} (hs : Rep sK s) :
    Nat.card (kerSet (grpOf gs) s) = kerCount E sK := by
  have h1 := card_filter_eq hE (fun k => mulK k sK = mulK sK k ∧ fixesOn (fixVecs sK) k = true)
    (fun x => x * s = s * x ∧ ∀ v, (s : Mat12) *ᵥ v = v → (x : Mat12) *ᵥ v = v)
    (fun k x hx _ => and_congr (commute_iff_key hx hs) (fixesOn_iff hs hx).symm)
  rw [kerCount, kerOn, ← h1]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

@[expose] def zfixOn (E : Enum) (s : ℕ) (vs : List ℕ) : ℕ :=
  let cs := E.keys.toList.filter fun c => mulK c s == mulK s c
  (vs.filter fun v => cs.all fun c => mulVecK c v == v).length

@[expose] def zfixCount (E : Enum) (s : ℕ) : ℕ := zfixOn E s (fixVecs s)

theorem zfixCount_le (hE : enumOK gs E = true) {s : GL12} {sK : ℕ} (hs : Rep sK s) :
    zfixCount E sK ≤ Nat.card (zfixSet (grpOf gs) s) := by
  classical
  have hnd : ((fixVecs sK).filter fun v =>
      (E.keys.toList.filter fun c => mulK c sK == mulK sK c).all fun c => mulVecK c v == v).Nodup :=
    (nodup_fixVecs sK).filter _
  rw [zfixCount, zfixOn, ← List.toFinset_card_of_nodup hnd, ← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective (fun w => ⟨toVec 12 w.1, ?_⟩) ?_
  · obtain ⟨hw, hcond⟩ := List.mem_filter.1 (List.mem_toFinset.1 w.2)
    obtain ⟨hw, hfix⟩ := mem_fixVecs.1 hw
    simp only [beq_iff_eq, List.all_eq_true, List.mem_filter] at hcond
    refine ⟨(mulVecK_iff_toVec hs hw).1 hfix, fun c hc hcs => ?_⟩
    obtain ⟨i, hi, hri⟩ := Enum.exists_key hE hc
    have hmem : E.keys.getD i 0 ∈ E.keys.toList := by
      rw [getD_mem hi]
      exact Array.getElem_mem_toList hi
    have := hcond _ ⟨hmem, by simpa using (commute_iff_key hri hs).1 hcs⟩
    exact (mulVecK_iff_toVec hri hw).1 this
  · intro w₁ w₂ e
    have e' : toVec 12 w₁.1 = toVec 12 w₂.1 := congrArg Subtype.val e
    have h1 := (mem_fixVecs.1 (List.mem_filter.1 (List.mem_toFinset.1 w₁.2)).1).1
    have h2 := (mem_fixVecs.1 (List.mem_filter.1 (List.mem_toFinset.1 w₂.2)).1).1
    exact Subtype.ext (toVec_injOn h1 h2 e')

@[expose] def candB (E : Enum) (s : ℕ) : Bool :=
  mulK s s == idK && s != idK && decide (fixCountF s ≤ 128) &&
    decide (16384 ≤ commCount E s * fixCountF s) && decide (zfixCount E s ≤ 2)

theorem candB_of_isCand (hE : enumOK gs E = true) {s : GL12} {sK : ℕ} (hs : Rep sK s)
    (h : IsCand (grpOf gs) s) : candB E sK = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hfix : fixCountF sK = Nat.card (fixM (s : Mat12)) := by
    rw [fixCountF_eq, ← card_fixM_eq, hs]
  simp only [candB, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (hs.mul hs).key_unique (by rw [h1]; exact rep_one) (mulK_lt _ _) idK_lt
  · intro e
    rw [e] at hs
    exact h2 (hs.unique rep_one)
  · rw [hfix]
    exact h3
  · rw [← card_inf_centralizer_eq hE hs, hfix]
    exact h4
  · exact (zfixCount_le hE hs).trans h5

theorem conj_of_key {sK tK yK : ℕ} {s tb y : GL12} (hs : Rep sK s) (ht : Rep tK tb)
    (hy : Rep yK y) (h : mulK yK tK = mulK sK yK) : s = y * tb * y⁻¹ := by
  have e : y * tb = s * y := by
    have h3 := hy.mul ht
    rw [h] at h3
    exact h3.unique (hs.mul hy)
  calc s = s * y * y⁻¹ := by group
    _ = y * tb * y⁻¹ := by rw [← e]

@[expose] def avoidCheck (E EY : Enum) : Bool := EY.keys.all fun s => !(candB E s)

theorem not_isCand_of_avoidCheck {hs : Array (ℕ × ℕ)} {EY : Enum} (hE : enumOK gs E = true)
    (hEY : enumOK hs EY = true) (h : avoidCheck E EY = true) {s : GL12} (hsY : s ∈ grpOf hs) :
    ¬ IsCand (grpOf gs) s := by
  intro hc
  obtain ⟨i, hi, hri⟩ := Enum.exists_key hEY hsY
  have hcb := candB_of_isCand hE hri hc
  simp only [avoidCheck, Array.all_eq_true, Bool.not_eq_true'] at h
  have := h i hi
  rw [← getD_mem hi] at this
  rw [this] at hcb
  exact Bool.false_ne_true hcb

@[expose] def burnPairs (E : Enum) (s : ℕ) : ℕ :=
  ((Finset.range E.keys.size ×ˢ Finset.range 4096).filter fun p =>
    mulK (E.keys.getD p.1 0) s = mulK s (E.keys.getD p.1 0) ∧ mulVecK s p.2 = p.2 ∧
      mulVecK (E.keys.getD p.1 0) p.2 = p.2).card

theorem card_burnSet_pairs (hE : enumOK gs E = true) {s : GL12} {sK : ℕ} (hs : Rep sK s) :
    Nat.card (burnSet (grpOf gs) s) = burnPairs E sK := by
  classical
  rw [burnPairs, ← Nat.card_eq_finsetCard]
  choose f hf using fun i : Fin E.keys.size => Enum.exists_mem hE i i.2
  choose g hg hgr using fun x : grpOf gs => Enum.exists_key hE x.2
  apply le_antisymm
  · refine Nat.card_le_card_of_injective (fun p => ⟨(g ⟨p.1.1, p.2.1⟩, vecBits p.1.2), ?_⟩) ?_
    · obtain ⟨h1, h2, h3, h4⟩ := p.2
      have hr := hgr ⟨p.1.1, h1⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 (hg _),
        Finset.mem_range.2 (vecBits_lt _)⟩, (commute_iff_key hr hs).1 h2,
        (mulVecK_vecBits_iff hs _).2 h3, (mulVecK_vecBits_iff hr _).2 h4⟩
    · intro p q e
      have e1 : g ⟨p.1.1, p.2.1⟩ = g ⟨q.1.1, q.2.1⟩ := congrArg (fun z => z.1.1) e
      have e2 : vecBits p.1.2 = vecBits q.1.2 := congrArg (fun z => z.1.2) e
      have h1 : p.1.1 = q.1.1 := by
        have h0 := hgr ⟨q.1.1, q.2.1⟩
        rw [← e1] at h0
        exact (hgr ⟨p.1.1, p.2.1⟩).unique h0
      have h2 : p.1.2 = q.1.2 := by
        rw [← toVec_vecBits p.1.2, ← toVec_vecBits q.1.2, e2]
      exact Subtype.ext (Prod.ext h1 h2)
  · refine Nat.card_le_card_of_injective (fun p => ⟨(f ⟨p.1.1, ?_⟩, toVec 12 p.1.2), ?_⟩) ?_
    · exact Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_filter.1 p.2).1).1
    · obtain ⟨hmem, h2, h3, h4⟩ := Finset.mem_filter.1 p.2
      have hv := Finset.mem_range.1 (Finset.mem_product.1 hmem).2
      have hi := Finset.mem_range.1 (Finset.mem_product.1 hmem).1
      have hr := (hf ⟨p.1.1, hi⟩).2
      exact ⟨(hf _).1, (commute_iff_key hr hs).2 h2, (mulVecK_iff_toVec hs hv).1 h3,
        (mulVecK_iff_toVec hr hv).1 h4⟩
    · intro p q e
      have hmp := Finset.mem_product.1 (Finset.mem_filter.1 p.2).1
      have hmq := Finset.mem_product.1 (Finset.mem_filter.1 q.2).1
      have e1 := congrArg (fun z => z.1.1) e
      have e2 := congrArg (fun z => z.1.2) e
      simp only at e1 e2
      have hip := Finset.mem_range.1 hmp.1
      have hiq := Finset.mem_range.1 hmq.1
      have h1 : p.1.1 = q.1.1 := Enum.index_unique hE hip hiq
        ((hf ⟨p.1.1, hip⟩).2.key_unique (e1 ▸ (hf ⟨q.1.1, hiq⟩).2) (Enum.key_lt hE hip)
          (Enum.key_lt hE hiq))
      have h2 : p.1.2 = q.1.2 :=
        toVec_injOn (Finset.mem_range.1 hmp.2) (Finset.mem_range.1 hmq.2) e2
      exact Subtype.ext (Prod.ext h1 h2)

@[expose] def burnOn (E : Enum) (s : ℕ) (vs : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range E.keys.size,
    if mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0) then
      (vs.filter fun v => mulVecK (E.keys.getD i 0) v == v).length else 0

@[expose] def burnCount (E : Enum) (s : ℕ) : ℕ := burnOn E s (fixVecs s)

theorem burnPairs_eq (E : Enum) (s : ℕ) : burnPairs E s = burnCount E s := by
  rw [burnPairs, burnCount, burnOn, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0)
  · simp only [hc, ↓reduceIte]
    have hnd : ((fixVecs s).filter fun v => mulVecK (E.keys.getD i 0) v == v).Nodup :=
      (nodup_fixVecs s).filter _
    have e : ((fixVecs s).filter fun v => mulVecK (E.keys.getD i 0) v == v).toFinset =
        (Finset.range 4096).filter fun v => mulVecK s v = v ∧ mulVecK (E.keys.getD i 0) v = v := by
      ext v
      rw [List.mem_toFinset, List.mem_filter, mem_fixVecs, Finset.mem_filter, Finset.mem_range,
        beq_iff_eq, and_assoc]
    rw [← List.toFinset_card_of_nodup hnd, e, Finset.card_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [true_and]
  · simp only [hc, ↓reduceIte]
    exact Finset.sum_eq_zero fun v _ => by simp only [false_and, ↓reduceIte]

theorem card_burnSet_eq (hE : enumOK gs E = true) {s : GL12} {sK : ℕ} (hs : Rep sK s) :
    Nat.card (burnSet (grpOf gs) s) = burnCount E sK := by
  rw [← burnPairs_eq]
  exact card_burnSet_pairs hE hs

@[expose] def maxCheck (E : Enum) (tK : ℕ) : Bool :=
  let b := burnCount E tK
  E.keys.all fun s => mulK s s != idK || fixCountF s != 64 || commCount E s != 256 ||
    burnCount E s != b || E.keys.any fun y => mulK y tK == mulK s y

theorem conj_of_maxCheck (hE : enumOK gs E = true) {tK : ℕ} (h : maxCheck E tK = true)
    {tb : GL12} (ht : Rep tK tb) {s : GL12} (hs : s ∈ grpOf gs) (hs2 : s * s = 1)
    (hfix : Nat.card (fixM (s : Mat12)) = 2 ^ 6)
    (hcs : Nat.card ↥(grpOf gs ⊓ centralizer ({s} : Set GL12)) = 2 ^ 8)
    (hb : Nat.card (burnSet (grpOf gs) s) = Nat.card (burnSet (grpOf gs) tb)) :
    ∃ y ∈ grpOf gs, s = y * tb * y⁻¹ := by
  obtain ⟨i, hi, hri⟩ := Enum.exists_key hE hs
  simp only [maxCheck, Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Array.any_eq_true, beq_iff_eq] at h
  rcases h i hi with ((((h1 | h1) | h1) | h1) | ⟨j, hj, h1⟩)
  · rw [← getD_mem hi] at h1
    exact absurd ((hri.mul hri).key_unique (by rw [hs2]; exact rep_one) (mulK_lt _ _) idK_lt) h1
  · rw [← getD_mem hi] at h1
    exact absurd (by rw [fixCountF_eq, ← card_fixM_eq, hri, hfix]; norm_num) h1
  · rw [← getD_mem hi] at h1
    exact absurd (by rw [← card_inf_centralizer_eq hE hri, hcs]; norm_num) h1
  · rw [← getD_mem hi] at h1
    exact absurd (by rw [← card_burnSet_eq hE hri, ← card_burnSet_eq hE ht, hb]) h1
  · obtain ⟨y, hy, hry⟩ := Enum.exists_mem hE j hj
    rw [← getD_mem hi, ← getD_mem hj] at h1
    exact ⟨y, hy, conj_of_key hri ht hry h1⟩

end CFSG.EvenSmallLie.OmegaEight.N3Split
