module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrameCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCoords

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.RankThree.Native CFSG.ComponentClassification.J2Cover

theorem reflArrs_get {a : ℕ} (ha : a < 240) : reflArrs[a]! = reflArr a :=
  getElem!_toArray_map_range _ ha

theorem refl_conj_refl {a : ℕ} (ha : a < 240) (r : Fin 240) :
    refl a * refl r * (refl a)⁻¹ = refl (refl a r) := by
  have h := allLt_spec (allLt_spec equiv_check ha) r.2
  rw [reflArrs_get ha, reflArrs_get r.2, reflArrs_get (by
    rw [(rep_refl ha).apply r.2]; exact (refl a _).2)] at h
  rw [refl_inv ha]
  refine eq_of_eqA (rep_compA (rep_compA (rep_refl ha) (rep_refl r.2)) (rep_refl ha))
    (rep_refl (refl a r).2) ?_
  rwa [(rep_refl ha).apply r.2] at h

theorem refl_conj {g : Equiv.Perm (Fin 240)} (hg : g ∈ wE8) (r : Fin 240) :
    g * refl r * g⁻¹ = refl (g r) := by
  revert r
  refine wE8_induction (P := fun g => ∀ r : Fin 240, g * refl r * g⁻¹ = refl (g r))
    (fun r => by rw [one_mul, inv_one, mul_one]; rfl) (fun a ha g hg r => ?_) g hg
  rw [show refl a * g * refl r * (refl a * g)⁻¹ = refl a * (g * refl r * g⁻¹) * (refl a)⁻¹ by
    group, hg r, refl_conj_refl ha]
  rfl

theorem wQ_valid : ValidSchreier wQ := ofArrays_valid (by norm_num) wChain_ok.1.1

theorem wQ_baseCount : wQ.baseCount = 8 := rfl

theorem wQ_base_get (i : Fin wQ.baseCount) : (wQ.base.get i : ℕ) = keyPts.getD i 0 := by
  have hi : (i : ℕ) < 8 := i.2
  change ((wBase.toArray)[(i : ℕ)] : ℕ) = _
  interval_cases (i : ℕ) <;> rfl

theorem mem_levelSubgroup_of_fixes {g : Equiv.Perm (Fin 240)} (hg : g ∈ wE8) :
    ∀ k ≤ 8, (∀ i : Fin wQ.baseCount, (i : ℕ) < k → g (wQ.base.get i) = wQ.base.get i) →
      g ∈ wQ.levelSubgroup k := by
  intro k
  induction k with
  | zero =>
    intro _ _
    rw [wQ.levelSubgroup_zero_eq_original wQ_valid, ← wE8_eq]
    exact hg
  | succ k ih =>
    intro hk hfix
    have hk' : k < wQ.baseCount := by rw [wQ_baseCount]; omega
    have h := wQ.levelSubgroup_succ_eq_stabilizer wQ_valid ⟨k, hk'⟩
    change wQ.levelSubgroup (k + 1) = _ at h
    rw [h]
    refine ⟨ih (by omega) fun i hi => hfix i (by omega), ?_⟩
    exact MulAction.mem_stabilizer_iff.2 (hfix ⟨k, hk'⟩ (by simp))

theorem eq_one_of_fixes_frame {g : Equiv.Perm (Fin 240)} (hg : g ∈ wE8)
    (hfix : ∀ i : Fin 8, g ⟨frameRoot i, frameRoot_lt i⟩ = ⟨frameRoot i, frameRoot_lt i⟩) :
    g = 1 := by
  have hmem := mem_levelSubgroup_of_fixes hg 8 le_rfl fun i _ => by
    have hi : (i : ℕ) < 8 := i.2
    have e : wQ.base.get i = ⟨frameRoot ⟨i, hi⟩, frameRoot_lt _⟩ :=
      Fin.ext (by rw [wQ_base_get]; exact keyPts_getD ⟨i, hi⟩)
    rw [e]
    exact hfix ⟨i, hi⟩
  rw [← wQ_baseCount, wQ.levelSubgroup_terminal_eq_bot wQ_valid, mem_bot] at hmem
  exact hmem

theorem eq_of_frame {g h : Equiv.Perm (Fin 240)} (hg : g ∈ wE8) (hh : h ∈ wE8)
    (he : ∀ i : Fin 8, g ⟨frameRoot i, frameRoot_lt i⟩ = h ⟨frameRoot i, frameRoot_lt i⟩) :
    g = h := by
  have h1 := eq_one_of_fixes_frame (mul_mem (inv_mem hh) hg) fun i => by
    rw [Equiv.Perm.mul_apply, he i, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  rw [← mul_inv_cancel_left h g, h1, mul_one]

structure FrameFacts : Prop where
  memE1 : ∀ r < 240, memE1 frameArrs reflArrs[r]! = frame16.contains r
  mask : ∀ m < 256, frameMaskOf frameArrs[m]! = m
  img : ∀ m < 256, ∀ i < 8, (frameArrs[m]!)[keyPts.getD i 0]! =
    if m.testBit i then negArr[keyPts.getD i 0]! else keyPts.getD i 0
  neg1 : ∀ i < 8, negSet reflArrs[keyPts.getD i 0]! =
    [keyPts.getD i 0, negArr[keyPts.getD i 0]!].mergeSort (fun a b => decide (a ≤ b))
  neg2 : ∀ i < 8, ∀ j < 8, i ≠ j → negSet frameArrs[2 ^ i + 2 ^ j]! =
    [keyPts.getD i 0, negArr[keyPts.getD i 0]!, keyPts.getD j 0,
      negArr[keyPts.getD j 0]!].mergeSort (fun a b => decide (a ≤ b))
  plane : ∀ m < 256, framePop m = 4 → (fixCount 240 frameArrs[m]! = 24 ↔ frameIsPlane m = true)

theorem frame_facts : FrameFacts := by
  have h := frame_check
  simp only [frameCheck, frameCheckWith, Bool.and_eq_true, allLt_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun i hi j hj hij => ?_, fun m hm h4m => ?_⟩
  · have := h5 i hi j hj
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at this
    exact this.resolve_left hij
  · have := h6 m hm
    rw [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd h4m h
    · rw [← h]
      exact (beq_iff_eq).symm.trans (by simp)

theorem mem_negSet {t : Array ℕ} {X : Equiv.Perm (Fin 240)} (ht : Rep 240 t X) (r : Fin 240) :
    (r : ℕ) ∈ negSet t ↔ X r = zPerm r := by
  rw [negSet, List.mem_filter, List.mem_range, beq_iff_eq, ht.apply r.2, rep_negArr.apply r.2]
  constructor
  · rintro ⟨-, h⟩
    exact Fin.ext h
  · intro h
    exact ⟨r.2, by rw [h]⟩

@[expose] def fpt (i : Fin 8) : Fin 240 := ⟨frameRoot i, frameRoot_lt i⟩

theorem fpt_val (i : Fin 8) : (fpt i : ℕ) = keyPts.getD i 0 := (keyPts_getD i).symm

theorem frameElt_fpt (v : FrameVec) (i : Fin 8) :
    frameElt v (fpt i) = if v i = 1 then zPerm (fpt i) else fpt i := by
  have h := frame_facts.img (frameEncode v) (frameEncode_lt v) i i.2
  rw [frameArrs_encode, ← fpt_val, (rep_frameArr v).apply (fpt i).2] at h
  have hb : (frameEncode v).testBit i = decide (v i = 1) := by
    have := congrFun (frameDecode_frameEncode v) i
    rw [frameDecode] at this
    by_cases hv : v i = 1
    · rw [decide_eq_true hv]
      by_contra hc
      rw [Bool.not_eq_true] at hc
      rw [hc] at this
      simp only [Bool.false_eq_true, ite_false] at this
      rw [← this] at hv
      exact absurd hv (by decide)
    · rw [decide_eq_false hv]
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rw [hc] at this
      simp only [ite_true] at this
      exact hv this.symm
  rw [hb] at h
  by_cases hv : v i = 1
  · simp only [hv, decide_true, ↓reduceIte] at h ⊢
    apply Fin.ext
    rw [rep_negArr.apply (fpt i).2] at h
    exact h
  · simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    apply Fin.ext
    exact h

theorem zPerm_apply_ne (r : Fin 240) : zPerm r ≠ r := by
  intro h
  have h1 := card_fixedPoints_of_rep rep_negArr
  rw [refl_facts.zfix] at h1
  exact (Fintype.card_eq_zero_iff.1 h1).false ⟨r, h⟩

theorem zPerm_zPerm (r : Fin 240) : zPerm (zPerm r) = r := by
  rw [← Equiv.Perm.mul_apply, zPerm_mul_self, Equiv.Perm.one_apply]

theorem neg_of_comm {w X : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) (hc : w * X = X * w)
    {r : Fin 240} (hr : X r = zPerm r) : X (w r) = zPerm (w r) := by
  rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hr, ← Equiv.Perm.mul_apply,
    zPerm_comm w hw, Equiv.Perm.mul_apply]

theorem mem_pair_of_mem_mergeSort {a b x : ℕ}
    (h : x ∈ [a, b].mergeSort (fun a b => decide (a ≤ b))) : x = a ∨ x = b := by
  rw [List.mem_mergeSort] at h
  simpa using h

theorem mem_four_of_mem_mergeSort {a b c d x : ℕ}
    (h : x ∈ [a, b, c, d].mergeSort (fun a b => decide (a ≤ b))) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  rw [List.mem_mergeSort] at h
  simpa using h

theorem refl_fpt (i : Fin 8) : refl (fpt i) = frameElt (frameE i) := (frameElt_frameE i).symm

theorem fpt_negated (v : FrameVec) (i : Fin 8) (hv : v i = 1) :
    frameElt v (fpt i) = zPerm (fpt i) := by
  rw [frameElt_fpt, ite_eq_left hv]

theorem apply_fpt_of_comm_refl {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) (i : Fin 8)
    (hc : w * refl (fpt i) = refl (fpt i) * w) : w (fpt i) = fpt i ∨ w (fpt i) = zPerm (fpt i) := by
  have hr : refl (fpt i) (fpt i) = zPerm (fpt i) := by
    rw [refl_fpt]
    exact fpt_negated _ i (by simp [frameE])
  have h := neg_of_comm hw hc hr
  have hmem := (mem_negSet (rep_refl (fpt i).2) (w (fpt i))).2 h
  have h1 := frame_facts.neg1 i i.2
  rw [← fpt_val, reflArrs_get (fpt i).2] at h1
  rw [h1] at hmem
  rcases mem_pair_of_mem_mergeSort hmem with h2 | h2
  · exact Or.inl (Fin.ext h2)
  · refine Or.inr (Fin.ext ?_)
    rw [h2, rep_negArr.apply (fpt i).2]

theorem mem_e1Sub_of_fpt {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (h : ∀ i, w (fpt i) = fpt i ∨ w (fpt i) = zPerm (fpt i)) : w ∈ e1Sub := by
  classical
  set v : FrameVec := fun i => if w (fpt i) = fpt i then 0 else 1 with hv
  have he : frameElt v = w := eq_of_frame (frameElt_mem_wE8 v) hw fun i => by
    change frameElt v (fpt i) = w (fpt i)
    rw [frameElt_fpt]
    by_cases hi : w (fpt i) = fpt i
    · have : v i ≠ 1 := by rw [hv]; simp [hi]
      rw [ite_eq_right this, hi]
    · have : v i = 1 := by rw [hv]; simp [hi]
      rw [ite_eq_left this, (h i).resolve_left hi]
  exact mem_e1Sub.2 ⟨v, he⟩

theorem centralizer_e1Sub {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hc : ∀ e ∈ e1Sub, w * e = e * w) : w ∈ e1Sub :=
  mem_e1Sub_of_fpt hw fun i => apply_fpt_of_comm_refl hw i
    (hc _ (by rw [refl_fpt]; exact mem_e1Sub.2 ⟨_, rfl⟩))

theorem frameEncode_frameE_add : ∀ i j : Fin 8, i ≠ j →
    frameEncode (frameE i + frameE j) = 2 ^ (i : ℕ) + 2 ^ (j : ℕ) := by
  decide

theorem frameE_add_apply (i j k : Fin 8) :
    (frameE i + frameE j) k = (if k = i then 1 else 0) + (if k = j then 1 else 0) := rfl

theorem apply_fpt_of_comm_pair {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) {i j : Fin 8}
    (hij : i ≠ j) (hc : w * frameElt (frameE i + frameE j) = frameElt (frameE i + frameE j) * w) :
    w (fpt i) = fpt i ∨ w (fpt i) = zPerm (fpt i) ∨ w (fpt i) = fpt j ∨
      w (fpt i) = zPerm (fpt j) := by
  have hr : frameElt (frameE i + frameE j) (fpt i) = zPerm (fpt i) :=
    fpt_negated _ i (by rw [frameE_add_apply]; simp [hij])
  have h := neg_of_comm hw hc hr
  have hmem := (mem_negSet (rep_frameArr _) (w (fpt i))).2 h
  have h1 := frame_facts.neg2 i i.2 j j.2 (fun h => hij (Fin.ext h))
  rw [← frameEncode_frameE_add i j hij, frameArrs_encode, ← fpt_val, ← fpt_val] at h1
  rw [h1] at hmem
  rcases mem_four_of_mem_mergeSort hmem with h2 | h2 | h2 | h2
  · exact Or.inl (Fin.ext h2)
  · exact Or.inr (Or.inl (Fin.ext (by rw [h2, rep_negArr.apply (fpt i).2])))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h2)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (by rw [h2, rep_negArr.apply (fpt j).2]))))

theorem frameElt_fpt_other {i k j : Fin 8} (hj : j ≠ i) (hk : j ≠ k) :
    frameElt (frameE i + frameE k) (fpt j) = fpt j := by
  rw [frameElt_fpt, ite_eq_right (by rw [frameE_add_apply]; simp [hj, hk])]

theorem frameElt_zPerm (v : FrameVec) (r : Fin 240) :
    frameElt v (zPerm r) = zPerm (frameElt v r) := by
  rw [← Equiv.Perm.mul_apply, zPerm_comm _ (frameElt_mem_wE8 v), Equiv.Perm.mul_apply]

theorem ne_add_one_two : ∀ i : Fin 8, i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by decide

theorem pair_mem_e1PlusSub {i j : Fin 8} (hij : i ≠ j) :
    frameElt (frameE i + frameE j) ∈ e1PlusSub :=
  mem_e1PlusSub.2 ⟨_, vec2_mem_evenSub i j hij, rfl⟩

theorem centralizer_e1PlusSub {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hc : ∀ e ∈ e1PlusSub, w * e = e * w) : w ∈ e1Sub := by
  refine mem_e1Sub_of_fpt hw fun i => ?_
  obtain ⟨h1, h2, h3⟩ := ne_add_one_two i
  have hneg : frameElt (frameE i + frameE (i + 2)) (w (fpt i)) =
      zPerm (w (fpt i)) := neg_of_comm hw (hc _ (pair_mem_e1PlusSub h2))
    (fpt_negated _ i (by rw [frameE_add_apply]; simp [h2]))
  rcases apply_fpt_of_comm_pair hw h1 (hc _ (pair_mem_e1PlusSub h1)) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h, frameElt_fpt_other (Ne.symm h1) h3] at hneg
    exact zPerm_apply_ne _ hneg.symm
  · exfalso
    rw [h, frameElt_zPerm, frameElt_fpt_other (Ne.symm h1) h3, zPerm_zPerm] at hneg
    exact zPerm_apply_ne _ hneg
