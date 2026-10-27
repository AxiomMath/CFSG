module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrame
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAGLCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylT

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native

theorem frameMaskOf_congr {t u : Array ℕ} (h : eqA 240 t u = true) :
    frameMaskOf t = frameMaskOf u := by
  have hk : ∀ i ∈ List.range 8, t[keyPts.getD i 0]! = u[keyPts.getD i 0]! := by
    intro i hi
    have hlt : keyPts.getD i 0 < 240 := by
      rw [List.mem_range] at hi
      interval_cases i <;> decide
    have := allLt_spec h hlt
    rwa [beq_iff_eq] at this
  unfold frameMaskOf
  congr 2
  apply List.filter_congr
  intro i hi
  rw [hk i hi]

theorem memE1_of_mem {t : Array ℕ} {X : Equiv.Perm (Fin 240)} (ht : Rep 240 t X)
    (hX : X ∈ e1Sub) : memE1 frameArrs t = true := by
  obtain ⟨v, rfl⟩ := mem_e1Sub.1 hX
  have he : eqA 240 t frameArrs[frameEncode v]! = true := by
    rw [frameArrs_encode]
    exact (eqA_iff ht (rep_frameArr v)).2 rfl
  rw [memE1, frameMaskOf_congr he, frame_facts.mask _ (frameEncode_lt v)]
  exact he

theorem frame16_facts :
    (∀ r < 240, memE1 frameArrs reflArrs[r]! = true →
      ∃ i < 8, r = keyPts.getD i 0 ∨ r = negArr[keyPts.getD i 0]!) ∧
    (∀ i < 8, ∀ j < 8, i ≠ j →
      keyPts.getD i 0 ≠ keyPts.getD j 0 ∧ keyPts.getD i 0 ≠ negArr[keyPts.getD j 0]!) := by
  have h := frame16_check
  simp only [frame16Check, frame16CheckWith, Bool.and_eq_true, allLt_iff] at h
  refine ⟨fun r hr hm => ?_, fun i hi j hj hij => ?_⟩
  · have := h.1 r hr
    rw [hm, Bool.not_true, Bool.false_or, List.any_eq_true] at this
    obtain ⟨i, hi, he⟩ := this
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at he
    exact ⟨i, List.mem_range.1 hi, he⟩
  · have := h.2 i hi j hj
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.resolve_left hij

theorem eq_fpt_of_refl_mem {r : Fin 240} (h : refl r ∈ e1Sub) :
    ∃ i, r = fpt i ∨ r = zPerm (fpt i) := by
  have hm := memE1_of_mem (rep_refl r.2) h
  rw [← reflArrs_get r.2] at hm
  obtain ⟨i, hi, he⟩ := frame16_facts.1 r r.2 hm
  refine ⟨⟨i, hi⟩, ?_⟩
  rcases he with he | he
  · exact Or.inl (Fin.ext (by rw [he, fpt_val]))
  · refine Or.inr (Fin.ext ?_)
    rw [he, ← rep_negArr (fpt ⟨i, hi⟩), fpt_val]

theorem fpt_ne {i j : Fin 8} (hij : i ≠ j) : fpt i ≠ fpt j ∧ fpt i ≠ zPerm (fpt j) := by
  obtain ⟨h1, h2⟩ := frame16_facts.2 i i.2 j j.2 (fun h => hij (Fin.ext h))
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [← fpt_val, ← fpt_val, h]
  · rw [← fpt_val, ← fpt_val, h, rep_negArr.apply (fpt j).2]

theorem fpt_injective : Function.Injective fpt := fun i j h => by
  by_contra hij
  exact (fpt_ne hij).1 h

theorem refl_zPerm (r : Fin 240) : refl (zPerm r) = refl r := by
  have h := refl_facts.neg r r.2
  have e : ((zPerm r : Fin 240) : ℕ) = negArr[(r : ℕ)]! := (rep_negArr r).symm
  rw [e]
  exact eq_of_eqA (rep_refl (refl_facts.neg_lt r r.2)) (rep_refl r.2) h

theorem blockVec_empty : blockVec (∅ : Finset (Fin 8)) = 0 := by
  funext i
  simp [blockVec]

theorem blockVec_insert {a : Fin 8} {s : Finset (Fin 8)} (ha : a ∉ s) :
    blockVec (insert a s) = frameE a + blockVec s := by
  funext j
  simp only [blockVec, frameE, Finset.mem_insert, Pi.add_apply]
  by_cases hj : j = a
  · subst hj
    simp [ha]
  · simp [hj]

theorem conj_frameElt_of_lines {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (σ : Equiv.Perm (Fin 8)) (h : ∀ i, w (fpt i) = fpt (σ i) ∨ w (fpt i) = zPerm (fpt (σ i)))
    (v : FrameVec) : w * frameElt v * w⁻¹ = frameElt (permVec σ v) := by
  have hbasis : ∀ i, w * frameElt (frameE i) * w⁻¹ = frameElt (permVec σ (frameE i)) := by
    intro i
    rw [← refl_fpt, refl_conj hw, permVec_frameE, ← refl_fpt]
    rcases h i with h1 | h1
    · rw [h1]
    · rw [h1, refl_zPerm]
  rw [← blockVec_frameSupp v]
  induction frameSupp v using Finset.induction_on with
  | empty =>
    rw [blockVec_empty, frameElt_zero, mul_one, mul_inv_cancel,
      show permVec σ 0 = 0 from funext fun _ => rfl, frameElt_zero]
  | insert a s ha ih =>
    rw [blockVec_insert ha, frameElt_add, permVec_add, frameElt_add, ← hbasis a, ← ih]
    group

theorem exists_line {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hn : w ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240)))) (i : Fin 8) :
    ∃ k, w (fpt i) = fpt k ∨ w (fpt i) = zPerm (fpt k) := by
  apply eq_fpt_of_refl_mem
  rw [← refl_conj hw]
  have hmem : refl (fpt i) ∈ e1Sub := by
    rw [refl_fpt]
    exact mem_e1Sub.2 ⟨_, rfl⟩
  exact (mem_normalizer_iff.1 hn _).1 hmem

theorem card_fixedPoints_conj (g x : Equiv.Perm (Fin 240)) :
    Fintype.card (Function.fixedPoints (g * x * g⁻¹)) = Fintype.card (Function.fixedPoints x) := by
  refine Fintype.card_congr
    { toFun := fun y => ⟨g⁻¹ y.1, ?_⟩
      invFun := fun y => ⟨g y.1, ?_⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have h := y.2
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Equiv.Perm.mul_apply] at h ⊢
    have := congrArg (⇑g⁻¹) h
    simpa using this
  · have h := y.2
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Equiv.Perm.mul_apply] at h ⊢
    simp [h]

theorem blockVec_injective : Function.Injective blockVec := fun s t h => by
  ext i
  have := congrFun h i
  simp only [blockVec] at this
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

theorem frameWt_blockVec (s : Finset (Fin 8)) : frameWt (blockVec s) = s.card := by
  rw [frameWt]
  congr 1
  ext i
  simp [frameSupp, blockVec]

theorem frameBlocks_card : ∀ B ∈ frameBlocks, B.card = 4 := by decide +kernel

theorem frameBlocks_plane : ∀ B ∈ frameBlocks, frameIsPlane (frameEncode (blockVec B)) = true := by
  decide +kernel

theorem mem_frameBlocks_of_fix {s : Finset (Fin 8)} (hs : s.card = 4)
    (h : Fintype.card (Function.fixedPoints (frameElt (blockVec s))) = 24) : s ∈ frameBlocks := by
  have hm := frameEncode_lt (blockVec s)
  have hpop : framePop (frameEncode (blockVec s)) = 4 := by
    rw [← frameWt_eq, frameWt_blockVec, hs]
  have hfix : fixCount 240 frameArrs[frameEncode (blockVec s)]! = 24 := by
    rw [frameArrs_encode, ← card_fixedPoints_of_rep (rep_frameArr _)]
    exact h
  have hp := (frame_facts.plane _ hm hpop).1 hfix
  have hc : frameClass (frameEncode (blockVec s)) = 4 := by
    rw [frameClass, ite_eq_right (by omega), ite_eq_left hpop, ite_eq_left hp]
  obtain ⟨B, hB, he⟩ := (frameClass_eq_four _ hm).1 hc
  rw [frameDecode_frameEncode] at he
  rwa [blockVec_injective he]

theorem fix_frameBlocks {B : Finset (Fin 8)} (hB : B ∈ frameBlocks) :
    Fintype.card (Function.fixedPoints (frameElt (blockVec B))) = 24 := by
  have hm := frameEncode_lt (blockVec B)
  have hpop : framePop (frameEncode (blockVec B)) = 4 := by
    rw [← frameWt_eq, frameWt_blockVec, frameBlocks_card B hB]
  have h := (frame_facts.plane _ hm hpop).2 (frameBlocks_plane B hB)
  rw [frameArrs_encode, ← card_fixedPoints_of_rep (rep_frameArr _)] at h
  exact h

theorem mem_frameAut_of_lines {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) (σ : Equiv.Perm (Fin 8))
    (h : ∀ i, w (fpt i) = fpt (σ i) ∨ w (fpt i) = zPerm (fpt (σ i))) : σ ∈ frameAut := by
  intro B hB
  have hc := conj_frameElt_of_lines hw σ h (blockVec B)
  rw [permVec_blockVec] at hc
  rw [Finset.map_eq_image, Equiv.coe_toEmbedding]
  refine mem_frameBlocks_of_fix ?_ ?_
  · rw [Finset.card_image_of_injective _ σ.injective, frameBlocks_card B hB]
  · change Fintype.card (Function.fixedPoints (frameElt (blockVec (B.image σ)))) = 24
    rw [← hc, card_fixedPoints_conj]
    exact fix_frameBlocks hB

theorem apply_zPerm_of_mem {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) (r : Fin 240) :
    w (zPerm r) = zPerm (w r) := by
  rw [← Equiv.Perm.mul_apply, zPerm_comm w hw, Equiv.Perm.mul_apply]

theorem exists_linePerm {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (h : ∀ i, ∃ k, w (fpt i) = fpt k ∨ w (fpt i) = zPerm (fpt k)) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i, w (fpt i) = fpt (σ i) ∨ w (fpt i) = zPerm (fpt (σ i)) := by
  choose f hf using h
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hi := hf i
    have hj := hf j
    rw [hij] at hi
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hne (fpt_injective (w.injective (hi.trans hj.symm)))
    · refine (fpt_ne hne).2 (w.injective ?_)
      rw [hi, apply_zPerm_of_mem hw, hj, zPerm_zPerm]
    · refine (fpt_ne (Ne.symm hne)).2 (w.injective ?_)
      rw [hj, apply_zPerm_of_mem hw, hi, zPerm_zPerm]
    · exact hne (fpt_injective (w.injective (hi.trans hj.symm)))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem normalizer_e1Sub_action {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hn : w ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240)))) :
    ∃ σ ∈ frameAut, ∀ v, w * frameElt v * w⁻¹ = frameElt (permVec σ v) := by
  obtain ⟨σ, hσ⟩ := exists_linePerm hw (exists_line hw hn)
  exact ⟨σ, mem_frameAut_of_lines hw σ hσ, conj_frameElt_of_lines hw σ hσ⟩

@[expose] def frameAutSub : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := frameAut
  mul_mem' {σ τ} hσ hτ B hB := by
    have := hσ _ (hτ B hB)
    rwa [Finset.map_map] at this
  one_mem' B hB := by
    rw [show (1 : Equiv.Perm (Fin 8)).toEmbedding = Function.Embedding.refl _ from rfl,
      Finset.map_refl]
    exact hB
  inv_mem' {σ} hσ B hB := by
    obtain ⟨C, hC, hCB⟩ := Finset.surjOn_of_injOn_of_card_le
      (fun C : Finset (Fin 8) => C.map σ.toEmbedding) (fun C hC => hσ C hC)
      (fun C _ D _ h => Finset.map_injective σ.toEmbedding h) le_rfl hB
    rw [← hCB, Finset.map_map,
      show σ.toEmbedding.trans σ⁻¹.toEmbedding = Function.Embedding.refl _ from
        Function.Embedding.ext fun x => by simp, Finset.map_refl]
    exact hC

theorem fix_of_block {ρ : Equiv.Perm (Fin 8)} (hρ : ρ ∈ frameAut) {a b c d : Fin 8}
    (hB : ({a, b, c, d} : Finset (Fin 8)) ∈ frameBlocks) (ha : ρ a = a) (hb : ρ b = b)
    (hc : ρ c = c)
    (huniq : ∀ C ∈ frameBlocks, a ∈ C → b ∈ C → c ∈ C → C = {a, b, c, d})
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) : ρ d = d := by
  set B : Finset (Fin 8) := {a, b, c, d}
  have hC := hρ B hB
  have hmem : ∀ x ∈ B, ρ x ∈ B.map ρ.toEmbedding := fun x hx => Finset.mem_map_of_mem _ hx
  have hCB : B.map ρ.toEmbedding = B := huniq _ hC
    (by rw [← ha]; exact hmem a (by simp [B])) (by rw [← hb]; exact hmem b (by simp [B]))
    (by rw [← hc]; exact hmem c (by simp [B]))
  have hd := hmem d (by simp [B])
  rw [hCB] at hd
  simp only [B, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h | h | h
  · exact absurd (ρ.injective (h.trans ha.symm)) hda
  · exact absurd (ρ.injective (h.trans hb.symm)) hdb
  · exact absurd (ρ.injective (h.trans hc.symm)) hdc
  · exact h

theorem block_uniq_012 : ∀ C ∈ frameBlocks, (0 : Fin 8) ∈ C → (1 : Fin 8) ∈ C → (2 : Fin 8) ∈ C →
    C = {0, 1, 2, 3} := by decide +kernel

theorem block_uniq_014 : ∀ C ∈ frameBlocks, (0 : Fin 8) ∈ C → (1 : Fin 8) ∈ C → (4 : Fin 8) ∈ C →
    C = {0, 1, 4, 5} := by decide +kernel

theorem block_uniq_024 : ∀ C ∈ frameBlocks, (0 : Fin 8) ∈ C → (2 : Fin 8) ∈ C → (4 : Fin 8) ∈ C →
    C = {0, 2, 4, 6} := by decide +kernel

theorem block_uniq_016 : ∀ C ∈ frameBlocks, (0 : Fin 8) ∈ C → (1 : Fin 8) ∈ C → (6 : Fin 8) ∈ C →
    C = {0, 1, 6, 7} := by decide +kernel

theorem eq_one_of_fix_frame {ρ : Equiv.Perm (Fin 8)} (hρ : ρ ∈ frameAut) (h0 : ρ 0 = 0)
    (h1 : ρ 1 = 1) (h2 : ρ 2 = 2) (h4 : ρ 4 = 4) : ρ = 1 := by
  have h3 : ρ 3 = 3 := fix_of_block hρ (by decide +kernel) h0 h1 h2 block_uniq_012
    (by decide) (by decide) (by decide)
  have h5 : ρ 5 = 5 := fix_of_block hρ (by decide +kernel) h0 h1 h4 block_uniq_014
    (by decide) (by decide) (by decide)
  have h6 : ρ 6 = 6 := fix_of_block hρ (by decide +kernel) h0 h2 h4 block_uniq_024
    (by decide) (by decide) (by decide)
  have h7 : ρ 7 = 7 := fix_of_block hρ (by decide +kernel) h0 h1 h6 block_uniq_016
    (by decide) (by decide) (by decide)
  ext x
  fin_cases x <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]

theorem planeThrough_spec : ∀ a b c d : Fin 8, (planeThrough a b c).testBit d = true →
    ∃ B ∈ frameBlocks, a ∈ B ∧ b ∈ B ∧ c ∈ B ∧ d ∈ B := by decide +kernel

theorem no_block_0124 : ∀ B ∈ frameBlocks, ¬ ((0 : Fin 8) ∈ B ∧ (1 : Fin 8) ∈ B ∧
    (2 : Fin 8) ∈ B ∧ (4 : Fin 8) ∈ B) := by decide +kernel

theorem closure_frameGens_le : closure frameGens ≤ frameAutSub := by
  rw [closure_le]
  exact frameGens_subset_frameAut

@[expose] def IsAffFrame (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.1 ∧
    (planeThrough t.1 t.2.1 t.2.2.1).testBit t.2.2.2 = false

instance : DecidablePred IsAffFrame := fun t => by
  unfold IsAffFrame
  infer_instance

theorem frame_tuple {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ frameAutSub) :
    IsAffFrame (σ 0, σ 1, σ 2, σ 4) := by
  refine ⟨fun h => by simpa using σ.injective h, fun h => by simpa using σ.injective h,
    fun h => by simpa using σ.injective h, ?_⟩
  by_contra hb
  rw [Bool.not_eq_false] at hb
  obtain ⟨B, hB, h0, h1, h2, h4⟩ := planeThrough_spec _ _ _ _ hb
  have hinv := (frameAutSub.inv_mem hσ) B hB
  apply no_block_0124 _ hinv
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  exact ⟨⟨_, h0, by simp⟩, ⟨_, h1, by simp⟩, ⟨_, h2, by simp⟩, ⟨_, h4, by simp⟩⟩

theorem eq_of_frame_tuple {σ τ : Equiv.Perm (Fin 8)} (hσ : σ ∈ frameAutSub)
    (hτ : τ ∈ frameAutSub) (h0 : τ 0 = σ 0) (h1 : τ 1 = σ 1) (h2 : τ 2 = σ 2) (h4 : τ 4 = σ 4) :
    σ = τ := by
  have hρ : τ⁻¹ * σ = 1 := by
    apply eq_one_of_fix_frame (frameAutSub.mul_mem (frameAutSub.inv_mem hτ) hσ)
    all_goals rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exacts [h0.symm, h1.symm, h2.symm, h4.symm]
  rw [← mul_inv_cancel_left τ σ, hρ, mul_one]

theorem frameAutSub_eq : frameAutSub = closure frameGens := by
  refine le_antisymm (fun σ hσ => ?_) closure_frameGens_le
  obtain ⟨h01, h02, h12, hpl⟩ := frame_tuple hσ
  obtain ⟨τ, hτ, h0, h1, h2, h4⟩ := agl_frames _ _ _ _ h01 h02 h12 hpl
  rw [eq_of_frame_tuple hσ (closure_frameGens_le hτ) h0 h1 h2 h4]
  exact hτ

theorem card_frameAutSub : Nat.card frameAutSub = 1344 := by
  let φ : frameAutSub → {t // IsAffFrame t} := fun σ =>
    ⟨(σ.1 0, σ.1 1, σ.1 2, σ.1 4), frame_tuple σ.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun σ τ h => ?_, fun t => ?_⟩
    · simp only [φ, Subtype.mk.injEq, Prod.mk.injEq] at h
      exact Subtype.ext (eq_of_frame_tuple σ.2 τ.2 h.1.symm h.2.1.symm h.2.2.1.symm h.2.2.2.symm)
    · obtain ⟨⟨a, b, d, e⟩, h01, h02, h12, hpl⟩ := t
      obtain ⟨τ, hτ, h0, h1, h2, h4⟩ := agl_frames a b d e h01 h02 h12 hpl
      exact ⟨⟨τ, closure_frameGens_le hτ⟩, by simp [φ, h0, h1, h2, h4]⟩
  rw [Nat.card_eq_of_bijective φ hφ, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

@[expose] def frameRealizedW : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∃ w ∈ wPlus, ∀ v, w * frameElt v * w⁻¹ = frameElt (permVec σ v)}
  mul_mem' := by
    rintro σ τ ⟨w, hw, h⟩ ⟨u, hu, h'⟩
    refine ⟨w * u, mul_mem hw hu, fun v => ?_⟩
    rw [permVec_mul, ← h, ← h']
    group
  one_mem' := ⟨1, one_mem _, fun v => by rw [one_mul, inv_one, mul_one, permVec_one]⟩
  inv_mem' := by
    rintro σ ⟨w, hw, h⟩
    refine ⟨w⁻¹, inv_mem hw, fun v => ?_⟩
    have := h (permVec σ⁻¹ v)
    rw [permVec_permVec_inv] at this
    rw [← this]
    group

theorem singer_facts : Rep 240 singerArr (permOfArr 240 singerArr) ∧
    permOfArr 240 singerArr ∈ wE8 ∧ isId (powArr' singerArr 7) = true ∧
    (∀ i < 8, singerArr[keyPts.getD i 0]! = keyPts.getD (singerList.getD i 0) 0) ∧
    ∀ i < 8, (signArrs[5]!)[keyPts.getD i 0]! =
      if i < 4 then negArr[keyPts.getD (flipList.getD i 0) 0]! else keyPts.getD i 0 := by
  have h := singer_check
  rw [singerCheck] at h
  obtain ⟨h, h5⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h4⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h3⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  rw [allLt_iff] at h4 h5
  refine ⟨(rep_permOfArr h1).1, mem_wE8_of_siftW (rep_permOfArr h1).1 h2, h3,
    fun i hi => by simpa using h4 i hi, fun i hi => by simpa using h5 i hi⟩

theorem rep_powArr' {x : Array ℕ} {X : Equiv.Perm (Fin 240)} (hx : Rep 240 x X) :
    ∀ k, Rep 240 (powArr' x k) (X ^ k)
  | 0 => by rw [powArr', pow_zero]; exact rep_idA
  | k + 1 => by rw [powArr', pow_succ']; exact rep_compA hx (rep_powArr' hx k)

theorem singer_list_eq : ∀ i : Fin 8, (singerList.getD i 0 : ℕ) = (frameSinger i : ℕ) := by decide

theorem flip_list_eq : ∀ i : Fin 8, (flipList.getD i 0 : ℕ) = (frameFlip i : ℕ) := by decide

theorem frameSinger_mem_realized : frameSinger ∈ frameRealizedW := by
  obtain ⟨hrep, hmem, hpow, himg, -⟩ := singer_facts
  set w := permOfArr 240 singerArr
  have h7 : w ^ 7 = 1 := (isId_iff (rep_powArr' hrep 7)).1 hpow
  have hsign : Equiv.Perm.sign w = 1 := by
    have := congrArg Equiv.Perm.sign h7
    rw [map_pow, map_one] at this
    rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h
    · exact h
    · rw [h] at this; exact absurd this (by decide)
  refine ⟨w, mem_wPlus_iff.2 ⟨hmem, hsign⟩, conj_frameElt_of_lines hmem frameSinger fun i => ?_⟩
  left
  apply Fin.ext
  rw [← hrep.apply (fpt i).2, fpt_val, himg i i.2, singer_list_eq i, ← fpt_val]

theorem frameDecode_five : frameDecode 5 = vec2 0 2 := by decide

theorem frameFlip_fix : ∀ i : Fin 8, ¬ (i : ℕ) < 4 → frameFlip i = i := by decide

theorem frameFlip_mem_realized : frameFlip ∈ frameRealizedW := by
  obtain ⟨-, -, -, -, himg⟩ := singer_facts
  have hv : frameDecode 5 ∈ evenSub := by
    rw [frameDecode_five]; exact vec2_mem_evenSub 0 2 (by decide)
  have hrep := rep_signArr hv
  rw [← signArrs_get (by norm_num : 5 < 256)] at hrep
  refine ⟨signPerm (frameDecode 5), signPerm_mem_wPlus hv,
    conj_frameElt_of_lines (wPlus_le (signPerm_mem_wPlus hv)) frameFlip fun i => ?_⟩
  have h := himg i i.2
  rw [← fpt_val, hrep.apply (fpt i).2] at h
  by_cases hi : (i : ℕ) < 4
  · right
    rw [ite_eq_left hi] at h
    apply Fin.ext
    rw [h, flip_list_eq i, ← fpt_val, ← rep_negArr (fpt _)]
  · left
    rw [ite_eq_right hi] at h
    apply Fin.ext
    rw [h, frameFlip_fix i hi]
