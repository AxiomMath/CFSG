module

public import CFSG.LocalAnalysis.OddStandard.ONanSylowPres
public import CFSG.LocalAnalysis.OddStandard.ChengHeldON
public import Certificates.Data.ONanF2Img
import CFSG.Sporadic.ON

public section

namespace CFSG.OddStandard.ONanRec

open CFSG.OddStandard.ChengHeld.ONSylow CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.Sporadic.Recognition.PresentedWords CFSG.CosetTable CFSG.Blueprint F2

theorem alpImgOK_eq_true : alpImgOK = true := by decide +kernel

noncomputable def alpPerm (i : Fin 5) : Equiv.Perm (Fin 32) := permOfArr 32 alpImgs[i.val]!

structure AlpImgParts : Prop where
  inv : ∀ i < 5, isInvL alpImgs[i]!.toList alpInvs[i]!.toList = true
  rels : ∀ w ∈ alpRels, alpWordL w = List.range 32
  gens : ∀ j < 6, alpWordL alpGenWords[j]! = CFSG.ONSchreier.Data.T32Chain.generators[j]!.toList
  zne : ∃ x < 32, (alpWordL [(0, true), (0, true), (2, true), (2, true)]).getD x 0 ≠ x

theorem alpImgParts (h : alpImgOK = true) : AlpImgParts := by
  simp only [alpImgOK, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, List.any_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, x, hx, h4⟩ := h
  exact ⟨h1, fun w hw => by simpa using h2 w hw, h3, x, hx, h4⟩

theorem lrep_alpPerm (hp : AlpImgParts) (i : Fin 5) :
    LRep 32 alpImgs[i.val]!.toList (alpPerm i) ∧ LRep 32 alpInvs[i.val]!.toList (alpPerm i)⁻¹ := by
  have h := hp.inv i.val i.2
  have hl := h
  simp only [isInvL, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨hl1, hl2⟩, -⟩ := hl
  obtain ⟨p1, p2⟩ := prep_permOfArr (pisInv_of_isInvL h)
  exact ⟨lrep_of_prep p1 hl1, lrep_of_prep p2 hl2⟩

theorem lrep_alpLetL (hp : AlpImgParts) (l : Fin 5 × Bool) :
    LRep 32 (alpLetL l) (if l.2 then alpPerm l.1 else (alpPerm l.1)⁻¹) := by
  obtain ⟨h1, h2⟩ := lrep_alpPerm hp l.1
  by_cases hb : l.2
  · simpa [alpLetL, hb] using h1
  · simpa [alpLetL, hb] using h2

theorem lrep_alp_foldl (hp : AlpImgParts) (w : List (Fin 5 × Bool)) :
    ∀ (acc : List ℕ) (g : Equiv.Perm (Fin 32)), LRep 32 acc g →
      LRep 32 (w.foldl (fun acc l => compL acc (alpLetL l)) acc) (g * wprod alpPerm w) := by
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, wprod_cons, ← mul_assoc]
    exact ih _ _ (hg.comp (lrep_alpLetL hp l))

theorem lrep_alpWordL (hp : AlpImgParts) (w : List (Fin 5 × Bool)) :
    LRep 32 (alpWordL w) (wprod alpPerm w) := by
  have h := lrep_alp_foldl hp w (List.range 32) 1 (lrep_one 32)
  rw [one_mul] at h
  exact h

theorem exists_alpPerm :
    AlpFrame (alpPerm 0) (alpPerm 1) (alpPerm 2) (alpPerm 3) (alpPerm 4) ∧
      onT32Chain.originalSubgroup ≤ Subgroup.closure (Set.range alpPerm) ∧
      alpPerm 0 ^ 2 * alpPerm 2 ^ 2 ≠ 1 := by
  have hp := alpImgParts alpImgOK_eq_true
  refine ⟨?_, ?_, ?_⟩
  · refine frame_of_wprod_alpRels (fun w hw => ?_)
    have h1 := lrep_alpWordL hp w
    rw [hp.rels w hw] at h1
    have h2 : (![alpPerm 0, alpPerm 1, alpPerm 2, alpPerm 3, alpPerm 4] : Fin 5 → _) = alpPerm := by
      funext i
      fin_cases i <;> rfl
    rw [h2]
    exact h1.unique (lrep_one 32)
  · rw [onT32_sub, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    dsimp only
    have h1 := lrep_alpWordL hp alpGenWords[j]!
    rw [hp.gens j hj] at h1
    rw [permOfArr_eq_of_prep (prep_of_lrep h1)]
    have hmem : ∀ i, alpPerm i ∈ Subgroup.closure (Set.range alpPerm) := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    clear h1
    induction alpGenWords[j]! with
    | nil => exact one_mem _
    | cons l w ih =>
      rw [wprod_cons]
      refine mul_mem ?_ ih
      split
      · exact hmem _
      · exact inv_mem (hmem _)
  · intro h
    obtain ⟨x, hx, hne⟩ := hp.zne
    have h1 := lrep_alpWordL hp [(0, true), (0, true), (2, true), (2, true)]
    have h2 : wprod alpPerm [(0, true), (0, true), (2, true), (2, true)] = 1 := by
      simp only [wprod, List.map, List.prod_cons, List.prod_nil, mul_one, ite_true]
      rw [pow_two, pow_two] at h
      simpa [mul_assoc] using h
    rw [h2] at h1
    have h3 := prep_of_lrep (t := (alpWordL [(0, true), (0, true), (2, true), (2, true)]).toArray)
      (by simpa using h1)
    have h4 := h3.apply hx
    rw [← getD_toList, List.toList_toArray] at h4
    exact hne (by simpa using h4)

theorem exists_equivAlpE_t32
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) :
    Nonempty (AlpE ≃* onT32Chain.originalSubgroup) := by
  obtain ⟨hfr, hle, hz⟩ := exists_alpPerm
  have hinj : Function.Injective (hfr.toG h) := hfr.toG_injective h hz
  have hset : ({alpPerm 0, alpPerm 1, alpPerm 2, alpPerm 3, alpPerm 4} :
      Set (Equiv.Perm (Fin 32))) = Set.range alpPerm := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hrange : (hfr.toG h).range = Subgroup.closure (Set.range alpPerm) := by
    rw [hfr.range_toG h, alpP, hset]
  have hcard : Nat.card (hfr.toG h).range = 512 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, AlpE.card]
  have hQ : Nat.card onT32Chain.originalSubgroup = 512 := card_onT32
  have hQle : onT32Chain.originalSubgroup ≤ (hfr.toG h).range := by
    rw [hrange]
    exact hle
  have heq : onT32Chain.originalSubgroup = (hfr.toG h).range :=
    Subgroup.eq_of_le_of_card_ge hQle (by rw [hcard, hQ])
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr heq.symm)⟩

theorem exists_mulEquiv_alpE
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512)
    {G : Type} [Group G] (S : Sylow 2 G) (T : Sylow 2 NativeSporadic.ON)
    (e : (S : Subgroup G) ≃* (T : Subgroup NativeSporadic.ON)) :
    Nonempty (AlpE ≃* (S : Subgroup G)) := by
  obtain ⟨R, ⟨e3⟩⟩ := exists_sylow_onT32Chain
  obtain ⟨θ0⟩ := exists_equivAlpE_t32 h
  have : Finite NativeSporadic.ON := (CFSG.Sporadic.ON.fam_on_simplicity).1
  exact ⟨θ0.trans (e3.trans ((Sylow.equiv R T).trans e.symm))⟩

theorem stageA5_ON
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) :
    StageA5 NativeSporadic.ON := by
  intro G _ _ S T e
  obtain ⟨e'⟩ := e
  obtain ⟨θ⟩ := exists_mulEquiv_alpE h S T e'
  let f : AlpE →* G := (S : Subgroup G).subtype.comp θ.toMonoidHom
  have hf : Function.Injective f := (S : Subgroup G).subtype_injective.comp θ.injective
  refine ⟨f (AlpE.gen 0), f (AlpE.gen 1), f (AlpE.gen 2), f (AlpE.gen 3), f (AlpE.gen 4),
    frame_gen.map f, ?_, ?_⟩
  · unfold alpP
    have hset : ({f (AlpE.gen 0), f (AlpE.gen 1), f (AlpE.gen 2), f (AlpE.gen 3),
        f (AlpE.gen 4)} : Set G) = f '' Set.range AlpE.gen := by
      ext g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_range]
      constructor
      · rintro (rfl | rfl | rfl | rfl | rfl)
        exacts [⟨_, ⟨0, rfl⟩, rfl⟩, ⟨_, ⟨1, rfl⟩, rfl⟩, ⟨_, ⟨2, rfl⟩, rfl⟩, ⟨_, ⟨3, rfl⟩, rfl⟩,
          ⟨_, ⟨4, rfl⟩, rfl⟩]
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        fin_cases i <;> simp
    rw [hset, ← MonoidHom.map_closure, AlpE.closure_range_gen, ← MonoidHom.range_eq_map]
    ext g
    simp only [MonoidHom.mem_range, f, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, rfl⟩
      exact (θ x).2
    · intro hg
      obtain ⟨x, hx⟩ := θ.surjective ⟨g, hg⟩
      exact ⟨x, by rw [hx]⟩
  · have hz2 : orderOf AlpE.zc = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · decide +kernel
      · decide +kernel
    rw [← map_pow, ← map_pow, ← map_mul]
    change orderOf (f AlpE.zc) = 2
    rw [orderOf_injective f hf]
    exact hz2

end CFSG.OddStandard.ONanRec
