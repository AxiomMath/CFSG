module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowCheck

public section

namespace CFSG.ComponentClassification.AS81.Q47

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow
open scoped Pointwise

@[expose] def ptSet (W : Array ℕ) : Set (Fin 64) := {v | v.val ∈ W.toList}

theorem contains_iff' {W : Array ℕ} {a : ℕ} : W.contains a = true ↔ a ∈ W.toList := by
  rw [Array.contains_iff_mem, Array.mem_def]

theorem eightCheck_parts {W : Array ℕ} (h : eightCheck W = true) :
    W.size = 8 ∧ (∀ a ∈ W.toList, a < 64) ∧ W.toList.Nodup := by
  simp only [eightCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem ncard_ptSet {W : Array ℕ} (h : eightCheck W = true) : (ptSet W).ncard = 8 := by
  obtain ⟨hs, hlt, hnd⟩ := eightCheck_parts h
  let l : List (Fin 64) := W.toList.pmap (fun a ha => ⟨a, ha⟩) hlt
  have hl : ptSet W = (l.toFinset : Set (Fin 64)) := by
    ext v
    simp only [ptSet, Set.mem_ofPred_eq, List.coe_toFinset, l, List.mem_pmap]
    constructor
    · intro hv
      exact ⟨v.val, hv, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  have hnd' : l.Nodup := List.Nodup.pmap (fun a _ b _ e => congrArg Fin.val e) hnd
  rw [hl, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', List.length_pmap,
    Array.length_toList, hs]

theorem image_subset_of_mapsInto {t A B : Array ℕ} {π : Equiv.Perm (Fin 64)} (ht : Rep 64 t π)
    (h : mapsInto t A B = true) : π '' ptSet A ⊆ ptSet B := by
  rintro _ ⟨v, hv, rfl⟩
  have := List.all_eq_true.1 h v.val hv
  rw [contains_iff', ht.apply v.2] at this
  exact this

theorem memTab_get {B : Array ℕ} {v : ℕ} (hv : v < 64) : (memTab B)[v]! = B.contains v := by
  rw [memTab, getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn]

theorem image_subset_of_mapsIntoM {t A B : Array ℕ} {π : Equiv.Perm (Fin 64)} (ht : Rep 64 t π)
    (h : mapsIntoM t A (memTab B) = true) : π '' ptSet A ⊆ ptSet B := by
  rintro _ ⟨v, hv, rfl⟩
  have := List.all_eq_true.1 h v.val hv
  rw [ht.apply v.2, memTab_get (π v).2, contains_iff'] at this
  exact this

theorem image_eq_of_subset {A B : Array ℕ} (hA : eightCheck A = true) (hB : eightCheck B = true)
    {π : Equiv.Perm (Fin 64)} (h : π '' ptSet A ⊆ ptSet B) : π '' ptSet A = ptSet B := by
  refine Set.eq_of_subset_of_ncard_le h ?_ (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ π.injective, ncard_ptSet hA, ncard_ptSet hB]

theorem sameSet_iff {A B : Array ℕ} (h : sameSet A B = true) : ptSet A = ptSet B := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true] at h
  ext v
  constructor
  · intro hv
    exact contains_iff'.1 (h.1 _ hv)
  · intro hv
    exact contains_iff'.1 (h.2 _ hv)

theorem tsCheck_parts {W : Array ℕ} (h : tsCheck W = true) :
    eightCheck W = true ∧ W[0]! = 0 ∧ (∀ a ∈ W.toList, ∀ b ∈ W.toList, a ^^^ b ∈ W.toList) ∧
      ∀ a ∈ W.toList, q47Form[a]! = 0 := by
  simp only [tsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, fun a ha b hb => contains_iff'.1 (h.1.2 a ha b hb), h.2⟩

theorem getElem!_mem_toList' {W : Array ℕ} {i : ℕ} (hi : i < W.size) : W[i]! ∈ W.toList := by
  rw [getElem!_pos W i hi]
  exact Array.getElem_mem_toList hi

structure TSub (W : Array ℕ) : Prop where
  eight : eightCheck W = true
  zero : (0 : Fin 64) ∈ ptSet W
  xr_mem : ∀ u ∈ ptSet W, ∀ v ∈ ptSet W, xr u v ∈ ptSet W
  sing : ∀ v ∈ ptSet W, qv v = 0
  one_mem : W[1]! ∈ W.toList
  one_ne : W[1]! ≠ 0

theorem tSub_of_tsCheck {W : Array ℕ} (h : tsCheck W = true) : TSub W := by
  obtain ⟨he, h0, hx, hq⟩ := tsCheck_parts h
  obtain ⟨hs, hlt, hnd⟩ := eightCheck_parts he
  have h0m : W[0]! ∈ W.toList := getElem!_mem_toList' (by omega)
  have h1m : W[1]! ∈ W.toList := getElem!_mem_toList' (by omega)
  refine ⟨he, ?_, fun u hu v hv => hx _ hu _ hv, fun v hv => hq _ hv, h1m, ?_⟩
  · show (0 : ℕ) ∈ W.toList
    rw [← h0]
    exact h0m
  · intro h1
    have e : W.toList[0]'(by simp [hs]) = W.toList[1]'(by simp [hs]) := by
      rw [Array.getElem_toList, Array.getElem_toList, ← getElem!_pos W 0 (by omega),
        ← getElem!_pos W 1 (by omega), h0, h1]
    have := (List.Nodup.getElem_inj_iff hnd).1 e
    omega

noncomputable abbrev ystar : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 q47YGens
noncomputable abbrev nstar : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 q47NGens
abbrev wOne : Set (Fin 64) := ptSet q47W1
abbrev wTwo : Set (Fin 64) := ptSet q47W2

theorem refCheck_parts (h : refCheck = true) :
    enumCheckN 64 q47YGens 168 = true ∧ q47YGens.all isomCheck = true ∧ tsCheck q47W1 = true ∧
    tsCheck q47W2 = true ∧ q47W1.toList.all (fun a => a == 0 || !(q47W2.contains a)) = true ∧
    q47YGens.all (fun y => mapsInto y q47W1 q47W1 && mapsInto y q47W2 q47W2) = true ∧
    transCheck (eltsN 64 q47YGens) q47W1 = true ∧ transCheck (eltsN 64 q47YGens) q47W2 = true ∧
    q47L30.length = 30 ∧ q47L30.all eightCheck = true ∧
    oAll.all (fun t => (List.range 30).any (fun j => mapsIntoM t q47W1 l30Tab[j]!) &&
      (List.range 30).any (fun j => mapsIntoM t q47W2 l30Tab[j]!)) = true ∧
    q47OrbRep.length = 4 ∧ q47OrbRep.all eightCheck = true ∧ q47Orb.length = 30 ∧
    (List.range 30).all (fun j =>
      (q47Orb[j]!.1 == 4 && sameSet q47L30[j]! q47W1) ||
        (q47Orb[j]!.1 == 5 && sameSet q47L30[j]! q47W2) ||
        (decide (q47Orb[j]!.1 < 4) && decide (q47Orb[j]!.2 < 168) &&
          mapsInto (eltsN 64 q47YGens)[q47Orb[j]!.2]! q47OrbRep[q47Orb[j]!.1]! q47L30[j]!)) =
      true ∧
    q47G1.length = 4 ∧ q47G2.length = 4 ∧ q47G1.all isomCheck = true ∧
    q47G2.all isomCheck = true ∧
    (List.range 4).all (fun k =>
      mapsInto q47G1[k]! q47W1 q47OrbRep[k]! && mapsInto q47G2[k]! q47W2 q47OrbRep[k]!) = true ∧
    stabCheck oAll q47W1 q47U1Gens = true ∧ stabCheck oAll q47W2 q47U2Gens = true ∧
    q47Wit.length = 64 ∧ witsCheck = true ∧ enumCheckN 64 q47NGens 336 = true ∧
    q47NGens.all isomCheck = true ∧ q47YGens.all (inLN 64 (eltsN 64 q47NGens)) = true ∧
    q47NGens.all swapCheck = true ∧ (oAll.filter swapCheck).length = 336 := by
  simp only [refCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

@[expose] def setStab (S : Set (Fin 64)) : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {π | π '' S = S}
  mul_mem' {π σ} hπ hσ := by
    change (π * σ) '' S = S
    rw [Equiv.Perm.coe_mul, Set.image_comp, hσ, hπ]
  one_mem' := by
    change (1 : Equiv.Perm (Fin 64)) '' S = S
    rw [Equiv.Perm.coe_one, Set.image_id]
  inv_mem' {π} hπ := by
    change ⇑(π⁻¹) '' S = S
    have e : ⇑(π⁻¹) '' (⇑π '' S) = S := by
      rw [← Set.image_comp, ← Equiv.Perm.coe_mul, inv_mul_cancel, Equiv.Perm.coe_one,
        Set.image_id]
    rw [hπ] at e
    exact e

theorem mem_setStab {S : Set (Fin 64)} {π : Equiv.Perm (Fin 64)} : π ∈ setStab S ↔ π '' S = S :=
  Iff.rfl

theorem grpN_le_setStab {gs : List (Array ℕ)} {m : ℕ} (hg : enumCheckN 64 gs m = true)
    {A : Array ℕ} (hA : eightCheck A = true) (h : ∀ g ∈ gs, mapsInto g A A = true) :
    grpN 64 gs ≤ setStab (ptSet A) :=
  grpN_le fun g hgs => image_eq_of_subset hA hA
    (image_subset_of_mapsInto (rep_of_validA (validA_of_mem hg hgs)) (h g hgs))

section Ref

variable (hq : refCheck = true)
include hq

theorem ystar_le_oV : ystar ≤ oV := by
  obtain ⟨-, hY, -⟩ := refCheck_parts hq
  exact grpN_le fun g hg => mem_oV_of_isomCheck (List.all_eq_true.1 hY g hg)

theorem card_ystar : Nat.card ystar = 168 := card_grpN (refCheck_parts hq).1

theorem nstar_le_oV : nstar ≤ oV := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hN, -⟩ :=
    refCheck_parts hq
  exact grpN_le fun g hg => mem_oV_of_isomCheck (List.all_eq_true.1 hN g hg)

theorem card_nstar : Nat.card nstar = 336 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    refCheck_parts hq
  exact card_grpN h

theorem tSub_wOne : TSub q47W1 := tSub_of_tsCheck (refCheck_parts hq).2.2.1

theorem tSub_wTwo : TSub q47W2 := tSub_of_tsCheck (refCheck_parts hq).2.2.2.1

theorem eq_zero_of_mem_both {v : Fin 64} (h1 : v ∈ wOne) (h2 : v ∈ wTwo) : v = 0 := by
  obtain ⟨-, -, -, -, h, -⟩ := refCheck_parts hq
  have := List.all_eq_true.1 h v.val h1
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  rcases this with h0 | hc
  · exact Fin.ext h0
  · rw [contains_iff'.2 h2] at hc
    exact absurd hc (by decide)

theorem ystar_le_setStab : ystar ≤ setStab wOne ⊓ setStab wTwo := by
  obtain ⟨hY, -, -, -, -, hm, -⟩ := refCheck_parts hq
  refine le_inf (grpN_le_setStab hY (tSub_wOne hq).eight fun g hg => ?_)
    (grpN_le_setStab hY (tSub_wTwo hq).eight fun g hg => ?_)
  · exact (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hm g hg).1
  · exact (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hm g hg).2

theorem exists_ystar_wOne {w : Fin 64} (hw : w ∈ wOne) (hw0 : w ≠ 0) :
    ∃ y ∈ ystar, y ⟨q47W1[1]!, (eightCheck_parts (tSub_wOne hq).eight).2.1 _
      (tSub_wOne hq).one_mem⟩ = w := by
  obtain ⟨hY, -, -, -, -, -, ht, -⟩ := refCheck_parts hq
  have := List.all_eq_true.1 ht w.val hw
  rw [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
  rcases this with h0 | ⟨y, hy, he⟩
  · exact absurd (Fin.ext h0) hw0
  · have hry := rep_of_validA (validA_of_mem_elts hY hy)
    refine ⟨permOfArr 64 y, (mem_grpN_iff hY).2 ⟨y, hy, hry⟩, Fin.ext ?_⟩
    rw [beq_iff_eq] at he
    rw [← hry.apply, he]

theorem exists_ystar_wTwo {w : Fin 64} (hw : w ∈ wTwo) (hw0 : w ≠ 0) :
    ∃ y ∈ ystar, y ⟨q47W2[1]!, (eightCheck_parts (tSub_wTwo hq).eight).2.1 _
      (tSub_wTwo hq).one_mem⟩ = w := by
  obtain ⟨hY, -, -, -, -, -, -, ht, -⟩ := refCheck_parts hq
  have := List.all_eq_true.1 ht w.val hw
  rw [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
  rcases this with h0 | ⟨y, hy, he⟩
  · exact absurd (Fin.ext h0) hw0
  · have hry := rep_of_validA (validA_of_mem_elts hY hy)
    refine ⟨permOfArr 64 y, (mem_grpN_iff hY).2 ⟨y, hy, hry⟩, Fin.ext ?_⟩
    rw [beq_iff_eq] at he
    rw [← hry.apply, he]

end Ref

theorem mem_permsA_iff {n : ℕ} {gs : List (Array ℕ)} {x : Equiv.Perm (Fin n)} :
    x ∈ permsA n gs.toArray ↔ ∃ g ∈ gs, permOfArr n g = x := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk0 : k < gs.toArray.size := hk
    have hk' : k < gs.length := by simpa using hk0
    refine ⟨gs[k], List.getElem_mem hk', ?_⟩
    show permOfArr n gs[k] = permOfArr n gs.toArray[k]!
    rw [getElem!_pos gs.toArray k hk0, List.getElem_toArray]
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have hk0 : k < gs.toArray.size := by simpa using hk
    refine ⟨k, hk0, ?_⟩
    show permOfArr n gs.toArray[k]! = permOfArr n gs[k]
    rw [getElem!_pos gs.toArray k hk0, List.getElem_toArray]

theorem grpN_append (n : ℕ) (gs hs : List (Array ℕ)) :
    grpN n (gs ++ hs) = grpN n gs ⊔ grpN n hs := by
  rw [grpN, grpN, grpN, ← Subgroup.closure_union]
  congr 1
  ext x
  rw [Set.mem_union, mem_permsA_iff, mem_permsA_iff, mem_permsA_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases List.mem_append.1 hg with h | h
    · exact Or.inl ⟨g, h, rfl⟩
    · exact Or.inr ⟨g, h, rfl⟩
  · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
    · exact ⟨g, List.mem_append_left _ hg, rfl⟩
    · exact ⟨g, List.mem_append_right _ hg, rfl⟩

theorem rep_evalWord {K : Subgroup (Equiv.Perm (Fin 64))} {gs : List (Array ℕ)}
    (hgs : ∀ g ∈ gs, ∃ x ∈ K, Rep 64 g x) (w : List ℕ)
    (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) : ∃ x ∈ K, Rep 64 (evalWord gs w) x := by
  induction w with
  | nil => exact ⟨1, one_mem _, rep_idA⟩
  | cons l w ih =>
    obtain ⟨x, hx, hrx⟩ := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hl := hw l List.mem_cons_self
    have hmem : gs[l - 1]! ∈ gs := by
      rw [getElem!_pos gs (l - 1) (by omega)]
      exact List.getElem_mem _
    obtain ⟨y, hy, hry⟩ := hgs _ hmem
    refine ⟨y * x, mul_mem hy hx, ?_⟩
    have e : evalWord gs (l :: w) = compA 64 gs[l - 1]! (evalWord gs w) := by
      simp only [evalWord, List.foldr_cons]
    rw [e]
    exact rep_compA hry hrx

theorem image_inv_eq {π : Equiv.Perm (Fin 64)} {A B : Set (Fin 64)} (h : π '' A = B) :
    ⇑(π⁻¹) '' B = A := by
  rw [← h, ← Set.image_comp, ← Equiv.Perm.coe_mul, inv_mul_cancel, Equiv.Perm.coe_one,
    Set.image_id]

@[expose] def PairPres (π : Equiv.Perm (Fin 64)) : Prop :=
  (π '' wOne = wOne ∧ π '' wTwo = wTwo) ∨ (π '' wOne = wTwo ∧ π '' wTwo = wOne)

@[expose] def pairStab : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {π | PairPres π}
  mul_mem' {π σ} hπ hσ := by
    change PairPres (π * σ)
    simp only [PairPres, Equiv.Perm.coe_mul, Set.image_comp] at hπ hσ ⊢
    rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hπ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp only [h1, h2, h3, h4, and_self, true_or, or_true]
  one_mem' := Or.inl ⟨by simp, by simp⟩
  inv_mem' {π} hπ := by
    change PairPres π⁻¹
    rcases hπ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨image_inv_eq h1, image_inv_eq h2⟩
    · exact Or.inr ⟨image_inv_eq h2, image_inv_eq h1⟩

theorem mapsIntoM_of_image {t A B : Array ℕ} {π : Equiv.Perm (Fin 64)} (ht : Rep 64 t π)
    (hA : eightCheck A = true) (h : π '' ptSet A ⊆ ptSet B) : mapsIntoM t A (memTab B) = true := by
  refine List.all_eq_true.2 fun a ha => ?_
  have hlt : a < 64 := (eightCheck_parts hA).2.1 a ha
  have hmem : π ⟨a, hlt⟩ ∈ ptSet B := h ⟨⟨a, hlt⟩, ha, rfl⟩
  rw [ht.apply hlt, memTab_get (π ⟨a, hlt⟩).2, contains_iff']
  exact hmem

theorem swapCheck_iff {t : Array ℕ} {π : Equiv.Perm (Fin 64)} (ht : Rep 64 t π)
    (h1 : eightCheck q47W1 = true) (h2 : eightCheck q47W2 = true) :
    swapCheck t = true ↔ PairPres π := by
  constructor
  · intro h
    simp only [swapCheck, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨image_eq_of_subset h1 h1 (image_subset_of_mapsIntoM ht h3),
        image_eq_of_subset h2 h2 (image_subset_of_mapsIntoM ht h4)⟩
    · exact Or.inr ⟨image_eq_of_subset h1 h2 (image_subset_of_mapsIntoM ht h3),
        image_eq_of_subset h2 h1 (image_subset_of_mapsIntoM ht h4)⟩
  · intro h
    simp only [swapCheck, Bool.or_eq_true, Bool.and_eq_true]
    rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨mapsIntoM_of_image ht h1 h3.le, mapsIntoM_of_image ht h2 h4.le⟩
    · exact Or.inr ⟨mapsIntoM_of_image ht h1 h3.le, mapsIntoM_of_image ht h2 h4.le⟩

theorem stabCheck_parts {W : Array ℕ} {U : List (Array ℕ)} (h : stabCheck oAll W U = true) :
    enumCheckN 64 U 8 = true ∧ U.all isomCheck = true ∧
    enumCheckN 64 (U ++ q47YGens) 1344 = true ∧
    (U ++ q47YGens).all (fun t => mapsInto t W W) = true ∧
    (oAll.filter fun t => mapsIntoM t W (memTab W)).length = 1344 ∧
    q47YGens.all (fun y => U.all fun u => inLN 64 (eltsN 64 U) (conjA 64 y u)) = true := by
  simp only [stabCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem exists_index_of_mem {gs : List (Array ℕ)} {m : ℕ} (hg : enumCheckN 64 gs m = true)
    {x : Equiv.Perm (Fin 64)} (hx : x ∈ grpN 64 gs) :
    ∃ j < m, x = permOfArr 64 (eltsN 64 gs)[j]! := by
  obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff hg).1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  have hlen : (eltsN 64 gs).length = m := by
    simp only [enumCheckN, Bool.and_eq_true, beq_iff_eq] at hg
    simpa [eltsN] using hg.2
  refine ⟨j, hlen ▸ hj, ?_⟩
  rw [getElem!_pos (eltsN 64 gs) j hj]
  exact (permOfArr_eq_of_rep hrt).symm

section Over

variable (hT : transCheckO = true) (hq : refCheck = true)
include hT hq

theorem exists_mul_of_stab {W : Array ℕ} {U : List (Array ℕ)} (hW : eightCheck W = true)
    (hs : stabCheck oAll W U = true) {π : Equiv.Perm (Fin 64)} (hπ : π ∈ oV)
    (hπW : π '' ptSet W = ptSet W) : ∃ u ∈ grpN 64 U, ∃ y ∈ ystar, π = u * y := by
  obtain ⟨hU, hUi, hK, hKW, hcount, hnorm⟩ := stabCheck_parts hs
  obtain ⟨hY, hYi, -⟩ := refCheck_parts hq
  set K := grpN 64 (U ++ q47YGens) with hKdef
  have hKO : K ≤ oV := grpN_le fun g hg => by
    rcases List.mem_append.1 hg with h | h
    · exact mem_oV_of_isomCheck (List.all_eq_true.1 hUi g h)
    · exact mem_oV_of_isomCheck (List.all_eq_true.1 hYi g h)
  have hKs : K ≤ setStab (ptSet W) :=
    grpN_le_setStab hK hW fun g hg => List.all_eq_true.1 hKW g hg
  let S : Set (Equiv.Perm (Fin 64)) := {σ | σ ∈ oV ∧ σ '' ptSet W = ptSet W}
  have hS : Nat.card S ≤ 1344 := by
    rw [← hcount]
    refine card_le_length fun σ hσ => ?_
    obtain ⟨t, ht, hrt⟩ := exists_mem_oAll hT hσ.1
    exact ⟨t, List.mem_filter.2 ⟨ht, mapsIntoM_of_image hrt hW hσ.2.le⟩, hrt⟩
  have hKS : (K : Set (Equiv.Perm (Fin 64))) = S := by
    refine Set.eq_of_subset_of_ncard_le (fun σ hσ => ⟨hKO hσ, hKs hσ⟩) ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card S ≤ Nat.card K
    rw [card_grpN hK]
    exact hS
  have hπK : π ∈ K := by
    have : π ∈ S := ⟨hπ, hπW⟩
    rw [← hKS] at this
    exact this
  have hN : ystar ≤ normalizer (grpN 64 U : Set (Equiv.Perm (Fin 64))) :=
    le_normalizer_of_all hU (fun g hg => validA_of_mem hY hg) hnorm
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right ystar (grpN 64 U) hN
  have hKsup : K = ystar ⊔ grpN 64 U := by
    rw [hKdef, grpN_append, sup_comm]
  have hπi : π⁻¹ ∈ ((ystar ⊔ grpN 64 U : Subgroup (Equiv.Perm (Fin 64))) :
      Set (Equiv.Perm (Fin 64))) := by
    rw [← hKsup]
    exact inv_mem hπK
  rw [hcoe] at hπi
  obtain ⟨y, hy, u, hu, e⟩ := hπi
  refine ⟨u⁻¹, inv_mem hu, y⁻¹, inv_mem hy, ?_⟩
  have e' : y * u = π⁻¹ := e
  rw [← mul_inv_rev, e', inv_inv]

theorem exists_l30 {π : Equiv.Perm (Fin 64)} (hπ : π ∈ oV) :
    (∃ j < 30, π '' wOne = ptSet q47L30[j]!) ∧ ∃ j < 30, π '' wTwo = ptSet q47L30[j]! := by
  obtain ⟨-, -, hts1, hts2, -, -, -, -, hlen, h8, hall, -⟩ := refCheck_parts hq
  obtain ⟨t, ht, hrt⟩ := exists_mem_oAll hT hπ
  have hb := List.all_eq_true.1 hall t ht
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range] at hb
  obtain ⟨⟨j, hj, hm⟩, ⟨j', hj', hm'⟩⟩ := hb
  have hL : ∀ i < 30, l30Tab[i]! = memTab q47L30[i]! ∧ eightCheck q47L30[i]! = true := by
    intro i hi
    refine ⟨?_, List.all_eq_true.1 h8 _ (by
      rw [getElem!_pos q47L30 i (by omega)]
      exact List.getElem_mem _)⟩
    rw [l30Tab, getElem!_pos _ i (by simp [hlen]; omega), Array.getElem_map,
      getElem!_pos q47L30 i (by omega)]
    simp
  have e1 := (hL j hj).1
  have e2 := (hL j' hj').1
  rw [e1] at hm
  rw [e2] at hm'
  exact ⟨⟨j, hj, image_eq_of_subset (tsCheck_parts hts1).1 (hL j hj).2
      (image_subset_of_mapsIntoM hrt hm)⟩,
    ⟨j', hj', image_eq_of_subset (tsCheck_parts hts2).1 (hL j' hj').2
      (image_subset_of_mapsIntoM hrt hm')⟩⟩

omit hT in
theorem orb_data {j : ℕ} (hj : j < 30) :
    ptSet q47L30[j]! = wOne ∨ ptSet q47L30[j]! = wTwo ∨
      ∃ k < 4, ∃ y ∈ ystar, y '' ptSet q47OrbRep[k]! = ptSet q47L30[j]! := by
  obtain ⟨hY, -, -, -, -, -, -, -, hlen, h8, -, hrl, hr8, -, hall, -⟩ := refCheck_parts hq
  have hb := List.all_eq_true.1 hall j (List.mem_range.2 hj)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  rcases hb with (⟨-, h1⟩ | ⟨-, h2⟩) | ⟨⟨hk, hi⟩, hm⟩
  · exact Or.inl (sameSet_iff h1)
  · exact Or.inr (Or.inl (sameSet_iff h2))
  · right; right
    set k := q47Orb[j]!.1
    set i := q47Orb[j]!.2
    have hlenY : (eltsN 64 q47YGens).length = 168 := by
      simp only [enumCheckN, Bool.and_eq_true, beq_iff_eq] at hY
      simpa [eltsN] using hY.2
    have hmem : (eltsN 64 q47YGens)[i]! ∈ eltsN 64 q47YGens := by
      rw [getElem!_pos _ i (by omega)]
      exact List.getElem_mem _
    have hry := rep_of_validA (validA_of_mem_elts hY hmem)
    have hOk : eightCheck q47OrbRep[k]! = true := List.all_eq_true.1 hr8 _ (by
      rw [getElem!_pos q47OrbRep k (by omega)]
      exact List.getElem_mem _)
    have hLj : eightCheck q47L30[j]! = true := List.all_eq_true.1 h8 _ (by
      rw [getElem!_pos q47L30 j (by omega)]
      exact List.getElem_mem _)
    exact ⟨k, hk, _, (mem_grpN_iff hY).2 ⟨_, hmem, hry⟩,
      image_eq_of_subset hOk hLj (image_subset_of_mapsInto hry hm)⟩

omit hT in
theorem g_data {k : ℕ} (hk : k < 4) :
    (permOfArr 64 q47G1[k]! ∈ oV ∧ ⇑(permOfArr 64 q47G1[k]!) '' wOne = ptSet q47OrbRep[k]!) ∧
      permOfArr 64 q47G2[k]! ∈ oV ∧ ⇑(permOfArr 64 q47G2[k]!) '' wTwo = ptSet q47OrbRep[k]! := by
  obtain ⟨-, -, hts1, hts2, -, -, -, -, -, -, -, hrl, hr8, -, -, hl1, hl2, hi1, hi2, hm, -⟩ :=
    refCheck_parts hq
  have hb := List.all_eq_true.1 hm k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at hb
  have hm1 : q47G1[k]! ∈ q47G1 := by
    rw [getElem!_pos q47G1 k (by omega)]
    exact List.getElem_mem _
  have hm2 : q47G2[k]! ∈ q47G2 := by
    rw [getElem!_pos q47G2 k (by omega)]
    exact List.getElem_mem _
  have hc1 := List.all_eq_true.1 hi1 _ hm1
  have hc2 := List.all_eq_true.1 hi2 _ hm2
  have hOk : eightCheck q47OrbRep[k]! = true := List.all_eq_true.1 hr8 _ (by
    rw [getElem!_pos q47OrbRep k (by omega)]
    exact List.getElem_mem _)
  have r1 := rep_of_validA (isomCheck_parts hc1).1
  have r2 := rep_of_validA (isomCheck_parts hc2).1
  exact ⟨⟨mem_oV_of_isomCheck hc1, image_eq_of_subset (tsCheck_parts hts1).1 hOk
      (image_subset_of_mapsInto r1 hb.1)⟩, mem_oV_of_isomCheck hc2,
    image_eq_of_subset (tsCheck_parts hts2).1 hOk (image_subset_of_mapsInto r2 hb.2)⟩

theorem mem_nstar_of_pairPres {π : Equiv.Perm (Fin 64)} (hπ : π ∈ oV) (hp : PairPres π) :
    π ∈ nstar := by
  obtain ⟨-, -, hts1, hts2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hN, hNi,
    -, hNs, hcount⟩ := refCheck_parts hq
  have h1 := (tsCheck_parts hts1).1
  have h2 := (tsCheck_parts hts2).1
  let S : Set (Equiv.Perm (Fin 64)) := {σ | σ ∈ oV ∧ PairPres σ}
  have hS : Nat.card S ≤ 336 := by
    rw [← hcount]
    refine card_le_length fun σ hσ => ?_
    obtain ⟨t, ht, hrt⟩ := exists_mem_oAll hT hσ.1
    exact ⟨t, List.mem_filter.2 ⟨ht, (swapCheck_iff hrt h1 h2).2 hσ.2⟩, hrt⟩
  have hNS : (nstar : Set (Equiv.Perm (Fin 64))) = S := by
    refine Set.eq_of_subset_of_ncard_le (fun σ hσ => ⟨nstar_le_oV hq hσ, ?_⟩) ?_
      (Set.toFinite _)
    · have hle : nstar ≤ pairStab := grpN_le fun g hg =>
        (swapCheck_iff (rep_of_validA (validA_of_mem hN hg)) h1 h2).1
          (List.all_eq_true.1 hNs g hg)
      exact hle hσ
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      change Nat.card S ≤ Nat.card nstar
      rw [card_nstar hq]
      exact hS
  have : π ∈ S := ⟨hπ, hp⟩
  rw [← hNS] at this
  exact this

end Over

theorem length_q47YGens : q47YGens.length = 2 := rfl

theorem dvd_of_witCheck {g u : Array ℕ} {ws : List (List ℕ)}
    (hY : enumCheckN 64 q47YGens 168 = true)
    (hw : witCheck (compA 64 g u) ws = true) {H : Subgroup (Equiv.Perm (Fin 64))}
    (hYH : ystar ≤ H) {x : Equiv.Perm (Fin 64)} (hrx : Rep 64 (compA 64 g u) x) (hx : x ∈ H) :
    32 ∣ Nat.card H := by
  simp only [witCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hlet, hP⟩ := hw
  have hgens : ∀ a ∈ q47YGens ++ [compA 64 g u], ∃ y ∈ H, Rep 64 a y := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact ⟨_, hYH (gen_mem_grpN ha), rep_of_validA (validA_of_mem hY ha)⟩
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨x, hx, hrx⟩
  have hle : grpN 64 (ws.map (evalWord (q47YGens ++ [compA 64 g u]))) ≤ H := by
    refine grpN_le fun a ha => ?_
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, hry⟩ := rep_evalWord hgens w (fun l hl => by
      have := hlet w hw' l hl
      rw [List.length_append, List.length_singleton, length_q47YGens]
      omega)
    rw [permOfArr_eq_of_rep hry]
    exact hy
  rw [← card_grpN hP]
  exact Subgroup.card_dvd_of_le hle

theorem witsCheck_parts (h : witsCheck = true) :
    (∀ k < 4, ∀ j < 8,
      witCheck (compA 64 q47G1[k]! (eltsN 64 q47U1Gens)[j]!) q47Wit[k * 8 + j]! = true) ∧
    ∀ k < 4, ∀ j < 8,
      witCheck (compA 64 q47G2[k]! (eltsN 64 q47U2Gens)[j]!) q47Wit[(4 + k) * 8 + j]! = true := by
  have h' := h
  unfold witsCheck at h'
  rw [List.all_eq_true] at h'
  refine ⟨fun k hk j hj => ?_, fun k hk j hj => ?_⟩
  · have := List.all_eq_true.1 (List.all_eq_true.1 (h' 0 (by simp)) k (List.mem_range.2 hk)) j
      (List.mem_range.2 hj)
    simpa using this
  · have := List.all_eq_true.1 (List.all_eq_true.1 (h' 1 (by simp)) k (List.mem_range.2 hk)) j
      (List.mem_range.2 hj)
    simpa using this

section Over2

variable (hT : transCheckO = true) (hq : refCheck = true)
include hT hq

theorem image_mem_of_side {Wa : Array ℕ} {G U : List (Array ℕ)} {off : ℕ}
    (hW8 : eightCheck Wa = true) (hst : stabCheck oAll Wa U = true)
    (hG : ∀ k < 4, permOfArr 64 G[k]! ∈ oV ∧
      ⇑(permOfArr 64 G[k]!) '' ptSet Wa = ptSet q47OrbRep[k]!)
    (hGi : ∀ k < 4, validA 64 G[k]! = true)
    (hwit : ∀ k < 4, ∀ j < 8,
      witCheck (compA 64 G[k]! (eltsN 64 U)[j]!) q47Wit[(off + k) * 8 + j]! = true)
    {H : Subgroup (Equiv.Perm (Fin 64))} (hHO : H ≤ oV) (hYH : ystar ≤ H)
    (h32 : ¬ 32 ∣ Nat.card H) {h : Equiv.Perm (Fin 64)} (hh : h ∈ H)
    (hl : ∃ j < 30, h '' ptSet Wa = ptSet q47L30[j]!) :
    h '' ptSet Wa = wOne ∨ h '' ptSet Wa = wTwo := by
  obtain ⟨hY, -⟩ := refCheck_parts hq
  obtain ⟨j, hj, hjW⟩ := hl
  rcases orb_data hq hj with e | e | ⟨k, hk, y, hy, hyk⟩
  · exact Or.inl (hjW.trans e)
  · exact Or.inr (hjW.trans e)
  · exfalso
    obtain ⟨hgO, hg⟩ := hG k hk
    set g := permOfArr 64 G[k]! with hgdef
    have hσ : ⇑(g⁻¹ * y⁻¹ * h) '' ptSet Wa = ptSet Wa := by
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, hjW, ← hyk,
        image_inv_eq rfl, image_inv_eq hg]
    have hσO : g⁻¹ * y⁻¹ * h ∈ oV :=
      oV.mul_mem (oV.mul_mem (oV.inv_mem hgO) (oV.inv_mem (ystar_le_oV hq hy))) (hHO hh)
    obtain ⟨u, hu, y', hy', e⟩ := exists_mul_of_stab hT hq hW8 hst hσO hσ
    obtain ⟨j', hj', rfl⟩ := exists_index_of_mem (stabCheck_parts hst).1 hu
    have hgu : g * permOfArr 64 (eltsN 64 U)[j']! = y⁻¹ * h * y'⁻¹ := by
      calc g * permOfArr 64 (eltsN 64 U)[j']!
          = g * (permOfArr 64 (eltsN 64 U)[j']! * y') * y'⁻¹ := by group
        _ = g * (g⁻¹ * y⁻¹ * h) * y'⁻¹ := by rw [← e]
        _ = y⁻¹ * h * y'⁻¹ := by group
    have hx : g * permOfArr 64 (eltsN 64 U)[j']! ∈ H := by
      rw [hgu]
      exact H.mul_mem (H.mul_mem (H.inv_mem (hYH hy)) hh) (H.inv_mem (hYH hy'))
    have hmem : (eltsN 64 U)[j']! ∈ eltsN 64 U := by
      have hlen : (eltsN 64 U).length = 8 := by
        have := (stabCheck_parts hst).1
        simp only [enumCheckN, Bool.and_eq_true, beq_iff_eq] at this
        simpa [eltsN] using this.2
      rw [getElem!_pos _ j' (by omega)]
      exact List.getElem_mem _
    have hru := rep_of_validA (validA_of_mem_elts (stabCheck_parts hst).1 hmem)
    exact h32 (dvd_of_witCheck hY (hwit k hk j' hj') hYH
      (rep_compA (rep_of_validA (hGi k hk)) hru) hx)

theorem le_nstar_of_le {H : Subgroup (Equiv.Perm (Fin 64))} (hHO : H ≤ oV) (hYH : ystar ≤ H)
    (h32 : ¬ 32 ∣ Nat.card H) : H ≤ nstar := by
  obtain ⟨-, -, hts1, hts2, -, -, -, -, -, -, -, -, -, -, -, hl1, hl2, hi1, hi2, -, hst1, hst2,
    -, hw, -⟩ := refCheck_parts hq
  obtain ⟨hw1, hw2⟩ := witsCheck_parts hw
  have h81 := (tsCheck_parts hts1).1
  have h82 := (tsCheck_parts hts2).1
  have hGi1 : ∀ k < 4, validA 64 q47G1[k]! = true := fun k hk =>
    (isomCheck_parts (List.all_eq_true.1 hi1 _ (by
      rw [getElem!_pos q47G1 k (by omega)]
      exact List.getElem_mem _))).1
  have hGi2 : ∀ k < 4, validA 64 q47G2[k]! = true := fun k hk =>
    (isomCheck_parts (List.all_eq_true.1 hi2 _ (by
      rw [getElem!_pos q47G2 k (by omega)]
      exact List.getElem_mem _))).1
  intro h hh
  have hhO := hHO hh
  have hl := exists_l30 hT hq hhO
  have hA := image_mem_of_side hT hq (off := 0) h81 hst1 (fun k hk => (g_data hq hk).1) hGi1
    (fun k hk j hj => by simpa using hw1 k hk j hj) hHO hYH h32 hh hl.1
  have hB := image_mem_of_side hT hq (off := 4) h82 hst2 (fun k hk => (g_data hq hk).2) hGi2
    hw2 hHO hYH h32 hh hl.2
  have hne : wOne ≠ wTwo := by
    intro e
    have h1 := (tSub_wOne hq).one_mem
    have hlt := (eightCheck_parts h81).2.1 _ h1
    have hm1 : (⟨q47W1[1]!, hlt⟩ : Fin 64) ∈ wOne := h1
    have hm2 : (⟨q47W1[1]!, hlt⟩ : Fin 64) ∈ wTwo := e ▸ hm1
    exact (tSub_wOne hq).one_ne (congrArg Fin.val (eq_zero_of_mem_both hq hm1 hm2))
  have hinj : ∀ {A B : Set (Fin 64)}, h '' A = h '' B → A = B := fun e =>
    Set.image_injective.2 h.injective e
  refine mem_nstar_of_pairPres hT hq hhO ?_
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hinj (hA.trans hB.symm)) hne
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr ⟨hA, hB⟩
  · exact absurd (hinj (hA.trans hB.symm)) hne

end Over2

end CFSG.ComponentClassification.AS81.Q47
