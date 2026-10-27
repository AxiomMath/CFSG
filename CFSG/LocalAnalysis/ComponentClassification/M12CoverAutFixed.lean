module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedCheck
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import Certificates.Certificate11003

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem pair_getD_mem (k : ℕ) :
    ([m12gA, m12gB].getD k 1, [m12gA, m12bp].getD k 1) ∈ m12Pairs := by
  rcases k with _ | _ | k
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · have h1 : [m12gA, m12gB].getD (k + 2) 1 = 1 := by simp
    have h2 : [m12gA, m12bp].getD (k + 2) 1 = 1 := by simp
    rw [h1, h2]
    exact m12Pairs.one_mem

theorem pairEval_mem (w : List ℤ) :
    (evalCodes [m12gA, m12gB] w, evalCodes [m12gA, m12bp] w) ∈ m12Pairs := by
  induction w with
  | nil => exact m12Pairs.one_mem
  | cons z w ih =>
    simp only [evalCodes]
    split_ifs
    · exact m12Pairs.mul_mem (pair_getD_mem _) ih
    · exact m12Pairs.mul_mem (m12Pairs.inv_mem (pair_getD_mem _)) ih

theorem pairs_of_word {g : Equiv.Perm (Fin 12)} (w : List ℤ)
    (h1 : evalCodes [m12gA, m12gB] w = g) (h2 : evalCodes [m12gA, m12bp] w = g) :
    (g, g) ∈ m12Pairs := by
  have := pairEval_mem w
  rwa [h1, h2] at this

theorem pairs_permX : (permX, permX) ∈ m12Pairs :=
  pairs_of_word wordX (Certificates.certificate11003.1) (Certificates.certificate11003.2.1)

theorem pairs_permY : (permY, permY) ∈ m12Pairs :=
  pairs_of_word wordY (Certificates.certificate11003.2.2.1) (Certificates.certificate11003.2.2.2.1)

theorem pairs_permZ : (permZ, permZ) ∈ m12Pairs :=
  pairs_of_word wordZ (Certificates.certificate11003.2.2.2.2.1) (Certificates.certificate11003.2.2.2.2.2.1)

@[expose] def elemX : NativeSporadic.M12 := ⟨permX, pairs_fst_mem pairs_permX⟩

@[expose] def elemY : NativeSporadic.M12 := ⟨permY, pairs_fst_mem pairs_permY⟩

@[expose] def elemZ : NativeSporadic.M12 := ⟨permZ, pairs_fst_mem pairs_permZ⟩

theorem elemX_coe : (elemX : Equiv.Perm (Fin 12)) = permX := rfl

theorem elemY_coe : (elemY : Equiv.Perm (Fin 12)) = permY := rfl

theorem elemZ_coe : (elemZ : Equiv.Perm (Fin 12)) = permZ := rfl

theorem permX_apply : ∀ i, permX i = ![0, 3, 8, 6, 10, 1, 11, 2, 4, 9, 7, 5] i :=
  Certificates.certificate11003.2.2.2.2.2.2.1

theorem permY_apply : ∀ i, permY i = ![6, 0, 2, 3, 7, 11, 5, 9, 10, 8, 4, 1] i :=
  Certificates.certificate11003.2.2.2.2.2.2.2.1

theorem permZ_apply : ∀ i, permZ i = ![9, 7, 3, 2, 11, 10, 8, 1, 6, 0, 5, 4] i :=
  Certificates.certificate11003.2.2.2.2.2.2.2.2.1

theorem elemX_mem_fixSub : elemX ∈ fixSub beta := Subtype.ext (beta_apply_of_mem pairs_permX)

theorem elemY_mem_fixSub : elemY ∈ fixSub beta := Subtype.ext (beta_apply_of_mem pairs_permY)

theorem elemZ_mem_fixSub : elemZ ∈ fixSub beta := Subtype.ext (beta_apply_of_mem pairs_permZ)

theorem permZ_sq : permZ ^ 2 = 1 :=
  Certificates.certificate11003.2.2.2.2.2.2.2.2.2.1

theorem orderOf_elemZ : orderOf elemZ = 2 := by
  refine orderOf_eq_prime (Subtype.ext permZ_sq) (fun h => ?_)
  have := congrArg (fun g : NativeSporadic.M12 => (g : Equiv.Perm (Fin 12)) 0) h
  change permZ 0 = (1 : Equiv.Perm (Fin 12)) 0 at this
  exact absurd this (by decide +kernel)

@[expose] def fixedD : Subgroup NativeSporadic.M12 := Subgroup.closure {elemX, elemY}

theorem fixedD_map : fixedD.map NativeSporadic.M12.subtype = fixedDQ.originalSubgroup := by
  rw [fixedD, MonoidHom.map_closure, Set.image_pair, fixedDQ, certificate_originalSubgroup]
  congr 1
  ext g
  simp [elemX, elemY]

theorem mem_fixedD {g : NativeSporadic.M12} :
    g ∈ fixedD ↔ (g : Equiv.Perm (Fin 12)) ∈ fixedDQ.originalSubgroup := by
  rw [← fixedD_map]
  exact (Subgroup.mem_map_iff_mem NativeSporadic.M12.subtype_injective).symm

theorem fixedDQ_check : fixedDQ.check = true ∧ fixedDQ.orderCertificate = 60 := by
  have h := checkChainD_eq
  simp only [checkChainD, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem fixedDQ_valid : ValidSchreier fixedDQ := fixedDQ_check.1

theorem mem_enum_fixedDQ (g : Equiv.Perm (Fin 12)) :
    g ∈ enumeration fixedDQ ↔ g ∈ fixedDQ.originalSubgroup :=
  mem_enumeration_iff fixedDQ fixedDQ_valid g

theorem card_fixedDQ : Nat.card fixedDQ.originalSubgroup = 60 := by
  rw [← fixedDQ.orderCertificate_eq_card fixedDQ_valid, fixedDQ_check.2]

theorem card_fixedD : Nat.card fixedD = 60 := by
  rw [← Subgroup.card_map_of_injective NativeSporadic.M12.subtype_injective, fixedD_map,
    card_fixedDQ]

theorem fixedDQ_le : fixedDQ.originalSubgroup ≤ NativeSporadic.M12 := by
  rw [← fixedD_map]
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem memB_iff {g : Equiv.Perm (Fin 12)} {L : List (Equiv.Perm (Fin 12))} :
    memB g L = true ↔ g ∈ L := by
  simp only [memB, List.any_eq_true, schreierPermEq_eq_true_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · exact fun hg => ⟨g, hg, rfl⟩

theorem peq_false {g h : Equiv.Perm (Fin 12)} (hgh : g ≠ h) : schreierPermEq g h = false :=
  Bool.eq_false_iff.2 fun e => hgh ((schreierPermEq_eq_true_iff _ _).1 e)

theorem peq_true {g h : Equiv.Perm (Fin 12)} (hgh : g = h) : schreierPermEq g h = true :=
  (schreierPermEq_eq_true_iff _ _).2 hgh

theorem sq_eq_one_of_pow_four {g : Equiv.Perm (Fin 12)} (hg : g ∈ fixedDQ.originalSubgroup)
    (h4 : g ^ 4 = 1) : g ^ 2 = 1 := by
  have h := List.all_eq_true.1 checkFour_eq g ((mem_enum_fixedDQ g).2 hg)
  rw [peq_true h4, Bool.not_true, Bool.false_or] at h
  exact (schreierPermEq_eq_true_iff _ _).1 h

theorem exists_conj_permR {g : Equiv.Perm (Fin 12)} (hg : g ∈ fixedDQ.originalSubgroup)
    (h2 : g ^ 2 = 1) (h1 : g ≠ 1) : ∃ c ∈ fixedDQ.originalSubgroup, g = c * permR * c⁻¹ := by
  have h := List.all_eq_true.1 checkInvolutions_eq g ((mem_enum_fixedDQ g).2 hg)
  rw [peq_true h2, peq_false h1, Bool.not_true, Bool.false_or, Bool.false_or,
    List.any_eq_true] at h
  obtain ⟨c, hc, hgc⟩ := h
  exact ⟨c, (mem_enum_fixedDQ c).1 hc, (schreierPermEq_eq_true_iff _ _).1 hgc⟩

theorem conjIndex_mem {g : Equiv.Perm (Fin 12)} (hg : g ∈ fixedDQ.originalSubgroup) (i : Fin 5) :
    g * fourR i * g⁻¹ ∈ fourList (conjIndex g i) ∧
      g * fourS i * g⁻¹ ∈ fourList (conjIndex g i) := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 checkConj_eq g ((mem_enum_fixedDQ g).2 hg)) i
    (List.mem_finRange i)
  rw [Bool.and_eq_true] at h
  exact ⟨memB_iff.1 h.1, memB_iff.1 h.2⟩

theorem eq_one_of_conjIndex {g : Equiv.Perm (Fin 12)} (hg : g ∈ fixedDQ.originalSubgroup)
    (h : ∀ i, conjIndex g i = i) : g = 1 := by
  have h' := List.all_eq_true.1 checkKernel_eq g ((mem_enum_fixedDQ g).2 hg)
  have hall : (List.finRange 5).all (fun i => conjIndex g i == i) = true :=
    List.all_eq_true.2 fun i _ => beq_iff_eq.2 (h i)
  rw [hall, Bool.not_true, Bool.false_or] at h'
  exact (schreierPermEq_eq_true_iff _ _).1 h'

theorem exists_fourList {u v : Equiv.Perm (Fin 12)} (hu : u ∈ fixedDQ.originalSubgroup)
    (hv : v ∈ fixedDQ.originalSubgroup) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) (hc : u * v = v * u) :
    ∃ i, u ∈ fourList i ∧ v ∈ fourList i := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 checkPairs_eq u
    ((mem_enum_fixedDQ u).2 hu)) v ((mem_enum_fixedDQ v).2 hv)
  rw [peq_true hu2, peq_true hv2, peq_false hu1, peq_false hv1, peq_false huv, peq_true hc]
    at h
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨i, -, hi1, hi2⟩ := h
  exact ⟨i, memB_iff.1 hi1, memB_iff.1 hi2⟩

theorem checkCount_spec :
    (involutionsOf (enumeration fixedDQ)).length = 15 ∧
      memB permZ (enumeration fixedDQ) = false := by
  have h := checkCount_eq
  simp only [checkCount, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact h

theorem permZ_not_mem : permZ ∉ fixedDQ.originalSubgroup := by
  intro h
  have := checkCount_spec.2
  rw [memB_iff.2 ((mem_enum_fixedDQ permZ).2 h)] at this
  exact absurd this (by decide)

theorem elemZ_not_mem : elemZ ∉ fixedD := fun h => permZ_not_mem (mem_fixedD.1 h)

@[expose] def fourGroupPerm (i : Fin 5) : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure {fourR i, fourS i}

theorem fourList_mul (i : Fin 5) : ∀ a ∈ fourList i, ∀ b ∈ fourList i, a * b ∈ fourList i :=
  fun a ha b hb => memB_iff.1 (List.all_eq_true.1 (List.all_eq_true.1
    (List.all_eq_true.1 checkFourMul_eq i (List.mem_finRange i)) a ha) b hb)

theorem fourList_inv (i : Fin 5) : ∀ a ∈ fourList i, a⁻¹ ∈ fourList i :=
  fun a ha => memB_iff.1 (List.all_eq_true.1
    (List.all_eq_true.1 checkFourInv_eq i (List.mem_finRange i)) a ha)

theorem fourList_nodup (i : Fin 5) : (fourList i).Nodup :=
  of_decide_eq_true (List.all_eq_true.1 checkFourDistinctEntries_eq i (List.mem_finRange i))

theorem fourList_distinct (i j : Fin 5) (hr : fourR i ∈ fourList j)
    (hs : fourS i ∈ fourList j) : i = j := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 checkFourSeparated_eq i
    (List.mem_finRange i)) j (List.mem_finRange j)
  rw [memB_iff.2 hr, memB_iff.2 hs] at h
  simp only [Bool.and_self, Bool.not_true, Bool.or_false, beq_iff_eq] at h
  exact h.symm

theorem mem_fourGroupPerm {i : Fin 5} {g : Equiv.Perm (Fin 12)} :
    g ∈ fourGroupPerm i ↔ g ∈ fourList i := by
  constructor
  · intro hg
    let K : Subgroup (Equiv.Perm (Fin 12)) :=
      { carrier := {g | g ∈ fourList i}
        one_mem' := by simp [fourList]
        mul_mem' := fun ha hb => fourList_mul i _ ha _ hb
        inv_mem' := fun ha => fourList_inv i _ ha }
    have hK : fourGroupPerm i ≤ K := by
      rw [fourGroupPerm, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · change fourR i ∈ fourList i
        simp [fourList]
      · change fourS i ∈ fourList i
        simp [fourList]
    exact hK hg
  · intro hg
    simp only [fourList, List.mem_cons, List.not_mem_nil, or_false] at hg
    have hr : fourR i ∈ fourGroupPerm i := Subgroup.subset_closure (Set.mem_insert _ _)
    have hs : fourS i ∈ fourGroupPerm i := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rcases hg with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hr
    · exact hs
    · exact mul_mem hr hs

theorem card_fourGroupPerm (i : Fin 5) : Nat.card (fourGroupPerm i) = 4 :=
  card_eq_length (fun g => g ∈ fourGroupPerm i) id Function.injective_id (fourList i)
    (fourList_nodup i) fun g => by simp [mem_fourGroupPerm]

theorem fourGroupPerm_injective : Function.Injective fourGroupPerm := by
  intro i j h
  have hr : fourR i ∈ fourGroupPerm j := h ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hs : fourS i ∈ fourGroupPerm j :=
    h ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact fourList_distinct i j (mem_fourGroupPerm.1 hr) (mem_fourGroupPerm.1 hs)

theorem fourRS_word (i : Fin 5) :
    evalCodes [permX, permY] (fourRWord i) = fourR i ∧
      evalCodes [permX, permY] (fourSWord i) = fourS i := by
  have h := List.all_eq_true.1 checkFourWords_eq i (List.mem_finRange i)
  rw [Bool.and_eq_true, schreierPermEq_eq_true_iff, schreierPermEq_eq_true_iff] at h
  exact h

theorem gens_mem_fixedDQ : ∀ g ∈ [permX, permY], g ∈ fixedDQ.originalSubgroup := by
  intro g hg
  rw [fixedDQ, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem fourGroupPerm_le (i : Fin 5) : fourGroupPerm i ≤ fixedDQ.originalSubgroup := by
  rw [fourGroupPerm, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [← (fourRS_word i).1]
    exact evalCodes_mem _ gens_mem_fixedDQ _
  · rw [← (fourRS_word i).2]
    exact evalCodes_mem _ gens_mem_fixedDQ _

theorem fourGroupPerm_conj {g : Equiv.Perm (Fin 12)} (hg : g ∈ fixedDQ.originalSubgroup)
    (i : Fin 5) :
    (fourGroupPerm i).map (MulAut.conj g).toMonoidHom = fourGroupPerm (conjIndex g i) := by
  obtain ⟨hr, hs⟩ := conjIndex_mem hg i
  apply Subgroup.eq_of_le_of_card_ge
  · rw [fourGroupPerm, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_fourGroupPerm.2 hr
    · exact mem_fourGroupPerm.2 hs
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_fourGroupPerm,
      card_fourGroupPerm]

theorem conjIndex_values (i : Fin 5) : conjIndex 1 i = i ∧
    conjIndex permX i = ![3, 4, 1, 2, 0] i ∧ conjIndex permY i = ![2, 3, 1, 4, 0] i := by
  have h := List.all_eq_true.1 checkFourIndex_eq i (List.mem_finRange i)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem conjIndex_one (i : Fin 5) : conjIndex 1 i = i := (conjIndex_values i).1

theorem conjIndex_mul {g h : Equiv.Perm (Fin 12)} (hg : g ∈ fixedDQ.originalSubgroup)
    (hh : h ∈ fixedDQ.originalSubgroup) (i : Fin 5) :
    conjIndex (g * h) i = conjIndex g (conjIndex h i) := by
  apply fourGroupPerm_injective
  rw [← fourGroupPerm_conj (mul_mem hg hh), ← fourGroupPerm_conj hg, ← fourGroupPerm_conj hh,
    Subgroup.map_map]
  congr 1

@[expose] def fourGroup (i : Fin 5) : Subgroup NativeSporadic.M12 :=
  (fourGroupPerm i).comap NativeSporadic.M12.subtype

theorem fourGroup_map (i : Fin 5) :
    (fourGroup i).map NativeSporadic.M12.subtype = fourGroupPerm i := by
  apply Subgroup.map_comap_eq_self
  rw [Subgroup.range_subtype]
  exact (fourGroupPerm_le i).trans fixedDQ_le

theorem mem_fourGroup {i : Fin 5} {g : NativeSporadic.M12} :
    g ∈ fourGroup i ↔ (g : Equiv.Perm (Fin 12)) ∈ fourList i :=
  mem_fourGroupPerm

theorem card_fourGroup (i : Fin 5) : Nat.card (fourGroup i) = 4 := by
  rw [← Subgroup.card_map_of_injective NativeSporadic.M12.subtype_injective, fourGroup_map,
    card_fourGroupPerm]

theorem fourGroup_le (i : Fin 5) : fourGroup i ≤ fixedD := fun _ hg =>
  mem_fixedD.2 (fourGroupPerm_le i hg)

theorem fourGroup_injective : Function.Injective fourGroup := by
  intro i j h
  apply fourGroupPerm_injective
  rw [← fourGroup_map, ← fourGroup_map, h]

theorem fourList_sq (i : Fin 5) : ∀ g ∈ fourList i, g ^ 2 = 1 := by
  intro g hg
  have h := List.all_eq_true.1 (List.all_eq_true.1 checkFourAbelian_eq i
    (List.mem_finRange i)) g hg
  rw [Bool.and_eq_true] at h
  exact (schreierPermEq_eq_true_iff _ _).1 h.1

theorem fourList_comm (i : Fin 5) : ∀ g ∈ fourList i, ∀ h ∈ fourList i, g * h = h * g := by
  intro g hg h hh
  have h' := List.all_eq_true.1 (List.all_eq_true.1 checkFourAbelian_eq i
    (List.mem_finRange i)) g hg
  rw [Bool.and_eq_true] at h'
  exact (schreierPermEq_eq_true_iff _ _).1 (List.all_eq_true.1 h'.2 h hh)

theorem fourGroup_elementary (i : Fin 5) :
    (∀ g ∈ fourGroup i, g ^ 2 = 1) ∧ ∀ g ∈ fourGroup i, ∀ h ∈ fourGroup i, g * h = h * g := by
  refine ⟨fun g hg => Subtype.ext ?_, fun g hg h hh => Subtype.ext ?_⟩
  · simpa using fourList_sq i _ (mem_fourGroup.1 hg)
  · simpa using fourList_comm i _ (mem_fourGroup.1 hg) _ (mem_fourGroup.1 hh)

theorem imageArray_injective : Function.Injective imageArray := by
  intro g h hgh
  ext i
  exact congrFun (List.ofFn_injective hgh) i

theorem fourList_arrays (i : Fin 5) : ∀ g ∈ fourList i, imageArray g ∈ fourGroupArrays i := by
  intro g hg
  have h := List.all_eq_true.1 checkFourArrays_eq i (List.mem_finRange i)
  rw [Bool.and_eq_true] at h
  exact List.contains_iff_mem.1 (List.all_eq_true.1 h.1 g hg)

theorem fourGroupArrays_sub (i : Fin 5) :
    ∀ a ∈ fourGroupArrays i, ∃ g ∈ fourList i, imageArray g = a := by
  intro a ha
  have h := List.all_eq_true.1 checkFourArrays_eq i (List.mem_finRange i)
  rw [Bool.and_eq_true] at h
  obtain ⟨g, hg, hga⟩ := List.any_eq_true.1 (List.all_eq_true.1 h.2 a ha)
  exact ⟨g, hg, beq_iff_eq.1 hga⟩

theorem mem_fourGroup_iff_imageArray {i : Fin 5} {g : NativeSporadic.M12} :
    g ∈ fourGroup i ↔ imageArray g ∈ fourGroupArrays i := by
  rw [mem_fourGroup]
  constructor
  · exact fourList_arrays i _
  · intro h
    obtain ⟨g', hg', hgg'⟩ := fourGroupArrays_sub i _ h
    rwa [imageArray_injective hgg'] at hg'

theorem fourGroupArrays_sorted :
    (∀ i, (fourGroupArrays i).Pairwise (· < ·)) ∧
      (List.ofFn fourGroupArrays).Pairwise (· < ·) :=
  Certificates.certificate11003.2.2.2.2.2.2.2.2.2.2.1

theorem sq_eq_one_of_card_four {H : Subgroup NativeSporadic.M12} (hH : H ≤ fixedD)
    (h4 : Nat.card H = 4) {g : NativeSporadic.M12} (hg : g ∈ H) : g ^ 2 = 1 := by
  have h4' : g ^ 4 = 1 := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : H)
    rw [h4, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  exact Subtype.ext (by
    simpa using sq_eq_one_of_pow_four (mem_fixedD.1 (hH hg))
      (by simpa using congrArg Subtype.val h4'))

theorem card_eq_four_iff {H : Subgroup NativeSporadic.M12} (hH : H ≤ fixedD) :
    Nat.card H = 4 ↔ ∃ i, H = fourGroup i := by
  constructor
  · intro h4
    have hex : ∃ u ∈ H, ∃ v ∈ H, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
      by_contra hne
      push Not at hne
      have hsub : (H : Set NativeSporadic.M12) ⊆ {1} ∪ {u | u ∈ H ∧ u ≠ 1} := fun u hu => by
        by_cases h1 : u = 1
        · exact Or.inl h1
        · exact Or.inr ⟨hu, h1⟩
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ H, u ≠ 1 := by
        by_contra hall
        push Not at hall
        have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hall
        rw [this, Subgroup.card_bot] at h4
        omega
      have hsub' : (H : Set NativeSporadic.M12) ⊆ {1, u} := fun v hv => by
        by_cases h1 : v = 1
        · exact Or.inl h1
        · exact Or.inr (hne u hu v hv hu1 h1).symm
      have hle := Set.ncard_le_ncard hsub' (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h4] at hle
      have := Set.ncard_insert_le (1 : NativeSporadic.M12) {u}
      rw [Set.ncard_singleton] at this
      omega
    obtain ⟨u, hu, v, hv, hu1, hv1, huv⟩ := hex
    have hu2 := sq_eq_one_of_card_four hH h4 hu
    have hv2 := sq_eq_one_of_card_four hH h4 hv
    have huv2 := sq_eq_one_of_card_four hH h4 (mul_mem hu hv)
    have hc : u * v = v * u := by
      have e1 : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by rw [← sq, hu2])
      have e2 : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by rw [← sq, hv2])
      have e3 : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_left (by rw [← sq, huv2])
      rw [mul_inv_rev, e1, e2] at e3
      exact e3.symm
    have hne1 : (u : Equiv.Perm (Fin 12)) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hne2 : (v : Equiv.Perm (Fin 12)) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hne3 : (u : Equiv.Perm (Fin 12)) ≠ v := fun h => huv (Subtype.ext h)
    obtain ⟨i, hui, hvi⟩ := exists_fourList (mem_fixedD.1 (hH hu)) (mem_fixedD.1 (hH hv))
      (by simpa using congrArg Subtype.val hu2) (by simpa using congrArg Subtype.val hv2) hne1
      hne2 hne3 (by simpa using congrArg Subtype.val hc)
    refine ⟨i, ?_⟩
    let K : Subgroup NativeSporadic.M12 := Subgroup.closure {u, v}
    have hKH : K ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    have hKW : K ≤ fourGroup i := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact mem_fourGroup.2 hui
      · exact mem_fourGroup.2 hvi
    have hK4 : 4 ≤ Nat.card K := by
      have hL : ∀ g ∈ [1, u, v, u * v], g ∈ K := by
        intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        have hu' : u ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
        have hv' : v ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        rcases hg with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact hu'
        · exact hv'
        · exact mul_mem hu' hv'
      have hnd : [1, u, v, u * v].Nodup := by
        have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by rw [← sq, hu2])
        have h1u : (1 : NativeSporadic.M12) ≠ u := fun h => hu1 h.symm
        have h1v : (1 : NativeSporadic.M12) ≠ v := fun h => hv1 h.symm
        have h1uv : (1 : NativeSporadic.M12) ≠ u * v := fun h => huv (by
          rw [eq_inv_of_mul_eq_one_right h.symm, huinv])
        have huuv : u ≠ u * v := fun h => hv1 (by
          have := congrArg (u⁻¹ * ·) h
          simpa using this.symm)
        have hvuv : v ≠ u * v := fun h => hu1 (by
          have := congrArg (· * v⁻¹) h
          simpa using this.symm)
        simp [List.nodup_cons, h1u, h1v, h1uv, huuv, hvuv, huv]
      classical
      have := Finset.card_le_card (s := [1, u, v, u * v].toFinset)
        (t := (K : Set NativeSporadic.M12).toFinset) (fun g hg => by
          simpa using hL g (List.mem_toFinset.1 hg))
      rw [List.toFinset_card_of_nodup hnd, Set.toFinset_card] at this
      rw [Nat.card_eq_fintype_card]
      simpa using this
    have h1 : K = H := Subgroup.eq_of_le_of_card_ge hKH (by rw [h4]; exact hK4)
    have h2 : K = fourGroup i :=
      Subgroup.eq_of_le_of_card_ge hKW (by rw [card_fourGroup]; exact hK4)
    rw [← h1, h2]
  · rintro ⟨i, rfl⟩
    exact card_fourGroup i

@[expose] def fivePointPerm (d : fixedD) : Equiv.Perm (Fin 5) where
  toFun := conjIndex (d : Equiv.Perm (Fin 12))
  invFun := conjIndex ((d⁻¹ : fixedD) : Equiv.Perm (Fin 12))
  left_inv i := by
    rw [← conjIndex_mul (mem_fixedD.1 (d⁻¹).2) (mem_fixedD.1 d.2)]
    simp [conjIndex_one]
  right_inv i := by
    rw [← conjIndex_mul (mem_fixedD.1 d.2) (mem_fixedD.1 (d⁻¹).2)]
    simp [conjIndex_one]

theorem fivePointPerm_apply (d : fixedD) (i : Fin 5) :
    fivePointPerm d i = conjIndex (d : Equiv.Perm (Fin 12)) i :=
  rfl

@[expose] def fivePointHom : fixedD →* Equiv.Perm (Fin 5) where
  toFun := fivePointPerm
  map_one' := Equiv.ext fun i => conjIndex_one i
  map_mul' d e := Equiv.ext fun i => conjIndex_mul (mem_fixedD.1 d.2) (mem_fixedD.1 e.2) i

@[expose] def fixedDX : fixedD := ⟨elemX, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def fixedDY : fixedD := ⟨elemY, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem fixedDX_coe : ((fixedDX : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = permX := rfl

theorem fixedDY_coe : ((fixedDY : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = permY := rfl

theorem fivePointHom_apply (d : fixedD) (i : Fin 5) :
    fivePointHom d i = conjIndex ((d : NativeSporadic.M12) : Equiv.Perm (Fin 12)) i :=
  rfl

theorem fixedD_closure : Subgroup.closure {fixedDX, fixedDY} = ⊤ :=
  closure_pair_eq_top rfl _ _

theorem fivePointHom_x : ∀ i, fivePointHom fixedDX i = ![3, 4, 1, 2, 0] i := by
  intro i
  rw [fivePointHom_apply, fixedDX_coe]
  exact (conjIndex_values i).2.1

theorem fivePointHom_y : ∀ i, fivePointHom fixedDY i = ![2, 3, 1, 4, 0] i := by
  intro i
  rw [fivePointHom_apply, fixedDY_coe]
  exact (conjIndex_values i).2.2

theorem sign_eq_one_of_pow_five {σ : Equiv.Perm (Fin 5)} (h : σ ^ 5 = 1) :
    Equiv.Perm.sign σ = 1 := by
  have h5 : Equiv.Perm.sign σ ^ 5 = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h5
    exact absurd h5 (by decide)

theorem fivePointHom_mem (d : fixedD) : fivePointHom d ∈ alternatingGroup (Fin 5) := by
  have hle : (⊤ : Subgroup fixedD) ≤ (alternatingGroup (Fin 5)).comap fivePointHom := by
    rw [← fixedD_closure, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow_five ?_)
      rw [← map_pow]
      have : fixedDX ^ 5 = 1 := Subtype.ext (Subtype.ext (by
        change permX ^ 5 = 1
        exact Certificates.certificate11003.2.2.2.2.2.2.2.2.2.2.2.1))
      rw [this, map_one]
    · refine Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow_five ?_)
      rw [← map_pow]
      have : fixedDY ^ 5 = 1 := Subtype.ext (Subtype.ext (by
        change permY ^ 5 = 1
        exact Certificates.certificate11003.2.2.2.2.2.2.2.2.2.2.2.2.1))
      rw [this, map_one]
  exact hle (Subgroup.mem_top d)

@[expose] def fivePointAlt : fixedD →* alternatingGroup (Fin 5) :=
  fivePointHom.codRestrict _ fivePointHom_mem

theorem fivePointAlt_injective : Function.Injective fivePointAlt := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro d hd
  have h1 : fivePointHom d = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
  have h2 : ∀ i, conjIndex (d : Equiv.Perm (Fin 12)) i = i := fun i =>
    congrArg (fun σ : Equiv.Perm (Fin 5) => σ i) h1
  exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext (eq_one_of_conjIndex (mem_fixedD.1 d.2) h2)))

theorem card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

@[expose] noncomputable def fivePointEquiv : fixedD ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective fivePointAlt (fivePointAlt_injective.bijective_of_nat_card_le (by
    rw [card_alternating_five, card_fixedD]))

theorem fivePointEquiv_apply (d : fixedD) (i : Fin 5) :
    (fivePointEquiv d : Equiv.Perm (Fin 5)) i = conjIndex (d : Equiv.Perm (Fin 12)) i :=
  rfl

theorem map_conj_map_subtype (H : Subgroup NativeSporadic.M12) (d : NativeSporadic.M12) :
    (H.map (MulAut.conj d).toMonoidHom).map NativeSporadic.M12.subtype =
      (H.map NativeSporadic.M12.subtype).map
        (MulAut.conj (d : Equiv.Perm (Fin 12))).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem fourGroup_conj (d : fixedD) (i : Fin 5) :
    (fourGroup i).map (MulAut.conj (d : NativeSporadic.M12)).toMonoidHom =
      fourGroup ((fivePointEquiv d : Equiv.Perm (Fin 5)) i) := by
  apply Subgroup.map_injective NativeSporadic.M12.subtype_injective
  rw [map_conj_map_subtype, fourGroup_map, fourGroup_map, fivePointEquiv_apply]
  exact fourGroupPerm_conj (mem_fixedD.1 d.2) i

theorem card_outer_fixedD_dvd : Nat.card (Outer fixedD) ∣ 2 :=
  CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six (Or.inl rfl) fivePointEquiv

theorem fixedD_le_fixSub : fixedD ≤ fixSub beta := by
  rw [fixedD, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact elemX_mem_fixSub
  · exact elemY_mem_fixSub

theorem permX_comm_permZ : permX * permZ = permZ * permX :=
  Certificates.certificate11003.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem permY_comm_permZ : permY * permZ = permZ * permY :=
  Certificates.certificate11003.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem elemZ_comm_fixedD : ∀ d ∈ fixedD, elemZ * d = d * elemZ := by
  have hle : fixedD ≤ Subgroup.centralizer {elemZ} := by
    rw [fixedD, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl
    · exact Subtype.ext permX_comm_permZ
    · exact Subtype.ext permY_comm_permZ
  intro d hd
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hd)).symm

@[expose] noncomputable def fixZ : fixSub beta := ⟨elemZ, elemZ_mem_fixSub⟩

theorem orderOf_fixZ : orderOf fixZ = 2 := by
  rw [fixZ, Subgroup.orderOf_mk, orderOf_elemZ]

theorem fixZ_pow_mod (n : ℕ) : fixZ ^ (n % 2) = fixZ ^ n := by
  rw [← orderOf_fixZ]
  exact pow_mod_orderOf fixZ n

@[expose] noncomputable def zHom : Multiplicative (ZMod 2) →* fixSub beta where
  toFun e := fixZ ^ (Multiplicative.toAdd e).val
  map_one' := by simp
  map_mul' e f := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [fixZ_pow_mod, pow_add]

theorem zHom_comm (e : Multiplicative (ZMod 2)) (d : fixedD) :
    Commute (zHom e) (Subgroup.inclusion fixedD_le_fixSub d) := by
  apply Commute.pow_left
  exact Subtype.ext (elemZ_comm_fixedD d d.2)

@[expose] noncomputable def fixedProdHom : Multiplicative (ZMod 2) × fixedD →* fixSub beta :=
  zHom.noncommCoprod (Subgroup.inclusion fixedD_le_fixSub) zHom_comm

theorem fixedProdHom_apply (p : Multiplicative (ZMod 2) × fixedD) :
    fixedProdHom p = zHom p.1 * Subgroup.inclusion fixedD_le_fixSub p.2 :=
  rfl

theorem fixedProdHom_injective : Function.Injective fixedProdHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨e, d⟩ h
  rw [MonoidHom.mem_ker, fixedProdHom_apply] at h
  have hv : (Multiplicative.toAdd e).val < 2 := ZMod.val_lt _
  rcases (show (Multiplicative.toAdd e).val = 0 ∨ (Multiplicative.toAdd e).val = 1 by omega)
    with h0 | h1
  · have he : e = 1 := by
      have : Multiplicative.toAdd e = 0 := (ZMod.val_eq_zero _).1 h0
      exact this
    simp only [zHom, MonoidHom.coe_mk, OneHom.coe_mk, h0, pow_zero, one_mul] at h
    have h' := congrArg Subtype.val h
    have hd : d = 1 := Subtype.ext h'
    rw [he, hd]
    exact Subgroup.mem_bot.2 rfl
  · exfalso
    simp only [zHom, MonoidHom.coe_mk, OneHom.coe_mk, h1, pow_one] at h
    have h' : (elemZ : NativeSporadic.M12) * d = 1 := congrArg Subtype.val h
    apply elemZ_not_mem
    have : elemZ = (d : NativeSporadic.M12)⁻¹ := eq_inv_of_mul_eq_one_left h'
    rw [this]
    exact fixedD.inv_mem d.2

theorem fixedProdHom_bijective : Function.Bijective fixedProdHom := by
  refine fixedProdHom_injective.bijective_of_nat_card_le ?_
  rw [card_fixSub_beta, Nat.card_prod, card_fixedD,
    Nat.card_eq_fintype_card (α := Multiplicative _)]
  rfl

@[expose] noncomputable def fixedProdEquiv : Multiplicative (ZMod 2) × fixedD ≃* fixSub beta :=
  MulEquiv.ofBijective fixedProdHom fixedProdHom_bijective

@[expose] noncomputable def fixedAltEquiv :
    fixSub beta ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 5) :=
  fixedProdEquiv.symm.trans (MulEquiv.prodCongr (MulEquiv.refl _) fivePointEquiv)

theorem fixedAltEquiv_apply (e : ℕ) (d : fixedD)
    (h : elemZ ^ e * (d : NativeSporadic.M12) ∈ fixSub beta) :
    fixedAltEquiv ⟨elemZ ^ e * d, h⟩ = (Multiplicative.ofAdd (e : ZMod 2), fivePointEquiv d) := by
  have hz : (⟨elemZ ^ e * d, h⟩ : fixSub beta) =
      fixedProdEquiv (Multiplicative.ofAdd (e : ZMod 2), d) := by
    apply Subtype.ext
    change elemZ ^ e * (d : NativeSporadic.M12) =
      ((fixZ ^ ((e : ZMod 2)).val : fixSub beta) : NativeSporadic.M12) * d
    rw [ZMod.val_natCast, ← orderOf_fixZ, pow_mod_orderOf]
    rfl
  rw [hz, fixedAltEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem mem_fixSub_iff_decomp {c : NativeSporadic.M12} (hc : c ∈ fixSub beta) :
    c ∈ fixedD ∨ elemZ * c ∈ fixedD := by
  obtain ⟨⟨e, d⟩, hed⟩ := fixedProdHom_bijective.2 ⟨c, hc⟩
  have hc' : c = (zHom e : NativeSporadic.M12) * d := congrArg Subtype.val hed.symm
  have hv : (Multiplicative.toAdd e).val < 2 := ZMod.val_lt _
  rcases (show (Multiplicative.toAdd e).val = 0 ∨ (Multiplicative.toAdd e).val = 1 by omega)
    with h0 | h1
  · left
    simp only [hc', zHom, MonoidHom.coe_mk, OneHom.coe_mk, h0, pow_zero, OneMemClass.coe_one,
      one_mul]
    exact d.2
  · right
    simp only [hc', zHom, MonoidHom.coe_mk, OneHom.coe_mk, h1, pow_one]
    have : elemZ * (elemZ * (d : NativeSporadic.M12)) = d := by
      rw [← mul_assoc, ← sq, ← orderOf_elemZ, pow_orderOf_eq_one, one_mul]
    rw [fixZ]
    simpa only [this] using d.2

theorem zpowers_sup_fixedD : Subgroup.zpowers elemZ ⊔ fixedD = fixSub beta := by
  apply le_antisymm
  · refine sup_le ?_ fixedD_le_fixSub
    rw [Subgroup.zpowers_le]
    exact elemZ_mem_fixSub
  · intro c hc
    rcases mem_fixSub_iff_decomp hc with h | h
    · exact Subgroup.mem_sup_right h
    · have : c = elemZ * (elemZ * c) := by
        rw [← mul_assoc, ← sq, ← orderOf_elemZ, pow_orderOf_eq_one, one_mul]
      rw [this]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) h

theorem zpowers_inf_fixedD : Subgroup.zpowers elemZ ⊓ fixedD = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hz, hd⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  have hk : elemZ ^ k = elemZ ^ (k % 2) := by
    simpa [orderOf_elemZ] using (zpow_mod_orderOf elemZ k).symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [hk, h, zpow_zero]
    exact Subgroup.one_mem _
  · rw [hk, h, zpow_one] at hd
    exact absurd hd elemZ_not_mem

theorem permX_commutator :
    permX = permY⁻¹ * (permY⁻¹ * permX⁻¹) * permY⁻¹⁻¹ * (permY⁻¹ * permX⁻¹)⁻¹ :=
  Certificates.certificate11003.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem permY_commutator :
    permY = permX⁻¹ * (permX⁻¹ * permY⁻¹) * permX⁻¹⁻¹ * (permX⁻¹ * permY⁻¹)⁻¹ :=
  Certificates.certificate11003.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem elemX_commutator : elemX = ⁅elemY⁻¹, elemY⁻¹ * elemX⁻¹⁆ := by
  rw [commutatorElement_def]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, elemX_coe, elemY_coe]
  exact permX_commutator

theorem elemY_commutator : elemY = ⁅elemX⁻¹, elemX⁻¹ * elemY⁻¹⁆ := by
  rw [commutatorElement_def]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, elemX_coe, elemY_coe]
  exact permY_commutator

theorem fixedD_perfect : ⁅fixedD, fixedD⁆ = fixedD := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  · have hx : elemX ∈ fixedD := Subgroup.subset_closure (Set.mem_insert _ _)
    have hy : elemY ∈ fixedD := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hx' : elemX ∈ ⁅fixedD, fixedD⁆ := by
      have h := Subgroup.commutator_mem_commutator (inv_mem hy) (mul_mem (inv_mem hy) (inv_mem hx))
      rwa [← elemX_commutator] at h
    have hy' : elemY ∈ ⁅fixedD, fixedD⁆ := by
      have h := Subgroup.commutator_mem_commutator (inv_mem hx) (mul_mem (inv_mem hx) (inv_mem hy))
      rwa [← elemY_commutator] at h
    change Subgroup.closure {elemX, elemY} ≤ _
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hx'
    · exact hy'

theorem commutator_mem_fixedD_of_decomp {c₁ c₂ : NativeSporadic.M12} (h₁ : c₁ ∈ fixSub beta)
    (h₂ : c₂ ∈ fixSub beta) : ⁅c₁, c₂⁆ ∈ fixedD := by
  obtain ⟨⟨e₁, d₁⟩, hp₁⟩ := fixedProdHom_bijective.2 ⟨c₁, h₁⟩
  obtain ⟨⟨e₂, d₂⟩, hp₂⟩ := fixedProdHom_bijective.2 ⟨c₂, h₂⟩
  have hp : ⁅((e₁, d₁) : Multiplicative (ZMod 2) × fixedD), (e₂, d₂)⁆ = (1, ⁅d₁, d₂⁆) := by
    rw [commutatorElement_def, commutatorElement_def]
    simp only [Prod.mk_mul_mk, Prod.inv_mk, Prod.mk.injEq, and_true]
    rw [mul_comm e₁ e₂, mul_inv_cancel_right, mul_inv_cancel]
  have hc : ⁅(⟨c₁, h₁⟩ : fixSub beta), ⟨c₂, h₂⟩⁆ =
      Subgroup.inclusion fixedD_le_fixSub ⁅d₁, d₂⁆ := by
    rw [← hp₁, ← hp₂, ← map_commutatorElement, hp, fixedProdHom_apply, map_one, one_mul]
  have h' : ⁅c₁, c₂⁆ = ((⁅d₁, d₂⁆ : fixedD) : NativeSporadic.M12) := congrArg Subtype.val hc
  rw [h']
  exact (⁅d₁, d₂⁆ : fixedD).2

theorem fixedD_eq_commutator : fixedD = ⁅fixSub beta, fixSub beta⁆ := by
  apply le_antisymm
  · calc fixedD = ⁅fixedD, fixedD⁆ := fixedD_perfect.symm
      _ ≤ ⁅fixSub beta, fixSub beta⁆ := Subgroup.commutator_mono fixedD_le_fixSub fixedD_le_fixSub
  · rw [Subgroup.commutator_le]
    intro c₁ h₁ c₂ h₂
    exact commutator_mem_fixedD_of_decomp h₁ h₂

theorem ctss_m12_pinned_outer_fixed_product_and_five_point_map :
    (∀ i, permX i = ![0, 3, 8, 6, 10, 1, 11, 2, 4, 9, 7, 5] i) ∧
    (∀ i, permY i = ![6, 0, 2, 3, 7, 11, 5, 9, 10, 8, 4, 1] i) ∧
    (∀ i, permZ i = ![9, 7, 3, 2, 11, 10, 8, 1, 6, 0, 5, 4] i) ∧
    elemX ∈ fixSub beta ∧ elemY ∈ fixSub beta ∧ elemZ ∈ fixSub beta ∧ orderOf elemZ = 2 ∧
    fixedD ≤ fixSub beta ∧ Subgroup.zpowers elemZ ⊔ fixedD = fixSub beta ∧
    Subgroup.zpowers elemZ ⊓ fixedD = ⊥ ∧ (∀ d ∈ fixedD, elemZ * d = d * elemZ) ∧
    fixedD = ⁅fixSub beta, fixSub beta⁆ ∧ ⁅fixedD, fixedD⁆ = fixedD ∧ Nat.card fixedD = 60 ∧
    (∀ H : Subgroup NativeSporadic.M12, H ≤ fixedD → (Nat.card H = 4 ↔ ∃ i, H = fourGroup i)) ∧
    Function.Injective fourGroup ∧
    (∀ i, fourGroup i ≤ fixedD ∧ (∀ g ∈ fourGroup i, g ^ 2 = 1) ∧
      ∀ g ∈ fourGroup i, ∀ h ∈ fourGroup i, g * h = h * g) ∧
    (∀ i (g : NativeSporadic.M12), g ∈ fourGroup i ↔ imageArray g ∈ fourGroupArrays i) ∧
    (∀ i, (fourGroupArrays i).Pairwise (· < ·)) ∧
    (List.ofFn fourGroupArrays).Pairwise (· < ·) ∧
    (∀ (d : fixedD) (i : Fin 5),
      (fourGroup i).map (MulAut.conj (d : NativeSporadic.M12)).toMonoidHom =
        fourGroup ((fivePointEquiv d : Equiv.Perm (Fin 5)) i)) ∧
    (∀ i, (fivePointEquiv fixedDX : Equiv.Perm (Fin 5)) i = ![3, 4, 1, 2, 0] i) ∧
    (∀ i, (fivePointEquiv fixedDY : Equiv.Perm (Fin 5)) i = ![2, 3, 1, 4, 0] i) ∧
    (∀ (e : ℕ) (d : fixedD) (h : elemZ ^ e * (d : NativeSporadic.M12) ∈ fixSub beta),
      fixedAltEquiv ⟨_, h⟩ = (Multiplicative.ofAdd (e : ZMod 2), fivePointEquiv d)) ∧
    Nat.card (Outer fixedD) ∣ 2 :=
  ⟨permX_apply, permY_apply, permZ_apply, elemX_mem_fixSub, elemY_mem_fixSub, elemZ_mem_fixSub,
    orderOf_elemZ, fixedD_le_fixSub, zpowers_sup_fixedD, zpowers_inf_fixedD, elemZ_comm_fixedD,
    fixedD_eq_commutator, fixedD_perfect, card_fixedD, fun _ hH => card_eq_four_iff hH,
    fourGroup_injective, fun i => ⟨fourGroup_le i, fourGroup_elementary i⟩,
    fun _ _ => mem_fourGroup_iff_imageArray, fourGroupArrays_sorted.1, fourGroupArrays_sorted.2,
    fourGroup_conj, fivePointHom_x, fivePointHom_y, fixedAltEquiv_apply, card_outer_fixedD_dvd⟩

end CFSG.ComponentClassification.M12Cover
