module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.AlternatingFactsRegular

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv

@[expose] def aNineEGenX : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineEZeroGenY : alternatingGroup (Fin 9) :=
  ⟨swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineEZeroGenZ : alternatingGroup (Fin 9) :=
  ⟨swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineEOneGenY : alternatingGroup (Fin 9) :=
  ⟨swap 0 2 * swap 1 3 * swap 4 7 * swap 5 6, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineEOneGenZ : alternatingGroup (Fin 9) :=
  ⟨swap 0 4 * swap 1 5 * swap 2 7 * swap 3 6, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def ANineEZero : Subgroup (alternatingGroup (Fin 9)) :=
  Subgroup.closure {aNineEGenX, aNineEZeroGenY, aNineEZeroGenZ}

@[expose] def ANineEOne : Subgroup (alternatingGroup (Fin 9)) :=
  Subgroup.closure {aNineEGenX, aNineEOneGenY, aNineEOneGenZ}

theorem isRegularTriple_aNineEZero : IsRegularTriple (aNineEGenX : Perm (Fin 9))
    (aNineEZeroGenY : Perm (Fin 9)) (aNineEZeroGenZ : Perm (Fin 9)) where
  mul_self_x := by decide
  mul_self_y := by decide
  mul_self_z := by decide
  mul_x := by decide +kernel
  mul_y := by decide +kernel
  mul_z := by decide +kernel
  injective := by decide +kernel
  comm := by decide +kernel
  sq := by decide +kernel
  card_support := by decide +kernel
  apply_eight := by decide +kernel
  transitive := by decide +kernel
  free := by decide +kernel

theorem isRegularTriple_aNineEOne : IsRegularTriple (aNineEGenX : Perm (Fin 9))
    (aNineEOneGenY : Perm (Fin 9)) (aNineEOneGenZ : Perm (Fin 9)) where
  mul_self_x := by decide
  mul_self_y := by decide
  mul_self_z := by decide
  mul_x := by decide +kernel
  mul_y := by decide +kernel
  mul_z := by decide +kernel
  injective := by decide +kernel
  comm := by decide +kernel
  sq := by decide +kernel
  card_support := by decide +kernel
  apply_eight := by decide +kernel
  transitive := by decide +kernel
  free := by decide +kernel

theorem card_aNineEZero : Nat.card ANineEZero = 8 :=
  isRegularTriple_aNineEZero.card_closure

instance isElementaryAbelian_aNineEZero : IsElementaryAbelian 2 ANineEZero :=
  isRegularTriple_aNineEZero.isElementaryAbelian

instance isElementaryAbelian_aNineEOne : IsElementaryAbelian 2 ANineEOne :=
  isRegularTriple_aNineEOne.isElementaryAbelian

theorem apply_eight_of_mem_aNineEZero {g : alternatingGroup (Fin 9)} (hg : g ∈ ANineEZero) :
    (g : Perm (Fin 9)) 8 = 8 :=
  isRegularTriple_aNineEZero.apply_eight_of_mem hg

theorem cycleType_of_mem_aNineEZero {g : alternatingGroup (Fin 9)} (hg : g ∈ ANineEZero)
    (hg1 : g ≠ 1) : (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2} :=
  isRegularTriple_aNineEZero.cycleType_of_mem hg hg1

theorem existsUnique_mem_aNineEZero_apply_eq {i j : Fin 9} (hi : i ≠ 8) (hj : j ≠ 8) :
    ∃! g, g ∈ ANineEZero ∧ (g : Perm (Fin 9)) i = j :=
  isRegularTriple_aNineEZero.existsUnique_mem_apply_eq hi hj

theorem eq_one_of_mem_aNineEZero_of_apply_eq {g : alternatingGroup (Fin 9)} (hg : g ∈ ANineEZero)
    {i : Fin 9} (hi : i ≠ 8) (hgi : (g : Perm (Fin 9)) i = i) : g = 1 :=
  isRegularTriple_aNineEZero.eq_one_of_apply_eq hg hi hgi

theorem normalizer_aNineEZero_le_stabilizer :
    Subgroup.normalizer (ANineEZero : Set (alternatingGroup (Fin 9))) ≤
      MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) :=
  isRegularTriple_aNineEZero.normalizer_le_stabilizer

theorem normalizer_aNineEOne_le_stabilizer :
    Subgroup.normalizer (ANineEOne : Set (alternatingGroup (Fin 9))) ≤
      MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) :=
  isRegularTriple_aNineEOne.normalizer_le_stabilizer

theorem mem_aNineSylow_of_coe_eq {g : alternatingGroup (Fin 9)} (v : Fin 64)
    (hv : (g : Perm (Fin 9)) = aNineSylowWordPerm v) : g ∈ ANineSylow := by
  rw [show g = aNineSylowWord v from Subtype.ext (by rw [hv, coe_aNineSylowWord])]
  exact aNineSylowWord_mem v

theorem aNineEGenX_eq_mul : aNineEGenX = aNineSylowGenA * aNineSylowGenC :=
  Subtype.ext (by decide)

theorem aNineEGenX_mem_aNineSylow : aNineEGenX ∈ ANineSylow :=
  mem_aNineSylow_of_coe_eq 40 (by decide)

theorem aNineEZero_le_aNineSylow : ANineEZero ≤ ANineSylow := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact aNineEGenX_mem_aNineSylow
  · exact mem_aNineSylow_of_coe_eq 20 (by decide)
  · exact mem_aNineSylow_of_coe_eq 1 (by decide)

theorem aNineEOne_le_aNineSylow : ANineEOne ≤ ANineSylow := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact aNineEGenX_mem_aNineSylow
  · exact mem_aNineSylow_of_coe_eq 28 (by decide)
  · exact mem_aNineSylow_of_coe_eq 43 (by decide)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
