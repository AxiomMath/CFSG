module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionPredicates
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourCoverObstructions
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroups

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def c8FourActionPrimitiveCode (i : Fin 5) : C8FourCode :=
  match i.val with
  | 0 => ⟨4⟩
  | 1 => ⟨16⟩
  | 2 => ⟨64⟩
  | 3 => ⟨68⟩
  | _ => ⟨80⟩

set_option maxHeartbeats 8000000 in
theorem c8FourActionPrimitiveCode_valid (i : Fin 5) :
    c8FourActionInvolution (c8FourActionPrimitiveCode i) ∧
      c8FourNormKernel (c8FourActionPrimitiveCode i) ∧
      c8FourActionNormImage (c8FourActionPrimitiveCode i) := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
theorem c8FourActionForbidden20 :
    c8FourActionInvolution ⟨20⟩ ∧ c8FourNormKernel ⟨20⟩ ∧ c8FourActionFixedNorm ⟨20⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem c8FourActionForbidden84 :
    c8FourActionInvolution ⟨84⟩ ∧ c8FourNormKernel ⟨84⟩ ∧ c8FourActionFixedNorm ⟨84⟩ := by
  decide +kernel

@[expose] def c8FourActionContainerIndex (i : Fin 54) : Fin 896 :=
  (#[50, 76, 89, 94, 258, 286, 288, 304, 314, 316, 320, 325, 343, 346, 348, 356, 360, 363, 364, 383, 402, 454, 465, 481, 505, 506, 542, 544, 548, 554, 566, 567, 583, 596, 604, 608, 611, 620, 624, 626, 627, 642, 650, 652, 686, 687, 694, 695, 763, 777, 781, 837, 860, 879] : Array (Fin 896))[i.val]!

@[expose] def c8FourActionContainerRecord (i : Fin 54) : C8FourSubgroupRecord :=
  (#[c8FourRecordData50, c8FourRecordData76, c8FourRecordData89, c8FourRecordData94, c8FourRecordData258, c8FourRecordData286, c8FourRecordData288, c8FourRecordData304, c8FourRecordData314, c8FourRecordData316, c8FourRecordData320, c8FourRecordData325, c8FourRecordData343, c8FourRecordData346, c8FourRecordData348, c8FourRecordData356, c8FourRecordData360, c8FourRecordData363, c8FourRecordData364, c8FourRecordData383, c8FourRecordData402, c8FourRecordData454, c8FourRecordData465, c8FourRecordData481, c8FourRecordData505, c8FourRecordData506, c8FourRecordData542, c8FourRecordData544, c8FourRecordData548, c8FourRecordData554, c8FourRecordData566, c8FourRecordData567, c8FourRecordData583, c8FourRecordData596, c8FourRecordData604, c8FourRecordData608, c8FourRecordData611, c8FourRecordData620, c8FourRecordData624, c8FourRecordData626, c8FourRecordData627, c8FourRecordData642, c8FourRecordData650, c8FourRecordData652, c8FourRecordData686, c8FourRecordData687, c8FourRecordData694, c8FourRecordData695, c8FourRecordData763, c8FourRecordData777, c8FourRecordData781, c8FourRecordData837, c8FourRecordData860, c8FourRecordData879] : Array C8FourSubgroupRecord)[i.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8FourActionContainerRecord_eq (i : Fin 54) :
    c8FourActionContainerRecord i = c8FourRecord (c8FourActionContainerIndex i) := by
  fin_cases i <;> unfold c8FourRecord <;> rfl

theorem c8FourActionContainerRecord_valid (i : Fin 54) :
    c8FourRecordValid (c8FourActionContainerRecord i) := by
  rw [c8FourActionContainerRecord_eq]
  exact c8Four_all_records_valid _

@[expose] def c8FourActionContainer (i : Fin 54) : Subgroup C8FourCode :=
  c8FourRecordSubgroup (c8FourActionContainerRecord i) (c8FourActionContainerRecord_valid i)

@[expose] def c8FourActionObstruction (i : Fin 20) : List C8FourCoverEquation :=
  (#[c8FourCoverObstruction0, c8FourCoverObstruction1, c8FourCoverObstruction2, c8FourCoverObstruction3, c8FourCoverObstruction4, c8FourCoverObstruction5, c8FourCoverObstruction6, c8FourCoverObstruction7, c8FourCoverObstruction8, c8FourCoverObstruction9, c8FourCoverObstruction10, c8FourCoverObstruction11, c8FourCoverObstruction12, c8FourCoverObstruction13, c8FourCoverObstruction14, c8FourCoverObstruction15, c8FourCoverObstruction16, c8FourCoverObstruction17, c8FourCoverObstruction18, c8FourCoverObstruction19] : Array (List C8FourCoverEquation))[i.val]!

set_option maxRecDepth 10000 in
theorem c8FourActionObstruction_valid (i : Fin 20) :
    c8FourCoverContradiction (c8FourActionObstruction i) := by
  fin_cases i
  · exact c8FourCoverObstruction0_valid
  · exact c8FourCoverObstruction1_valid
  · exact c8FourCoverObstruction2_valid
  · exact c8FourCoverObstruction3_valid
  · exact c8FourCoverObstruction4_valid
  · exact c8FourCoverObstruction5_valid
  · exact c8FourCoverObstruction6_valid
  · exact c8FourCoverObstruction7_valid
  · exact c8FourCoverObstruction8_valid
  · exact c8FourCoverObstruction9_valid
  · exact c8FourCoverObstruction10_valid
  · exact c8FourCoverObstruction11_valid
  · exact c8FourCoverObstruction12_valid
  · exact c8FourCoverObstruction13_valid
  · exact c8FourCoverObstruction14_valid
  · exact c8FourCoverObstruction15_valid
  · exact c8FourCoverObstruction16_valid
  · exact c8FourCoverObstruction17_valid
  · exact c8FourCoverObstruction18_valid
  · exact c8FourCoverObstruction19_valid

@[expose] def c8FourActionObstructionSupport (r : C8FourSubgroupRecord) (i : Fin 20) : Prop :=
  certificateListAll (c8FourActionObstruction i) (fun equation =>
    certificateListAll (c8FourCoverEquationSupport equation) (c8FourRecordMem r))

instance c8FourActionObstructionSupport_decidable (r : C8FourSubgroupRecord) (i : Fin 20) :
    Decidable (c8FourActionObstructionSupport r i) := inferInstanceAs (Decidable (
      certificateListAll (c8FourActionObstruction i) (fun equation =>
        certificateListAll (c8FourCoverEquationSupport equation) (c8FourRecordMem r))))

@[expose] def c8FourActionCovered (r : C8FourSubgroupRecord) : Prop :=
  c8FourActionRecordCentral r ⟨20⟩ ∨
  c8FourActionRecordCentral r ⟨84⟩ ∨
  (c8FourRecordMem r c8FourDelta ∧ c8FourActionRecordCentral r c8FourNu) ∨
  (∃ i : Fin 20, c8FourRecordMem r c8FourDelta ∧ c8FourActionObstructionSupport r i) ∨
  ∃ i : Fin 54, c8FourActionSubrecord r (c8FourActionContainerRecord i)

@[expose] def c8FourActionRecordWitness (r s : C8FourSubgroupRecord) : Prop :=
  r.generators.length ≤ 4 ∧
  (r.generators.length = 3 → ∃ i : Fin 5,
    c8FourRecordMem r (c8FourActionPrimitiveCode i) ∧
      c8FourActionRecordCentral s (c8FourActionPrimitiveCode i)) ∧
  (r.generators.length = 4 →
    c8FourRecordMem r ⟨16⟩ ∧ c8FourActionRecordCentral s ⟨16⟩ ∧
      c8FourRecordMem r ⟨64⟩ ∧ c8FourActionRecordCentral s ⟨64⟩)

instance c8FourActionRecordWitness_decidable (r s : C8FourSubgroupRecord) :
    Decidable (c8FourActionRecordWitness r s) := inferInstanceAs (Decidable (
      r.generators.length ≤ 4 ∧
      (r.generators.length = 3 → ∃ i : Fin 5,
        c8FourRecordMem r (c8FourActionPrimitiveCode i) ∧
          c8FourActionRecordCentral s (c8FourActionPrimitiveCode i)) ∧
      (r.generators.length = 4 →
        c8FourRecordMem r ⟨16⟩ ∧ c8FourActionRecordCentral s ⟨16⟩ ∧
          c8FourRecordMem r ⟨64⟩ ∧ c8FourActionRecordCentral s ⟨64⟩)))

@[expose] def c8FourActionBounded (r : C8FourSubgroupRecord) : Prop :=
  ∀ i : Fin 54, c8FourActionSubrecord r (c8FourActionContainerRecord i) →
    c8FourActionRecordWitness r (c8FourActionContainerRecord i)

instance c8FourActionBounded_decidable (r : C8FourSubgroupRecord) :
    Decidable (c8FourActionBounded r) := Fintype.decidableForallFintype

theorem c8FourActionBounded_of_small (r : C8FourSubgroupRecord)
    (hr : r.generators.length ≤ 2) : c8FourActionBounded r := by
  intro i _
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    omega
  · intro h
    omega

theorem c8FourActionFixedLines16_64 : c8FourActionDistinctFixedLines ⟨16⟩ ⟨64⟩ := by
  have h16 : (c8FourActionFixedParityElements ⟨16⟩).card = 2 := by decide +kernel
  have h64 : (c8FourActionFixedParityElements ⟨64⟩).card = 2 := by decide +kernel
  refine ⟨(c8FourActionFixedParity_card _).trans h16,
    (c8FourActionFixedParity_card _).trans h64, ?_⟩
  have hmem : (1, 0) ∈ c8FourActionFixedParityElements ⟨16⟩ := by decide +kernel
  have hnot : (1, 0) ∉ c8FourActionFixedParityElements ⟨64⟩ := by decide +kernel
  intro heq
  exact hnot ((c8FourActionFixedParityElements_mem _ _).mpr
    (heq ▸ (c8FourActionFixedParityElements_mem _ _).mp hmem))

set_option maxHeartbeats 8000000 in
theorem c8FourActionFixedLines16_64_nonzero (x y : CyclicPair 2 4)
    (hx : c8FourApply ⟨16⟩ x = x) (hy : c8FourApply ⟨64⟩ y = y)
    (hx0 : c8FourBinaryCoordinates x ≠ 0) (hy0 : c8FourBinaryCoordinates y ≠ 0) :
    c8FourBinaryCoordinates x ≠ c8FourBinaryCoordinates y := by
  have h : ∀ x y : CyclicPair 2 4,
      c8FourApply ⟨16⟩ x = x → c8FourApply ⟨64⟩ y = y →
      c8FourBinaryCoordinates x ≠ 0 → c8FourBinaryCoordinates y ≠ 0 →
      c8FourBinaryCoordinates x ≠ c8FourBinaryCoordinates y := by
    decide +kernel
  exact h x y hx hy hx0 hy0

end CFSG.LargeEvenClassification.Helpers
