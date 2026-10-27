module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses0
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses1
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses2
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses3
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses4
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses5
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses6
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses7
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses8
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses9
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses10
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses11
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses12
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnesses13

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourFixedLines
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks

public section

namespace CFSG.LargeEvenClassification.Helpers

local instance c8FourActionBinaryAddCommGroup : AddCommGroup (ZMod 2 × ZMod 2) :=
  @Prod.instAddCommGroup (ZMod 2) (ZMod 2)
    (ZMod.commRing 2).toAddCommGroup (ZMod.commRing 2).toAddCommGroup

noncomputable local instance c8FourActionBinaryModule :
    Module (ZMod 2) (ZMod 2 × ZMod 2) := Prod.instModule

theorem c8FourAction_all_covered (i : Fin 896) : c8FourActionCovered (c8FourRecord i) :=
  c8Four_record_property_of_chunks c8FourActionCovered
    c8FourActionChunk0_covered
    c8FourActionChunk1_covered
    c8FourActionChunk2_covered
    c8FourActionChunk3_covered
    c8FourActionChunk4_covered
    c8FourActionChunk5_covered
    c8FourActionChunk6_covered
    c8FourActionChunk7_covered
    c8FourActionChunk8_covered
    c8FourActionChunk9_covered
    c8FourActionChunk10_covered
    c8FourActionChunk11_covered
    c8FourActionChunk12_covered
    c8FourActionChunk13_covered
    i

theorem c8FourAction_all_bounded (i : Fin 896) : c8FourActionBounded (c8FourRecord i) :=
  c8Four_record_property_of_chunks c8FourActionBounded
    c8FourActionChunk0_bounded
    c8FourActionChunk1_bounded
    c8FourActionChunk2_bounded
    c8FourActionChunk3_bounded
    c8FourActionChunk4_bounded
    c8FourActionChunk5_bounded
    c8FourActionChunk6_bounded
    c8FourActionChunk7_bounded
    c8FourActionChunk8_bounded
    c8FourActionChunk9_bounded
    c8FourActionChunk10_bounded
    c8FourActionChunk11_bounded
    c8FourActionChunk12_bounded
    c8FourActionChunk13_bounded
    i

theorem c8FourAction_admissible_container (H : Subgroup C8FourCode)
    (hH : c8FourActionAdmissible H) : ∃ i : Fin 54, H ≤ c8FourActionContainer i := by
  obtain ⟨j, rfl⟩ := c8Four_subgroups_exhaustive H
  rcases c8FourAction_all_covered j with h20 | h84 | hpair | hcover | hcontainer
  · have hcentral := (c8FourActionRecordCentral_iff _ (c8Four_all_records_valid j) _).mp h20
    exact False.elim (hH.1 _ hcentral c8FourActionForbidden20.1
      c8FourActionForbidden20.2.1 c8FourActionForbidden20.2.2)
  · have hcentral := (c8FourActionRecordCentral_iff _ (c8Four_all_records_valid j) _).mp h84
    exact False.elim (hH.1 _ hcentral c8FourActionForbidden84.1
      c8FourActionForbidden84.2.1 c8FourActionForbidden84.2.2)
  · exact False.elim (hH.2.1 ⟨hpair.1,
      (c8FourActionRecordCentral_iff _ (c8Four_all_records_valid j) _).mp hpair.2⟩)
  · obtain ⟨k, hdelta, hsupport⟩ := hcover
    have hs : ∀ equation ∈ c8FourActionObstruction k,
        ∀ g ∈ c8FourCoverEquationSupport equation, g ∈ c8FourListedSubgroup j := by
      intro equation heq g hg
      exact (certificateListAll_iff _ _).mp
        ((certificateListAll_iff _ _).mp hsupport equation heq) g hg
    exact False.elim ((c8FourCoverContradiction_excludes _ _
      (c8FourActionObstruction_valid k) hs) (hH.2.2 hdelta))
  · obtain ⟨k, hk⟩ := hcontainer
    exact ⟨k, (c8FourActionSubrecord_iff _ _ (c8Four_all_records_valid j)
      (c8FourActionContainerRecord_valid k)).mp hk⟩

theorem c8FourAction_container_conclusions (H Q : Subgroup C8FourCode) (i : Fin 54)
    (hHM : H ≤ c8FourActionContainer i) (hQH : Q ≤ H) :
    pGeneratorRank 2 Q ≤ 4 ∧
      (pGeneratorRank 2 Q = 3 → ∃ g : C8FourCode, c8FourActionPrimitive H Q g) ∧
      (pGeneratorRank 2 Q = 4 → ∃ g h : C8FourCode,
        c8FourActionPrimitive H Q g ∧ c8FourActionPrimitive H Q h ∧
          c8FourActionDistinctFixedLines g h ∧
          (∀ x y : CyclicPair 2 4, c8FourApply g x = x → c8FourApply h y = y →
            c8FourBinaryCoordinates x ≠ 0 → c8FourBinaryCoordinates y ≠ 0 →
            c8FourBinaryCoordinates x ≠ c8FourBinaryCoordinates y)) := by
  obtain ⟨j, rfl⟩ := c8Four_subgroups_exhaustive Q
  have hsub : c8FourActionSubrecord (c8FourRecord j) (c8FourActionContainerRecord i) :=
    (c8FourActionSubrecord_iff _ _ (c8Four_all_records_valid j)
      (c8FourActionContainerRecord_valid i)).mpr (hQH.trans hHM)
  have hw := c8FourAction_all_bounded j i hsub
  have hprimitive (k : Fin 5)
      (hmem : c8FourRecordMem (c8FourRecord j) (c8FourActionPrimitiveCode k))
      (hcentral : c8FourActionRecordCentral (c8FourActionContainerRecord i)
        (c8FourActionPrimitiveCode k)) :
      c8FourActionPrimitive H (c8FourListedSubgroup j) (c8FourActionPrimitiveCode k) := by
    have hgood := c8FourActionPrimitiveCode_valid k
    refine ⟨hmem, ?_, hgood.1, hgood.2.1, hgood.2.2⟩
    exact c8FourActionCentral_mono hHM hQH hmem
      ((c8FourActionRecordCentral_iff _ (c8FourActionContainerRecord_valid i) _).mp hcentral)
  refine ⟨?_, ?_, ?_⟩
  · rw [c8Four_listed_rank]
    exact hw.1
  · intro h3
    rw [c8Four_listed_rank] at h3
    obtain ⟨k, hmem, hcentral⟩ := hw.2.1 h3
    exact ⟨c8FourActionPrimitiveCode k, hprimitive k hmem hcentral⟩
  · intro h4
    rw [c8Four_listed_rank] at h4
    obtain ⟨hmem16, hcentral16, hmem64, hcentral64⟩ := hw.2.2 h4
    exact ⟨⟨16⟩, ⟨64⟩, hprimitive 1 hmem16 hcentral16,
      hprimitive 2 hmem64 hcentral64, c8FourActionFixedLines16_64,
      fun x y hx hy hx0 hy0 => c8FourActionFixedLines16_64_nonzero x y hx hy hx0 hy0⟩

theorem c8Four_action_exhaustion (H : Subgroup C8FourCode)
    (hH : c8FourActionAdmissible H) (Q : Subgroup C8FourCode) (hQH : Q ≤ H) :
    pGeneratorRank 2 Q ≤ 4 ∧
      (pGeneratorRank 2 Q = 3 → ∃ g : C8FourCode, c8FourActionPrimitive H Q g) ∧
      (pGeneratorRank 2 Q = 4 → ∃ g h : C8FourCode,
        c8FourActionPrimitive H Q g ∧ c8FourActionPrimitive H Q h ∧
          c8FourActionDistinctFixedLines g h) := by
  obtain ⟨i, hi⟩ := c8FourAction_admissible_container H hH
  obtain ⟨hbound, hthree, hfour⟩ := c8FourAction_container_conclusions H Q i hi hQH
  refine ⟨hbound, hthree, ?_⟩
  intro h4
  obtain ⟨g, h, hg, hh, hlines, _⟩ := hfour h4
  exact ⟨g, h, hg, hh, hlines⟩

theorem c8Four_action_exhaustion_for_extension (H : Subgroup C8FourCode)
    (hH : c8FourActionAdmissible H) (Q : Subgroup C8FourCode) (hQH : Q ≤ H) :
    pGeneratorRank 2 Q ≤ 4 ∧
      (pGeneratorRank 2 Q = 3 → ∃ g : C8FourCode,
        g ∈ Q ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧ c8FourNormKernel g ∧ c8FourNormDoubles g ∧
          ∀ h ∈ H, Commute g h) ∧
      (pGeneratorRank 2 Q = 4 → ∃ g h : C8FourCode,
        g ∈ Q ∧ h ∈ Q ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧ h ^ 2 = 1 ∧ h ≠ 1 ∧
          c8FourNormKernel g ∧ c8FourNormDoubles g ∧
          c8FourNormKernel h ∧ c8FourNormDoubles h ∧
          (∀ k ∈ H, Commute g k) ∧ (∀ k ∈ H, Commute h k) ∧
          ∀ x y : CyclicPair 2 4, c8FourApply g x = x → c8FourApply h y = y →
            c8FourBinaryCoordinates x ≠ 0 → c8FourBinaryCoordinates y ≠ 0 →
            c8FourBinaryCoordinates x ≠ c8FourBinaryCoordinates y) := by
  obtain ⟨i, hi⟩ := c8FourAction_admissible_container H hH
  obtain ⟨hbound, hthree, hfour⟩ := c8FourAction_container_conclusions H Q i hi hQH
  refine ⟨hbound, ?_, ?_⟩
  · intro h3
    obtain ⟨g, hmem, hcentral, hinvolution, hkernel, himage⟩ := hthree h3
    exact ⟨g, hmem, hinvolution.2, hinvolution.1, hkernel,
      c8FourActionNormImage_doubles himage, fun h hh => hcentral.2 h hh⟩
  · intro h4
    obtain ⟨g, h, hg, hh, _, hparity⟩ := hfour h4
    exact ⟨g, h, hg.1, hh.1, hg.2.2.1.2, hg.2.2.1.1,
      hh.2.2.1.2, hh.2.2.1.1, hg.2.2.2.1, c8FourActionNormImage_doubles hg.2.2.2.2,
      hh.2.2.2.1, c8FourActionNormImage_doubles hh.2.2.2.2,
      fun k hk => hg.2.1.2 k hk, fun k hk => hh.2.1.2 k hk, hparity⟩

theorem c8Four_action_exhaustion_fixed_subspaces (H : Subgroup C8FourCode)
    (hH : c8FourActionAdmissible H) (Q : Subgroup C8FourCode) (hQH : Q ≤ H)
    (h4 : pGeneratorRank 2 Q = 4) :
    ∃ g h : C8FourCode, c8FourActionPrimitive H Q g ∧ c8FourActionPrimitive H Q h ∧
      Module.finrank (ZMod 2) ((AddSubgroup.toZModSubmodule 2) (c8FourActionFixedParity g)) = 1 ∧
      Module.finrank (ZMod 2) ((AddSubgroup.toZModSubmodule 2) (c8FourActionFixedParity h)) = 1 ∧
      (AddSubgroup.toZModSubmodule 2) (c8FourActionFixedParity g) ≠
        (AddSubgroup.toZModSubmodule 2) (c8FourActionFixedParity h) := by
  obtain ⟨g, h, hg, hh, hlines⟩ := (c8Four_action_exhaustion H hH Q hQH).2.2 h4
  have hsubspaces := binary_addSubgroup_distinct_lines _ _ hlines.1 hlines.2.1 hlines.2.2
  exact ⟨g, h, hg, hh, hsubspaces⟩

end CFSG.LargeEvenClassification.Helpers
