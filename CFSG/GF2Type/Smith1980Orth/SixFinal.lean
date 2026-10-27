module

public import CFSG.GF2Type.Smith1980Orth.S3ThmA
public import CFSG.GF2Type.Smith1980Orth.S4ThmB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.oe44 [IsSimpleGroup G] (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width) :
    OE44 S := by
  refine oe44_of_fourOne S (fourOne_of S fun g => ?_)
  have O' := O.conjBy g
  have hw' : 6 ≤ (S.conjBy g).width := by rw [Setting.width_conjBy]; exact hw
  obtain ⟨D⟩ := exists_s2Data_of_six_le I O' hw' twoRankSixBound
  have hT := O'.oTypes I hw' D
  have h34a := O'.oe34a I hw'
  refine ⟨h34a, fun k hxM hxQ => ?_, fun w y hw hwM hwQ hy hyQ hyz => ?_⟩
  · exact D.odd_ncard_conj_mem_Dl hT hxM hxQ
      (h34a _ (isConj_iff.mpr ⟨k, rfl⟩) hxM hxQ) (O'.oDelta I hw' k hxM hxQ)
  · rcases D.cl_commutator_mem hT hw hwM hwQ hy hyQ hyz with h | ⟨c, hc, hcQ, -, hcl⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, hcQ, hcl⟩

theorem OrthData.sixAt [IsSimpleGroup G] (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width) :
    SixAt S := by
  obtain ⟨D⟩ := exists_s2Data_of_six_le I O hw twoRankSixBound
  have h34a := O.oe34a I hw
  exact ⟨⟨D⟩, hw, O.not_bad I hw, h34a, oe34b_of S h34a,
    D.oLocal (O.oTypes I hw D) h34a (O.oe44 I hw), D.oe24Line⟩

theorem OrthData.oe421Three [IsSimpleGroup G] (I : TimInputs) (O : OrthData S)
    (hw : 6 ≤ S.width) : OE421Three S :=
  oe421Three_of_sixAt (fun g => (O.conjBy g).sixAt I (by rw [Setting.width_conjBy]; exact hw))
    (O.sixAt I hw)

theorem sixCore_of_timInputs (I : TimInputs) : SixCore where
  types _ _ _ _ _ O hw D := O.oTypes I hw D
  e34a _ _ _ _ _ O hw := O.oe34a I hw
  delta _ _ _ _ _ O hw := O.oDelta I hw
  e421 _ _ _ _ _ O hw := O.oe421Three I hw

theorem smith1980OrthogonalSix_of_timInputs (I : TimInputs)
    (hHolt : CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) (hId : IdentInput) :
    Smith1980OrthogonalSixStatement :=
  smith1980OrthogonalSix_of_core I hHolt hId (sixCore_of_timInputs I)

end CFSG.GF2Type.Smith1980Orth
