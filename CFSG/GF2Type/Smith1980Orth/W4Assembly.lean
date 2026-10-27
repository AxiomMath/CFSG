module

public import CFSG.GF2Type.Smith1980Orth.ReductionW4
public import CFSG.GF2Type.Smith1980Orth.Four21
public import CFSG.GF2Type.Smith1980Orth.W4PlusTypes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.fourOne_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) : FourOne S := by
  refine fourOne_of S fun g => ?_
  have O' := O.conjBy g
  have hw' : (S.conjBy g).width = 4 := by rw [Setting.width_conjBy]; exact hw
  obtain ⟨D⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres O' hw'
  have hT := O'.oTypes_of_width_eq_four' I hAS4 hThmA hres hw' D
  have h34a := O'.oe34a_of_width_eq_four I hAS4 hThmA hres hw'
  refine ⟨h34a, fun k hxM hxQ => ?_, fun w y hw hwM hwQ hy hyQ hyz => ?_⟩
  · exact D.odd_ncard_conj_mem_Dl hT hxM hxQ
      (h34a _ (isConj_iff.mpr ⟨k, rfl⟩) hxM hxQ)
      (O'.oDelta_of_width_eq_four I hAS4 hThmA hres hw' k hxM hxQ)
  · rcases D.cl_commutator_mem hT hw hwM hwQ hy hyQ hyz with h | ⟨c, hc, hcQ, -, hcl⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, hcQ, hcl⟩

theorem OrthData.oe44_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) : OE44 S :=
  oe44_of_fourOne S (O.fourOne_of_width_eq_four I hAS4 hThmA hres hw)

theorem OrthData.oLocal_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) : OLocal S := by
  obtain ⟨D⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres O hw
  exact D.oLocal (O.oTypes_of_width_eq_four' I hAS4 hThmA hres hw D)
    (O.oe34a_of_width_eq_four I hAS4 hThmA hres hw)
    (O.oe44_of_width_eq_four I hAS4 hThmA hres hw)

theorem OrthData.oe421Three_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) :
    OE421Three S := by
  obtain ⟨D⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres O hw
  refine oe421Three_of_inputs S (O.oLocal_of_width_eq_four I hAS4 hThmA hres hw)
    (fun g => ?_) (O.oe34a_of_width_eq_four I hAS4 hThmA hres hw) D.oe24Line
    (O.not_bad_of_width_eq_four I hAS4 hThmA hres hw)
    (O.fourOne_of_width_eq_four I hAS4 hThmA hres hw)
  have hw' : (S.conjBy g).width = 4 := by rw [Setting.width_conjBy]; exact hw
  exact (O.conjBy g).oLocal_of_width_eq_four I hAS4 hThmA hres hw'

theorem w4Inputs (I : TimInputs) (hAS4 : S14.AschbacherSmithW4Input)
    (hThmA : DW.W4Rank.TheoremAWidthFour) (hres : W4.PGL25W4Free) :
    W4Inputs where
  local_ G _ _ _ S O hw := O.oLocal_of_width_eq_four I hAS4 hThmA hres hw
  path G _ _ _ S O hw := by
    obtain ⟨D⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres O hw
    exact D.oPath (O.oTypes_of_width_eq_four' I hAS4 hThmA hres hw D)
      (O.oe34a_of_width_eq_four I hAS4 hThmA hres hw)
      (O.oe44_of_width_eq_four I hAS4 hThmA hres hw)
      (O.oe421Three_of_width_eq_four I hAS4 hThmA hres hw)
  index G _ _ _ S O hw := by
    obtain ⟨D⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres O hw
    exact D.index_mod_four

end CFSG.GF2Type.Smith1980Orth
