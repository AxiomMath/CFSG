module

public import CFSG.GF2Type.Smith1980Orth.W4PlusTypes
public import CFSG.GF2Type.Smith1980Orth.S3ThmARel
public import CFSG.GF2Type.Smith1980Orth.ConjInv
public import CFSG.GF2Type.Smith1980Orth.Four21

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

theorem oTypes_of_width_eq_four {M1 : Subgroup S.O} (D : S2Data S M1) (hw : S.width = 4) :
    D.OTypes := by
  intro x hx hxM hxQ
  obtain ⟨k, rfl⟩ := isConj_iff.mp hx
  have h34a : OE34a S := D.oe34a_of_width_eq_four hw
  refine D.types_of_base (fun {k'} hx'M hx'Q hx'z ha₀ => ?_) hxM hxQ
    (h34a _ (isConj_iff.mpr ⟨k, rfl⟩) hxM hxQ)
    (exists_of_not_bad (D.not_bad_of_width_eq_four hw k) hxM hxQ)
  exact D.types_base_of_card hw hx'M hx'Q hx'z ha₀
    (eight_le_card_QG_inf_Qa_of_oEight D.oEight D.good.H.conj_mem D.good.H.conj_ne
      hx'M hx'Q (S.mem_Qa_symm (fun h => hx'Q (h ▸ D.good.H.conj_mem)) ha₀))

theorem fourOne_of_width_eq_four [IsSimpleGroup G] {M1 : Subgroup S.O} (D : S2Data S M1)
    (hw : S.width = 4) : FourOne S := by
  have hT : D.OTypes := D.oTypes_of_width_eq_four hw
  have h34a : OE34a S := D.oe34a_of_width_eq_four hw
  have hOdd : OOdd S := by
    intro k hxM hxQ
    exact D.odd_ncard_conj_mem_Dl hT hxM hxQ
      (h34a _ (isConj_iff.mpr ⟨k, rfl⟩) hxM hxQ)
      (D.oDelta_of_width_eq_four hw k hxM hxQ)
  have hF3 : OF3 S := by
    intro w y hwc hwM hwQ hyc hyQ hyz
    rcases D.cl_commutator_mem hT hwc hwM hwQ hyc hyQ hyz with h | ⟨c, hc, hcQ, -, hcl⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, hcQ, hcl⟩
  exact fourOne_of S fun g => ⟨h34a.conjBy g, hOdd.conjBy g, hF3.conjBy g⟩

theorem oLocal_of_width_eq_four [IsSimpleGroup G] {M1 : Subgroup S.O} (D : S2Data S M1)
    (hw : S.width = 4) : OLocal S :=
  D.oLocal (D.oTypes_of_width_eq_four hw) (D.oe34a_of_width_eq_four hw)
    (oe44_of_fourOne S (D.fourOne_of_width_eq_four hw))

theorem oe421Three_of_width_eq_four [IsSimpleGroup G] {M1 : Subgroup S.O} (D : S2Data S M1)
    (hw : S.width = 4) : OE421Three S :=
  oe421Three_of_inputs S (D.oLocal_of_width_eq_four hw)
    (fun g => (D.oLocal_of_width_eq_four hw).conjBy g)
    (D.oe34a_of_width_eq_four hw) D.oe24Line (D.not_bad_of_width_eq_four hw)
    (D.fourOne_of_width_eq_four hw)

theorem oLocal_oPath_of_width_eq_four [IsSimpleGroup G] {M1 : Subgroup S.O} (D : S2Data S M1)
    (hw : S.width = 4) : OLocal S ∧ OPath S :=
  ⟨D.oLocal_of_width_eq_four hw,
    D.oPath (D.oTypes_of_width_eq_four hw) (D.oe34a_of_width_eq_four hw)
      (oe44_of_fourOne S (D.fourOne_of_width_eq_four hw))
      (D.oe421Three_of_width_eq_four hw)⟩

end S2Data

end CFSG.GF2Type.Smith1980Orth
