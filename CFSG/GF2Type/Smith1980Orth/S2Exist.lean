module

public import CFSG.GF2Type.Smith1980Orth.S2Six
public import CFSG.GF2Type.Smith1980Orth.Index
public import CFSG.GF2Type.Smith1980Orth.NotSimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] def TwoRankSixBound : Prop :=
  ∀ (q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2)), CFSG.Open.timmesfeldNondegenerate q →
    ∀ E : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)),
      E ≤ CFSG.Open.timmesfeldIsometries q → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 16

theorem exists_s2Data_of_six_le [IsSimpleGroup G]
    (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width)
    (hrank : TwoRankSixBound) : Nonempty (S2Data S) := by
  obtain ⟨k, hk⟩ := O.even
  rcases (show S.width = 6 ∨ 8 ≤ S.width by omega) with h | h
  · exact exists_s2Data_six I O h hrank
  · exact exists_s2Data I O h O.not_isSimpleGroup_Mbar0

theorem OrthData.index_mod_four_of_six_le [IsSimpleGroup G]
    (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width)
    (hrank : TwoRankSixBound) : S.M.index % 4 = 3 := by
  obtain ⟨D⟩ := exists_s2Data_of_six_le I O hw hrank
  exact D.index_mod_four

end CFSG.GF2Type.Smith1980Orth
