module

public import CFSG.GF2Type.Smith1980Orth.S2Decomp
public import CFSG.GF2Type.Smith1980Orth.S2Fusion
public import CFSG.GF2Type.Smith1980Orth.IndexCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem S2Data.index_mod_four (D : S2Data S) :
    S.M.index % 4 = 3 := by
  rw [← card_conj_eq_index, card_conj_mod_four S fun y hy hyM hyQ => ?_]
  · exact D.card_conj_mem_Q_mod_four
  refine D.two_le_finrank_commSpace ⟨_, rfl⟩ ?_ ?_
  · rw [← map_mul]
    have : (⟨y, hyM⟩ : S.M) * ⟨y, hyM⟩ = 1 :=
      Subtype.ext (SmithQ.mul_self_eq_one_of_isConj S hy)
    rw [this, map_one]
  · intro h1
    have hk : (⟨y, hyM⟩ : S.M) ∈ S.ρ.ker := h1
    rw [S.ker_ρ] at hk
    exact hyQ (S.mem_QG_iff.2 ⟨hyM, hk⟩)

end CFSG.GF2Type.Smith1980Orth
