module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CExcl
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P4COff

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem natOne_of_F4 (h12 : He12.StageLemma15212W_F4) (hF : ¬ X ≤ Mc)
    (h : Lemma15127Concl (zSOf T Mc M B₀) X) : NatOne T Mc M B₀ X := by
  obtain ⟨hU, halt⟩ := h
  let _ : CommGroup ↥(uOf1527 (zSOf T Mc M B₀) X) := commGroupOfElemAbelian hU
  have hV2 : ∀ w : ↥(uOf1527 (zSOf T Mc M B₀) X), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hU.2 w w.2)
  have hF' := d.facts15128 hF
  have hoff := d.q1Offender_F4 h12 hF
  rcases halt with ⟨Z, hZ, -, hext⟩ | hext5 | ⟨n, hsum⟩ | ⟨n, hn, k, hk1, hkn, hnat⟩
  · exact (ctx_excl hF' (FLc.excl_ext4 hV2 (hZ.trans inf_le_left) hext) hoff).elim
  · exact (ctx_excl hF' (FLc.excl_ext5 hV2 hext5) hoff).elim
  · exact (false_of_sumNatDual hF' hoff ⟨hU, n, hsum⟩).elim
  · by_cases hk : k = 1
    · subst hk
      exact ⟨hU, n, hn, hnat⟩
    · exact (ctx_excl hF' (FLc.excl_nat2 hV2 (by rcases hn with rfl | rfl <;> norm_num)
        (by omega) hnat) hoff).elim

end CData

end C

end S15223P4

end CFSG.Quasithin
