module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P4CExcl
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223W21
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace S15223P4

namespace C

theorem false_of_lnQuot_F4 (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (h12 : He12.StageLemma15212W_F4) (h1521 : StageLemma15221W_F4)
    {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M H : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}
    (c : P4Ctx T Mc M H B₀ I X) (hLn : IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5) : False := by
  have d := CData.mk' hF318 h36 h38 hK c hLn
  have hF : ¬ X ≤ Mc := d.X_not_le_Mc
  have hN := d.natOne_of_F4 h12 hF (d.lemma15127Concl_of h51 hI16 hA8 hF)
  obtain ⟨n, W, hn, ⟨D⟩, hZW⟩ := d.exists_natural hF hN
  rcases hn with rfl | rfl
  · exact d.false_of_four hF D hZW
  · exact d.false_of_five (fun H₁ H₂ hP => h1521 G T Mc M c.setting H c.hstar H₁ H₂ hP B₀ c.b0 I
      c.min.1) hF D hZW (d.isLnTwo_four_kI hF D hZW)

end C

end S15223P4

end CFSG.Quasithin
