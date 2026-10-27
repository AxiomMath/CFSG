module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223Stmt22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Y1K2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Y1Quot

public section

namespace CFSG.Quasithin.S15223P4.Y1

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem false_of_Y1_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}
    (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))
    (hred : ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)))
    {H₁ H₂ : Subgroup G} (hpair : IsHPair H (V154 T Mc M) H₁ H₂)
    (hK2 : ⁅X, oTwoUpper H₂⁆ ≤ pCoreOf 2 X)
    (hXK2 : X ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G))
    (h22 : StageLemma15222Canon_F4) : False :=
  h22 G T Mc M c.setting H c.hstar H₁ H₂ hpair B₀ c.b0 I c.min.1 c.concl c.charTwoI h3 hred
    (oPrimeResidualOf 3 (M ⊓ I)) rfl (oTwoUpper_oPrimeResidualOf_three _).symm
    (oPrimeResidualOf_le1516 3 _) (S_le_normalizer c) (nonempty_quot c hN h3)
    (commutator_le c hN h3 hK2 hXK2)

end CFSG.Quasithin.S15223P4.Y1
