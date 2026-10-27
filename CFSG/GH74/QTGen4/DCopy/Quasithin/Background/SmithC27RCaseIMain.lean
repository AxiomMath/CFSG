module

public import CFSG.Quasithin.Background.SmithC27RCaseIMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27RCaseI

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin


variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {H R M K V : Subgroup G}

theorem three_of_residueRankTwo_F4 (hC132 : ASInputs.AS_C_1_32_F4) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueRankTwo K V) : C27Three H R M K V :=
  three_of_residueRankTwo_of_F4 hC132 h hs hJ hnS ht (ResidueRankTwo.isRankTwoLie2Derived hs ht)
    ht.isRadicalParabolic ht.maxParabolicMaximal fun hb _ htr hmax hO =>
      Or.inr (Or.inr (Or.inl (c27_hat6 h hs hnS hb htr hmax hO hJ)))

theorem three_of_residueTypeI_F4 (hC132 : ASInputs.AS_C_1_32_F4) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueTypeI K V) : C27Three H R M K V := by
  rcases ht with ht | ht | ht
  · exact (false_of_residueRankOne h hs hJ hnS ht).elim
  · exact three_of_residueRankTwo_F4 hC132 h hs hJ hnS ht
  · exact three_of_residueRankThree h hs hJ hnS ht

end CFSG.Quasithin.SmithC27
