module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Classification.Basic.Transitivity
public import CFSG.Fischer.Classification.Symplectic.Recognition

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer

theorem symplecticInput : SymplecticInput := by
  intro G _ D hH _ hsymp
  exact classicalConclusion_of_symplecticType hH.pair hH.center hH.simple hsymp
    fun _ ha _ hb _ hc _ he hab habc hce hcec =>
      Pair.exists_conj_pair_of_commute hH.pair hH.center hH.simple ha hb hc he hab habc hce hcec

end CFSG.Fischer.Classification
