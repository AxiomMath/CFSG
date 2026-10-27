module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerB4Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSFiveLocal

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction

theorem hsInnerB4
    (hC : CatE16) : HSInnerB4 :=
  hsInnerB4_of_five hC
    (fun _ _ _ _ hL _ hu hu2 hcu _ hf hf5 => hs_five_local_of_commutator hL hu hu2 hcu hf hf5)
    (fun _ _ _ _ hL _ ha _ hb ha3 hb3 => hs_three_conj hL ha hb ha3 hb3)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
