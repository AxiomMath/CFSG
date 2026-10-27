module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Iface
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Gen

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem largeReeCenterGen
    : LargeReeCenterGen := by
  intro a K _ _ _ ha hK
  exact ⟨⟨center_zero hK, generation_zero ha hK⟩, ⟨center_one hK, generation_one ha hK⟩⟩

theorem largeReeParabolicFacts
    : LargeReeParabolicFacts :=
  largeReeParabolicFacts_of largeReeCenterGen

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

theorem pairsFor_2F4
    : PairsFor Type2F4 :=
  pairsFor_2F4_of_facts F4.largeReeParabolicFacts

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
