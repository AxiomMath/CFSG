module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4B3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4B2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4B2Three
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4NS
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GSp
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3N
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3S

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kaL4GOrthThree_thm : KAL4GOrthThree := by
  intro F _ _ h3 A hA
  by_cases hs : KAL4Split A
  · exact kaL4GOrthThreeSp_thm F h3 A hA hs
  · exact kaL4GOrthThreeNS_thm F h3 A hA hs

theorem kay_L4 : KAY FL4 :=
  kay_L4_of_classes kaL4B3_thm kaL4B2_thm kaL4B2Three_thm kaL4NS_thm kaL4GOrth_thm
    kaL4GOrthThree_thm kaL4GSp_thm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
