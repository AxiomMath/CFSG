module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Catalog

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open CFSG.EvenSporadicStandard.HSStd

theorem fusionA_proved : FusionA := fun _ _ _ _ _ _ _ _ hb a => fusion_a hb a

theorem s5FusionA_proved : S5FusionA := fun _ _ _ _ _ _ _ _ hb a => fusion_a hb a

theorem s5FusionB_proved : S5FusionB := fun _ _ _ _ _ _ _ _ hb a => fusion_b hb a

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
