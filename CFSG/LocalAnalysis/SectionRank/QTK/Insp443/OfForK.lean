module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfOf
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclOf

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin

theorem For.of_forK (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {P : (S : Type) → [Group S] → Prop} (hF : ForK P) : For P :=
  fun _ _ _ _ _ _ _ _ _ K hH hP =>
    hH.concl443B_of_conclK (hF ↥K _ _ _ (hH.kConf h37 h38 h39) hP)

end CFSG.SectionRank.QTK.Insp443
