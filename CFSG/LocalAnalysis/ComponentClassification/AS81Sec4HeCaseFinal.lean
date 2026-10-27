module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeCaseProof
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeRCent

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open CFSG.ComponentClassification.AS81.HePres

theorem sec4HeCase_of
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) :
    Sec4HeCase :=
  sec4HeCase_of_cent hE16 h11 (fun _ hd => heRP_class_conj hd) (fun _ hd => heRP_perfect_conj hd)
    (fun _ hd => heRP_card_conj hd)

end CFSG.ComponentClassification.AS81.HeTri
