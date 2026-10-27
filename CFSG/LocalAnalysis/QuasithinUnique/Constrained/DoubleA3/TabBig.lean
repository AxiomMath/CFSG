module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigKlein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigL217
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigL33
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigM11
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate110
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Rank2
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.DoubleA3

theorem kleinSC_of_kBig
    {G : Type} [Group G] {K : Subgroup G} (h : KBig K) : KleinSC ↥K := by
  rcases h with h | h | h
  · exact kleinSC_of_psl2_17 h
  · exact kleinSC_of_psl33 h
  · exact kleinSC_of_m11 h

theorem card_dvd_of_kBig
    {G : Type} [Group G] {K : Subgroup G} (h : KBig K) :
    16 ∣ Nat.card ↥K := by
  rcases h with h | h | h
  · exact card_dvd_of_psl2_17 h
  · exact card_dvd_of_psl33 h
  · exact card_dvd_of_m11 h

theorem tabBigSylow
    : TabBigSylow := fun _ _ _ _ hK => card_dvd_of_kBig hK

theorem tabBigA4
    : TabBigA4 := by
  intro G _ _ K L U hK hLK hA4 P hPK hP2 hPL
  exact tabBigA4_of_kleinSC (kleinSC_of_kBig hK) hLK hA4 hPK hP2 hPL

end CFSG.QuasithinUnique.DoubleA3
