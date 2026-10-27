module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FN
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FW

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_g2two_fix_ch615_F4
    (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  obtain ⟨g₂⟩ := nonempty_g2Two_commutator_equiv hK
  have hdl := dLemmaFacts_u33_ch615 (e.trans (g₂.trans u33EquivSubG2.symm))
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := isSimpleGroup_u33Pres
    exact (e.trans (g₂.trans u33EquivSubG2.symm)).isSimpleGroup
  exact c.false_of_case1_dLemma_fix_ch615_F4 h432 hU hN hdl
    (center_of_isSimpleGroup_ch615 hs hdl.1) hfix

end Cx615C

end CFSG.Quasithin.H13
