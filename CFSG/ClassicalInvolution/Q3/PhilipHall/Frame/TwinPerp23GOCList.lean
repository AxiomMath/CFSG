module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCSpor
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC

open CFSG.Open

section List


theorem outCyc_of_goldschmidtSimpleType {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (h : goldschmidtSimpleType L) : OutCyc L := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, -, h8, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  · exact outCyc_psl2_even (by omega) e
  · exact outCyc_sz hn e
  · exact outCyc_psu3 hf e
  · exact outCyc_psl2_odd hpo hf h8 e
  · exact outCyc_ree_order hm hcard
  · exact outCyc_goldschmidtJ1 e

theorem isCyclic_map_fstar_of_goldschmidtSimpleType {X : Type} [Group X] [Finite X]
    [IsSimpleGroup ↥(genFittingFStar X)] (hty : goldschmidtSimpleType ↥(genFittingFStar X))
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) :
    letI : (genFittingFStar X).Normal := CFSG.ComponentClassification.GeneralizedFitting.normal X
    IsCyclic ↥(Q.map (QuotientGroup.mk' (genFittingFStar X))) := by
  haveI : (genFittingFStar X).Normal := CFSG.ComponentClassification.GeneralizedFitting.normal X
  exact isCyclic_map_mk_of_outCyc (CFSG.Adapters.generalized_fitting_self_centralizing X)
    (outCyc_of_goldschmidtSimpleType hty) hQ

end List

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
