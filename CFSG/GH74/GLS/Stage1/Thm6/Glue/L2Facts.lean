module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Main
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.IVK.A7.Glue
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12hc
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma12k
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma14j
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.Statements
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

theorem ivkL2Facts_of_proved
    (hgen : IVK.IVK_1_2_general) (h13fc : IVK.IVK_1_3f_c) : IVKL2Facts :=
  ⟨hgen, IVK.ivk_1_2a_struct, IVK.ivk_1_2c, IVK.ivk_1_2d, IVK.ivk_1_2e, IVK.ivk_1_2f, IVK.ivk_1_2g,
    IVK.ivk_1_2h_c, IVK.ivk_1_3f_a, IVK.ivk_1_3f_b, h13fc, IVK.ivk_1_4a, IVK.ivk_1_4j⟩

end CFSG.GH74.GLS.Stage1.Thm6.Glue
