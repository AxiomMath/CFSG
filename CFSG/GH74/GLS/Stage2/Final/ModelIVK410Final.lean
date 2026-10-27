module

public import CFSG.GH74.GLS.Stage2.Final.ModelIVK410
public import CFSG.GH74.GLS.Stage2.Final.ModelPGLUni

public section

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem ivk_4_10 : IVK.IVK_4_10 := by
  refine ivk_4_10_of_uniPgl ?_
  intro F _ _ p f _ _ hF hp2 h5 hq4
  exact pglStmt_uni hF hp2 h5 hq4

end CFSG.GH74.GLS.Stage2.Final
