module

public import CFSG.GH74.GLS.IVK.Lifted32.Main
public import CFSG.GH74.GLS.IVK.Prod32.Main

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5

theorem ivk_3_2_lifted_thm (hII : II4_4_4_center)
    (h44 : CFSG.GH74.GLS.Stage1.Thm2.Recip.II4_44) (h2A7 : IVK.Lifted.II4_2A7) : IVK_3_2_lifted :=
  ivk_3_2_lifted_of_abstract hII h44 h2A7 (ivk_3_2_abstract_thm h2A7)

end CFSG.GH74.GLS.IVK.Lifted32
