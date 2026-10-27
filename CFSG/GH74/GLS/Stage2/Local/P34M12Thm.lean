module

public import CFSG.GH74.GLS.Stage2.Local.P34M12Main

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34M12

open CFSG.GH74.GLS.Stage12

theorem m12Card_thm : M12Card := fun _ _ _ _ _ ctx => (stage1M12_of_ctx ctx).card_zW

theorem prop34M12_thm : P34.Prop34M12 := prop34M12_of_card m12Card_thm

end CFSG.GH74.GLS.Stage2.Local.P34M12
