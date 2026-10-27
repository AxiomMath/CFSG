module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdSyl
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdClaimG

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open CFSG.GH74.GLS.Stage2.Final.Thm6

theorem claimG_closed : ClaimG :=
  fun _ _ _ _ _ _ ctx _ _ _ _ _ hP hidx hK => claimG ctx hP hidx hK

theorem adapter20_9 : Adapter20_9 :=
  adapter20_9_of_claimG claimG_closed

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
