module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Fam

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG CFSG.Blueprint

@[expose] def CF67M11 : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .M11
@[expose] def CF67M12 : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .M12
@[expose] def CF67M22 : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .M22
@[expose] def CF67M23 : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .M23
@[expose] def CF67J2 : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .J2
@[expose] def CF67J3 : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .J3
@[expose] def CF67McL : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .McL
@[expose] def CF67Ly : Prop := CF67Fam fun Y _ => NativeSporadic.IsSporadic Y .Ly

theorem cf67Spor_of_parts (h11 : CF67M11) (h12 : CF67M12) (h22 : CF67M22) (h23 : CF67M23)
    (h2 : CF67J2) (h3 : CF67J3) : CF67Spor := by
  intro N _ _ J hJ hY r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  rcases hY with h | h | h | h | h | h
  · exact h11 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact h12 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact h22 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact h23 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact h2 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact h3 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3

theorem cf67McLy_of_parts (hM : CF67McL) (hL : CF67Ly) : CF67McLy := by
  intro N _ _ J hJ hY r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  rcases hY with h | h
  · exact hM N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hL N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3

end CFSG.GH74.GLS.Stage2.Bender.Thm1
