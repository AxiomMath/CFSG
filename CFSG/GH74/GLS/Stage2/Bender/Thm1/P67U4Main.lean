module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnD
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqMain

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

theorem unLeafPlus (n : ℕ) : UnLeafPlus n :=
  fun {_ _ _ _} h hn hp2 {_} hrp hr1 {_ _} hVD h2 h3 =>
    false_of_u_inner_qp1 h hn hp2 hrp hr1 hVD h2 h3

theorem unLeafMinus (n : ℕ) : UnLeafMinus n :=
  fun {_ _ _ _} h hn {_} hrp hrq {_ _} hVD h2 h3 => false_of_u_nonplus h hn hrp hrq hVD h2 h3

theorem cf67U4_thm (hGA : CFSG.Open.GriessAllModelsStatement) :
    CF67U4 :=
  cf67U4_thm_of_leaves (unLeafPlus 4) (unLeafMinus 4) (fun hLie => cf67CoreDeriv_U4_three hLie) hGA

end CFSG.GH74.GLS.Stage2.Bender.Thm1
