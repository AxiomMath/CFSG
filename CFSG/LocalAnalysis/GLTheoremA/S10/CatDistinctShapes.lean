module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112EvenOrd

public section

namespace CFSG.Quasithin.H13.EvenOrd

theorem excl_360 : Excl 360 :=
  Excl.of_profile (a := 3) (r := 45) ⟨22, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

end CFSG.Quasithin.H13.EvenOrd

end
