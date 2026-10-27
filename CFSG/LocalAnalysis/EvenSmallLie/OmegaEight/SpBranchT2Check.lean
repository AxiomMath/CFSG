module

public import Certificates.Certificate3880
public import Certificates.Certificate3881
public import Certificates.Certificate3882
public import Certificates.Certificate3883
public import Certificates.Certificate3884
public import Certificates.Certificate3885
public import Certificates.Certificate3886
public import Certificates.Certificate3887
public import Certificates.Certificate3888
public import Certificates.Certificate3889
public import Certificates.Certificate3890
public import Certificates.Certificate3891
public import Certificates.Certificate3892
public import Certificates.Certificate3893
public import Certificates.Certificate3894
public import Certificates.Certificate3895
public import Certificates.Certificate3896

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem s2Basic_check : s2BasicCheck = true :=
  Certificates.certificate3880.1

theorem l2eSurv_check_0 : ∃ W, l2eSurvOK 0 W = true :=
  Certificates.certificate3880.2.1

theorem l2eSurv_check_1 : ∃ W, l2eSurvOK 1 W = true :=
  Certificates.certificate3880.2.2

theorem l2eSurv_check_2 : ∃ W, l2eSurvOK 2 W = true :=
  Certificates.certificate3881.1

theorem l2eSurv_check_3 : ∃ W, l2eSurvOK 3 W = true :=
  Certificates.certificate3881.2

theorem l2eSurv_check_4 : ∃ W, l2eSurvOK 4 W = true :=
  Certificates.certificate3882.1

theorem l2eSurv_check_5 : ∃ W, l2eSurvOK 5 W = true :=
  Certificates.certificate3882.2

theorem l2eSurv_check_6 : ∃ W, l2eSurvOK 6 W = true :=
  Certificates.certificate3883.1

theorem l2eSurv_check_7 : ∃ W, l2eSurvOK 7 W = true :=
  Certificates.certificate3883.2

theorem l2TH_check_0 : ∃ gs L, l2THOK 0 gs L = true :=
  Certificates.certificate3884.1

theorem l2TH_check_1 : ∃ gs L, l2THOK 1 gs L = true :=
  Certificates.certificate3884.2

theorem l2SurvAct_check_0 :
    ∃ I cents recs, l2SurvActOK 0 I cents recs = true :=
  Certificates.certificate3885

theorem l2SurvAct_check_1 :
    ∃ I cents recs, l2SurvActOK 1 I cents recs = true :=
  Certificates.certificate3886

theorem l2SurvAct_check_2 :
    ∃ I cents recs, l2SurvActOK 2 I cents recs = true :=
  Certificates.certificate3887

theorem l2SurvAct_check_3 :
    ∃ I cents recs, l2SurvActOK 3 I cents recs = true :=
  Certificates.certificate3888

theorem l2SurvAct_check_4 :
    ∃ I cents recs, l2SurvActOK 4 I cents recs = true :=
  Certificates.certificate3889

theorem l2SurvAct_check_5 :
    ∃ I cents recs, l2SurvActOK 5 I cents recs = true :=
  Certificates.certificate3890

theorem l2SurvAct_check_6 :
    ∃ I cents recs, l2SurvActOK 6 I cents recs = true :=
  Certificates.certificate3891

theorem l2SurvAct_check_7 :
    ∃ I cents recs, l2SurvActOK 7 I cents recs = true :=
  Certificates.certificate3892

theorem l2K_check_0 : ∃ gs L, l2KOK 0 gs L = true :=
  Certificates.certificate3893.1

theorem l2K_check_1 : ∃ gs L, l2KOK 1 gs L = true :=
  Certificates.certificate3893.2

theorem l2K_check_2 : ∃ gs L, l2KOK 2 gs L = true :=
  Certificates.certificate3894.1

theorem l2K_check_3 : ∃ gs L, l2KOK 3 gs L = true :=
  Certificates.certificate3894.2

theorem l2K_check_4 : ∃ gs L, l2KOK 4 gs L = true :=
  Certificates.certificate3895.1

theorem l2K_check_5 : ∃ gs L, l2KOK 5 gs L = true :=
  Certificates.certificate3895.2

theorem l2K_check_6 : ∃ gs L, l2KOK 6 gs L = true :=
  Certificates.certificate3896.1

theorem l2K_check_7 : ∃ gs L, l2KOK 7 gs L = true :=
  Certificates.certificate3896.2

end CFSG.EvenSmallLie.OmegaEight.SpBranch
