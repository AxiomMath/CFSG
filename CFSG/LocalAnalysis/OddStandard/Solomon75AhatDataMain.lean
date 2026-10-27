module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataBalance
public import Certificates.Certificate6119
public import Certificates.Certificate6120
public import Certificates.Certificate6121
public import Certificates.Certificate6122

public section

namespace CFSG.OddStandard.Solomon75

open AhatData

theorem coverSylowData_eight_of_certificate :
    CoverSylowData 8 :=
  AhatData.coverSylowData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6119.1) Certificates.certificate6119.2.1

theorem alternatingBalanceData_eight_of_certificate :
    AlternatingBalanceData 8 :=
  AhatData.alternatingBalanceData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6119.1)
    (by simpa using Certificates.certificate6119.2.2)

theorem coverSylowData_nine_of_certificate :
    CoverSylowData 9 :=
  AhatData.coverSylowData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6120.1) Certificates.certificate6120.2.1

theorem alternatingBalanceData_nine_of_certificate :
    AlternatingBalanceData 9 :=
  AhatData.alternatingBalanceData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6120.1)
    (by simpa using Certificates.certificate6120.2.2)

theorem coverSylowData_ten_of_certificate :
    CoverSylowData 10 :=
  AhatData.coverSylowData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6121.1) Certificates.certificate6121.2.1

theorem alternatingBalanceData_ten_of_certificate :
    AlternatingBalanceData 10 :=
  AhatData.alternatingBalanceData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6121.1)
    (by simpa using Certificates.certificate6121.2.2)

theorem coverSylowData_eleven_of_certificate :
    CoverSylowData 11 :=
  AhatData.coverSylowData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6122.1) Certificates.certificate6122.2.1

theorem alternatingBalanceData_eleven_of_certificate :
    AlternatingBalanceData 11 :=
  AhatData.alternatingBalanceData_of_good (by norm_num) (by norm_num)
    (by simpa using Certificates.certificate6122.1)
    (by simpa using Certificates.certificate6122.2.2)

end CFSG.OddStandard.Solomon75
