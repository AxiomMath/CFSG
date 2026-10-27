module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHL2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHL33
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHOrthBridge
public import Certificates.Certificate442375

public section

namespace CFSG.OddStandard.SmallF3.Omega


theorem asc82FactO3Cent_holds : Asc82FactO3Cent := by
  intro A _ _ H hH hC hS a ha
  have ha2 : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha, pow_two] at h
  rcases hS with hΩ | h92 | h81 | h33 | hu33
  · exact fh_f1_of_autOddFree H hC (fh_autOddFree_of_smallF3Omega hΩ) ha
  · exact fh_f1_of_fixedO3Free H (fh_fixedO3Free_psl2 h92) ha2
  · exact fh_f1_of_fixedO3Free H (fh_fixedO3Free_psl2 h81) ha2
  · exact fh_f1_of_fixedO3Free H
      (fh_fixedO3Free_L33 h33 Certificates.certificate442375) ha2
  · exact fh_f1_of_autOddFree H hC (fh_autOddFree_psu3 hu33) ha

end CFSG.OddStandard.SmallF3.Omega
