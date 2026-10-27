module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Eight
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111InputsB4

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82InputDihSd_of_certificates
    : Asc82InputDihSd := by
  intro E _ _ D hD h8 hcl P hP
  exact CFSG.ComponentClassification.Foote5.Asc25.dihedral_or_semidihedral hD h8 hcl hP

end CFSG.OddStandard.SmallF3.Omega
