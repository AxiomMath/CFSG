module

public import CFSG.ClassicalInvolution.Q3.Q3SMain
public import Certificates.Certificate270000

public section

namespace CFSG.ClassicalInvolution.Q3

theorem j2_witness_check : j2WitnessCheck = true := Certificates.certificate270000.1

theorem j3_witness_check : j3WitnessCheck = true := Certificates.certificate270000.2

theorem sectionalFourNonLie3_proved : SectionalFourNonLie3 :=
  sectionalFourNonLie3_of_checks j2_witness_check j3_witness_check

end CFSG.ClassicalInvolution.Q3
