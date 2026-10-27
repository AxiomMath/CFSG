module

public import CFSG.ClassicalInvolution.Asc77.AscAETProved
public import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
public import CFSG.ClassicalInvolution.Asc77.AscFusionS14

public section

namespace CFSG.ClassicalInvolution.Asc77.AscAET

open CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem aEmptyTwinExact_of_fusionCore : AEmptyTwinExact p f :=
  aEmptyTwinExact_proved (hypOmegaModAll_of_fusionCore (AscFusion.fusionCoreStmt p f))

end CFSG.ClassicalInvolution.Asc77.AscAET
