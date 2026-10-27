module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual3
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKD

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem ih8MuTableSect_proved : Ih8MuTableSect p f :=
  ih8MuTableSect_of_d4Star ih8D4Star

theorem ih8MuTable_proved : Ih8MuTable p f :=
  ih8MuTable_of_d4Star ih8D4Star

end CFSG.ClassicalInvolution.Asc77
