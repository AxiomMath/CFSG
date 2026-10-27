module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64Slot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64Aut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc

namespace E64

theorem e64AutModel_of_cert : E64AutModel :=
  ⟨E64Aut.center_e64Sub_eq_bot, fun θ _ hα h hT hF => E64Aut.e64_aut_eq_conj θ hα h hT hF⟩

end E64


theorem discUZetaTriAt_e64 {n : ℕ} :
    DiscUZetaTriAt n shapeE64 :=
  E64.discUZetaTriAt_e64_of_model E64.e64AutModel_of_cert

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
