module

public import CFSG.GH74.GLS.Stage1.Main.BrIndex

public section

namespace CFSG.GH74.GLS.Stage1.Main

open CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage2.Local

theorem psp4Extra_of_parts (hII : II4_4_4_center) (h41 : Prop4_1) (h : PSp4TwoClass) : PSp4Extra :=
  fun G _ _ z S q hcen hT L₁ L₂ hp => ⟨psp4_index_thm hII h41 G z S q hT, h G z S q hcen hT L₁ L₂ hp⟩

theorem l4nfExtra_of_parts (hII : II4_4_4_center) (h41 : Prop4_1) (h : L4NFRest) : L4NFExtra :=
  fun G _ _ z S q w ε hcen hT hw hε L₁ L₂ hp =>
    ⟨l4nf_index_thm hII h41 G z S q w hT, h G z S q w ε hcen hT hw hε L₁ L₂ hp⟩

end CFSG.GH74.GLS.Stage1.Main
