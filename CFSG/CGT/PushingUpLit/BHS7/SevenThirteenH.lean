module

public import CFSG.CGT.PushingUpLit.BHS7.Seven135Proof
public import CFSG.CGT.PushingUpLit.BHS7.SevenTwelveQSub

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem seven_thirteen_of_inputs (h : MinCex G T) (h5 : Seven5 G T)
    (h7 : Seven7 G T) (h135 : Seven135 G T) : Seven13 G T := by
  have hZ : ⁅vSub G T, zSub T⁆ = ⊥ := by
    by_contra hZ
    exact seven_thirteen_z h h5 h7 h135 hZ
  exact ⟨hZ, fun A hAT hA => branch_q_false h h5 h7 (seven_twelve_q h h5) hZ
    ⟨A, hAT, hA.1, hA.2⟩⟩

theorem sec7Pending_of_seven135
    (h135 : ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T : Subgroup Γ), MinCex G T → Seven135 G T) :
    Sec7Pending :=
  ⟨fun Γ _ _ G T h _ h5 h7 => seven_thirteen_of_inputs h h5 h7 (h135 Γ G T h)⟩

theorem sec7Pending_holds : Sec7Pending :=
  sec7Pending_of_seven135 fun _ _ _ _ _ h => seven_135 h

end CFSG.CGT.PushingUpLit.BHS7
