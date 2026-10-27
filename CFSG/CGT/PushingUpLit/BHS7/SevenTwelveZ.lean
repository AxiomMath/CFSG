module

public import CFSG.CGT.PushingUpLit.BHS7.SevenEleven
public import CFSG.CGT.PushingUpLit.BHS7.Pending

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem seven_twelve_of_ne (h : MinCex G T) {E H : Subgroup Γ} (hE : E ∈ bStarT G T)
    (hH : IsMaximalSubgroup G H) (hEH : E ⊔ baum T ≤ H)
    (hZ : ⁅vSub G T, zSub T⁆ ≠ ⊥) :
    ∀ x ∈ tZero G T, ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ) := by
  have hL : H ∈ lSet G T :=
    ⟨hH.1, (le_sup_right.trans hEH), fun hle => hE.2 (le_sup_left.trans hEH |>.trans hle)⟩
  have hT0 : tZero G T ≤ H := by
    rw [tZero_of_ne hZ]
    exact (C1GN.omegaOneCenterOf_le_self (baum T)).trans (le_sup_right.trans hEH)
  exact seven_eleven h hE.1.2 hE.2 hL (le_sup_left.trans hEH) hT0

end CFSG.CGT.PushingUpLit.BHS7
