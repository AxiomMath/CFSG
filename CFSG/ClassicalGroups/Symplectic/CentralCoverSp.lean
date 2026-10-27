module

public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Assembly.LowTwoRank

theorem exists_central_cover_sp_of_card_ge_five
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 5 ≤ Q.card) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (π : StatedSp m F →* L),
      Nat.card F = Q.card ∧ Function.Surjective π ∧
      π.ker ≤ Subgroup.center (StatedSp m F) := by
  refine exists_central_cover_sp_of_section hL m hm Q hQ hv e ?_
  intro F _ _ _ hFcard E _ _ π hπ hker
  exact CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central
    (n := m) (F := F) (by omega) (by rw [hFcard]; exact hQcard) hπ hker

end CFSG.ClassicalGroups.Symplectic

end
