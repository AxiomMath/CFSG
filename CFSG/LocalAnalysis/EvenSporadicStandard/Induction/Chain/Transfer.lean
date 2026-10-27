module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp31

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem map_oddCore_le {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) :
    (CFSG.oddCore A).map e.toMonoidHom ≤ CFSG.oddCore B := by
  have hN : ((CFSG.oddCore A).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.surjective
  have hodd : Odd (Nat.card ((CFSG.oddCore A).map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact odd_card_oddCore' A
  exact le_sSup ⟨hN, hodd⟩

theorem map_oddCore_eq {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) :
    (CFSG.oddCore A).map e.toMonoidHom = CFSG.oddCore B := by
  have : Finite B := Finite.of_equiv A e.toEquiv
  refine le_antisymm (map_oddCore_le e) fun x hx => ?_
  have h1 : e.symm x ∈ CFSG.oddCore A := map_oddCore_le e.symm ⟨x, hx, rfl⟩
  exact ⟨e.symm x, h1, by simp⟩

theorem isK_quot_of_equiv {IsK : GroupClass} (hinv : IsK.IsoInv) {A B : Type} [Group A] [Group B]
    [Finite A] (e : A ≃* B) (h : IsK (A ⧸ CFSG.oddCore A)) : IsK (B ⧸ CFSG.oddCore B) :=
  hinv _ _ (QuotientGroup.congr _ _ e (map_oddCore_eq e)) h

noncomputable def cqEquivOfEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

end CFSG.EvenSporadicStandard.Induction
