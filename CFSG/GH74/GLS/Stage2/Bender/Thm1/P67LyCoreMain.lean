module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Ly
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultArith

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore

open Subgroup CFSG CFSG.Blueprint

@[expose] def LyCoreAt (r : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], NativeSporadic.IsSporadic Y .Ly →
    ∀ V : Subgroup Y, IsElementaryAbelian r ↥V → Nat.card ↥V = r ^ 2 →
      ∃ g ∈ V, g ≠ 1 ∧
        ∀ W : Subgroup Y, W ≤ Subgroup.centralizer ({g} : Set Y) →
          (∀ c : Y, c * g = g * c → ∀ w ∈ W, c * w * c⁻¹ ∈ W) →
            Nat.Coprime (Nat.card ↥W) r → W = ⊥

theorem lyCentralizerCore_of_three_five (h3 : LyCoreAt 3)
    (h5 : LyCoreAt 5) : LyCentralizerCore := by
  intro Y _ _ hLy r hr hodd V hV hVc
  by_cases hr3 : r = 3
  · subst hr3
    exact h3 Y hLy V hV hVc
  by_cases hr5 : r = 5
  · subst hr5
    exact h5 Y hLy V hV hVc
  exfalso
  obtain ⟨eT⟩ := hLy
  have hcard : Nat.card Y = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hdvd : r ^ 2 ∣ 51765179004000000 := by
    rw [← hcard, ← hVc]
    exact Subgroup.card_subgroup_dvd_card V
  exact LyMult.not_sq_dvd_lyOrder hr hr2 hr3 hr5 hdvd

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore
