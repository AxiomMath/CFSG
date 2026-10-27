module

public import CFSG.CGT.Foote82.T66.Perm310
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Glauberman

public section

namespace CFSG.CGT.Foote82

open CFSG.RankThree.PartTwo

@[expose] def SchurAltLift : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (m : ℕ), 8 ≤ m → ∀ π : E →* Equiv.Perm (Fin m),
    π.range = alternatingGroup (Fin m) → ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ →
      π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
      ∀ (L : Subgroup E) (F : Set (Fin m)), 4 ≤ F.ncard → L.map π = altOn F →
        (∀ x ∈ L, π x = 1 → x = 1) → π.ker = ⊥

@[expose] def SchurU42Lift : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(omegaMinusTwo 2)), Function.Surjective π →
    ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ → π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
      ∀ L : Subgroup E, Nonempty (↥(L.map π) ≃* alternatingGroup (Fin 6)) →
        (∀ x ∈ L, π x = 1 → x = 1) → π.ker = ⊥

@[expose] def GlaubermanF : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ n : ℕ, 6 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      (∃ m : ℕ, 3 ≤ m ∧ Nonempty (X ≃* ↥(omegaPlusTwo m))) ∨
      (∃ m : ℕ, 2 ≤ m ∧ Nonempty (X ≃* ↥(omegaMinusTwo m)))) →
    CFSG.CGT.PushingUpLit.CGT6.Nine7.GlaubermanAt X

end CFSG.CGT.Foote82
