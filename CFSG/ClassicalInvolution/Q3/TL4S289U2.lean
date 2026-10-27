module

public import CFSG.ClassicalInvolution.Q3.TL4S289Exit

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

@[expose] def ExitIdentF (X : Type) [Group X] : Prop :=
  IsSimpleGroup ↥(genFittingFStar X) ∧ (genFittingFStar X).index ∣ 6 ∧
    ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
      (LieModel (FStarQuot X) .PSL 3 p f ∨ LieModel (FStarQuot X) .PSU 3 p f)) ∨
      NativeSporadic.IsSporadic (FStarQuot X) .M12)

@[expose] def SecIdExitS3IdentF (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → SecIdExitS3 Φ → ExitIdentF X

@[expose] def SecIdExitDich3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → SecIdExitS3 Φ → ExitIdentF X →
      ∀ M ∈ Φ, ∀ a : X, IsUniqueInvolution M a → ∀ P : Subgroup X, IsSylow2In P M →
        ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a

namespace S289

variable {X : Type} [Group X] [Finite X]

theorem exitIdentF_of_datum (hL2 : SecIdE3L2NoStar)
    {Φ : Set (Subgroup X)} (hst : ∃ L ∈ Φ, (omegaStarNbr Φ L).Nonempty)
    {R : Subgroup X} {S : Sylow 2 R} {z : X} (hm : EdgelessMember3 R S z)
    (heq : CoreAssembly.conjClass (tightCore R) = Φ)
    (hout : (¬ TightActs3 R z ∧ (Thm6Exit X ∨ TightTwisted X z)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))
    (hsimp : IsSimpleGroup ↥(genFittingFStar X)) (hidx : (genFittingFStar X).index ∣ 6)
    (hntw : ¬ TightTwisted X z) : ExitIdentF X := by
  refine ⟨hsimp, hidx, ?_⟩
  rcases hout with ⟨-, hX | hX⟩ | he
  · rcases hX with ⟨p, f, hp, hp2, ⟨hf, hk, hidx2⟩ | ⟨hk, -⟩⟩ | ⟨hk, -⟩
    · exfalso
      obtain ⟨L, hL, hne⟩ := hst
      have h1 := hL2 X R S z hm hsimp hidx2 p f hp hp2 hf hk L (heq ▸ hL)
      rw [heq] at h1
      rw [h1] at hne
      exact Set.not_nonempty_empty hne
    · exact Or.inl ⟨p, f, hp, hp2, hk⟩
    · exact Or.inr hk
  · exact absurd hX hntw
  · obtain ⟨e⟩ := he
    exact Or.inr (isSporadic_fstarQuot_of_center_quot hsimp e)

end S289

theorem secIdExitS3IdentF_of (hE3 : SecIdE3MuS3)
    (hL2 : SecIdE3L2NoStar) (n : ℕ) (h6 : Thm6RBelow 3 n) : SecIdExitS3IdentF n := by
  intro X _ _ hX Φ _ _ _ _ h
  obtain ⟨hed, hst, R, S, z, hm, heq, hO2, hout⟩ := h
  have hmu : MuS3Member R := fun W hW => Q3T6.Mu.muIsoS3_of_shape hm.datum.partIHypG hW
    (heq ▸ hed) (heq ▸ hst)
  obtain ⟨hsimp, hidx, hntw⟩ :=
    hE3 X (fun Y _ _ hY => h6 Y (hY.trans hX)) R S z hm hmu hO2 hout
  exact S289.exitIdentF_of_datum hL2 hst hm heq hout hsimp hidx hntw

end CFSG.ClassicalInvolution.Q3.TL4
