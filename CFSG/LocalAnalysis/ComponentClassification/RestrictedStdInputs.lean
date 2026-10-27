module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

@[expose] def SmallSource {A : Type} [Group A] (L : Subgroup A) : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ LieModel (L ⧸ center L) .PSL 2 p f ∧
      Odd (Nat.card (center L))) ∨
    (Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧ Odd (Nat.card (center L))) ∨
    LieModel (L ⧸ center L) .PSL 3 2 2

@[expose] def AlmostSimpleRestricted (P : Assembly.GroupProp) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (W : Subgroup A) [W.Normal], IsSimpleGroup W →
    (∃ x y : W, x * y ≠ y * x) → centralizer (W : Set A) = ⊥ → Catalog W → P W →
    ∀ a : A, orderOf a = 2 → ∀ L : Subgroup A, L ≤ W → L ≠ W →
      Assembly.IsComponentOf L (centralizer ({a} : Set A)) → IsStandardSubgroup L →
      SmallSource L → GSRestricted W

@[expose] def OddLinearUnrestricted (Y : Type) [Group Y] : Prop :=
  ∃ n p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ n ∧ LieModel Y .PSL n p f

@[expose] def OddClassicalUnrestricted (Y : Type) [Group Y] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((∃ n, 5 ≤ n ∧ LieModel Y .PSU n p f) ∨ (∃ n, 3 ≤ n ∧ LieModel Y .PSp n p f) ∨
      (∃ n, 3 ≤ n ∧ LieModel Y .POmegaOdd n p f) ∨ (∃ n, 4 ≤ n ∧ LieModel Y .POmegaPlus n p f) ∨
      (∃ n, 5 ≤ n ∧ LieModel Y .POmegaMinus n p f))

@[expose] def EvenOrthogonal (Y : Type) [Group Y] : Prop :=
  ∃ n f : ℕ, 4 ≤ n ∧ 1 ≤ f ∧ (LieModel Y .POmegaPlus n 2 f ∨ LieModel Y .POmegaMinus n 2 f)

@[expose] def ExceptionalChevalley (Y : Type) [Group Y] : Prop :=
  ∃ (t : StatedLieTag) (p f : ℕ), t ∈ chevalleyExceptionalTags ∧ p.Prime ∧ 1 ≤ f ∧
    LieModel Y t 0 p f

@[expose] def restrictedSporadicNames : Finset TauCeti.SporadicName :=
  {.J1, .J2, .J3, .M12, .HS, .He, .ONan, .Suz}

@[expose] def SporadicUnrestricted (Y : Type) [Group Y] : Prop :=
  ∃ s : TauCeti.SporadicName, s ∉ restrictedSporadicNames ∧ NativeSporadic.IsSporadic Y s

end CFSG.ComponentClassification.RestrictedStd
