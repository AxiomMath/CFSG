module

public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.Blueprint CFSG.CGT.PushingUpLit.BHS6

@[expose] def GInv {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) (A : Subgroup V) : Prop :=
  ∀ g ∈ G, ∀ a ∈ A, g a ∈ A

@[expose] def H1NaturalSL2 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      (∀ A B : Subgroup V, GInv G A → GInv G B → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) →
      IsNatSectionBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
        (x : Multiplicative (Fin 2 → GaloisField 2 n)) =>
          Multiplicative.ofAdd ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (Multiplicative.toAdd x))) G (commV G) (commV G ⊓ fixV G) →
      Nat.card V ≤ 2 ^ n * Nat.card ↥(commV G) ∧ Nat.card ↥(commV G ⊓ fixV G) ≤ 2 ^ n

@[expose] def L2SmallModules : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) →
      (∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤) → Nat.card V ≤ 2 ^ (2 * m) →
      (∀ g ∈ G, ∀ v : V, g v = v) ∨
      IsNatSectionBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))
        (x : Multiplicative (Fin 2 → GaloisField 2 m)) =>
          Multiplicative.ofAdd ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)).mulVec
            (Multiplicative.toAdd x))) G ⊤ ⊥ ∨
      (∃ k : ℕ, m = 2 * k ∧ IsNatSectionBy (omegaMinusAct k) G ⊤ ⊥)

@[expose] def SchurMultL2Two : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E →
    ∀ (Z : Subgroup E) [Z.Normal], Z ≤ Subgroup.center E → IsPGroup 2 ↥Z →
      Nonempty ((E ⧸ Z) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) → Z = ⊥

@[expose] def G23NoSmallFaithful : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 3 1 →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ ρ : L →* MulAut V, Function.Injective ρ → 2 ^ 14 ≤ Nat.card V

end CFSG.CGT.PushingUpLit.CGT6
