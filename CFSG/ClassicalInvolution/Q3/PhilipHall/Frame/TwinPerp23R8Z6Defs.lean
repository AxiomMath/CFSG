module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Pkg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Balance



section E8ZSix

@[expose] def P23E8ZCE (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ Q : Subgroup Y, IsPGroup 2 Q →
          Q ≤ Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y) → Nat.card Q ≤ 2

@[expose] def P23E8ZX (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ Z : Subgroup Y, I1In R t e Z →
          I1Six t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) →
          oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥ →
          ¬ Subgroup.centralizer ({e} : Set Y) ≤ Z ⊔ rLayer (Om R) e →
          ∀ T A : Subgroup Y, T ≤ Z ⊔ rLayer (Om R) e → Nat.card T = 512 → A ≤ T →
            Solomon73.IsE64 A → (∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) →
              ∃ X : Subgroup Y, X ≤ Subgroup.normalizer (A : Set Y) ∧
                (∀ g ∈ Subgroup.normalizer (A : Set Y), X.map (MulAut.conj g).toMonoidHom = X) ∧
                ∃ ν : ↥X →* ↥Solomon73.Yamaki.N0, Function.Surjective ν ∧
                  Nat.card ν.ker ≤ 2 ∧ ν.ker ≤ Subgroup.center ↥X

@[expose] def P23E8ZSix (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ Z : Subgroup Y, I1In R t e Z →
          oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ →
            ∃ T : Sylow 2 Y, (T : Subgroup Y) ≤ Z ⊔ rLayer (Om R) e ∧ t ∈ (T : Subgroup Y) ∧
              ∀ x ∈ (T : Subgroup Y), t * x = x * t

end E8ZSix

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
