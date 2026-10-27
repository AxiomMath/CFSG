module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open Standing.Setup42

@[expose] def Harris46QuaternionInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j → ∀ i' j' : ℕ,
        ∀ Q : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i' * z ^ j')), Q.Normal →
          ∀ k : ℕ, 1 ≤ k → IsEmpty (↥Q ≃* QuaternionGroup (2 ^ k))

@[expose] def Harris46SemidihedralInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ)
      (hs : Setting46e t L p f S w z V i j) (i' j' : ℕ),
      (∀ R : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i' * z ^ j')),
        IsSylowOf 2 R (centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i' * z ^ j') :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i' * z ^ j')))) →
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n)) →
      ∀ J : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i' * z ^ j')), IsComponent J →
        J ≤ centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i' * z ^ j') :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i' * z ^ j'))) →
        ⁅J, zpowers (hs.setup.tBar i' j')⁆ ≠ J

end CFSG.ComponentClassification.HarrisLit
