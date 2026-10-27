module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint

namespace E3S3O

@[expose] def SigmaFixOm3 (S : Type) [Group S] : Prop :=
  ∀ (A B : Subgroup S) (r : S) (x : MulAut S), QuatTwinDatum A r →
    (∃ q ∈ Subgroup.centralizer ({r} : Set S), conjSub q A = B) → B ≠ A → x * x = 1 →
      (∀ a ∈ A, x a = a) → (∃ w ∈ B, orderOf w = 4 ∧ ∀ b ∈ B, x b = w * b * w⁻¹) →
      (∀ C ∈ CoreAssembly.conjClass A, (∀ c ∈ C, x c = c) → C ≠ A →
        ¬ C ≤ Subgroup.normalizer (A : Set S)) →
        LieModel ↥(sigmaFixGen A x) .PSU 3 3 1 ∧
          ∀ C ∈ CoreAssembly.conjClass A, (∀ c ∈ C, x c = c) →
            ∃ y ∈ sigmaFixGen A x, conjSub y C = C ∧ y ^ 3 = 1 ∧ ∃ c ∈ C, y * c ≠ c * y

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
