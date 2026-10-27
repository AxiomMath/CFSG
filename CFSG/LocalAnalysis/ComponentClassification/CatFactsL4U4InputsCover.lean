module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cover82

open CFSG Subgroup

@[expose] def MultiplierL4U4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    (Blueprint.LieModel (Y ⧸ center Y) .PSL 4 p f ∨
      (Blueprint.LieModel (Y ⧸ center Y) .PSU 4 p f ∧ p ^ f ≠ 3)) →
    IsPGroup 2 (center Y)

@[expose] def A10DoubleTransLift : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → center Y ≠ ⊥ →
    ∀ (e : Y ⧸ center Y ≃* alternatingGroup (Fin 10)) (y : Y) (a b c d : Fin 10),
      [a, b, c, d].Nodup →
      ((e (QuotientGroup.mk y) : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) =
        Equiv.swap a b * Equiv.swap c d →
      y ^ 2 ≠ 1

end Cover82

end CFSG.ComponentClassification.CatFactsL4U4
