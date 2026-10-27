module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.Blueprint

@[expose] def IsLargeAlt (Y : Type) [Group Y] : Prop :=
  ∃ m : ℕ, 9 ≤ m ∧ Nonempty (Y ≃* alternatingGroup (Fin m))

@[expose] def AltComponentLookup : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (W : Subgroup A) [W.Normal], IsSimpleGroup W →
    (∃ x y : W, x * y ≠ y * x) → centralizer (W : Set A) = ⊥ → Catalog W →
    ∀ a : A, orderOf a = 2 → ∀ B : Subgroup A, B ≤ W →
      CFSG.Assembly.IsComponentOf B (centralizer ({a} : Set A)) →
      ∀ m : ℕ, 9 ≤ m → Nonempty (B ≃* alternatingGroup (Fin m)) →
        (∃ N : ℕ, Nonempty (W ≃* alternatingGroup (Fin N))) ∨
          (m = 10 ∧ Nonempty (W ≃* NativeSporadic.HN))

@[expose] def WreathOutcome {X : Type} [Group X] (t : X) (A : Subgroup X) (m : ℕ) : Prop :=
  ∃ K : Subgroup X, CFSG.IsComponent K ∧ K.map (MulAut.conj t).toMonoidHom ≠ K ∧
    CFSG.layer X = K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
    Nonempty (K ≃* alternatingGroup (Fin m)) ∧ (A : Set X) = {g | ∃ k ∈ K, g = k * (t * k * t⁻¹)}

@[expose] def SymOutcome {X : Type} [Group X] (t : X) (m : ℕ) : Prop :=
  ∃ e : Equiv.Perm (Fin (m + 2)) ≃* X, (e.symm t).IsSwap

@[expose] def HNOutcome {X : Type} [Group X] (t : X) : Prop :=
  ∃ W : Subgroup X, W.Normal ∧ W.index = 2 ∧ t ∉ W ∧ Nonempty (W ≃* NativeSporadic.HN)

@[expose] def ExactShapeTrichotomy : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X) (A : Subgroup X) (m : ℕ), 9 ≤ m →
    CFSG.SectionRank.IsKGroupCat X → CFSG.oddCore X = ⊥ → ExactShape t A m →
      t ∈ Subgroup.center X ∨ WreathOutcome t A m ∨ SymOutcome t m ∨ (m = 10 ∧ HNOutcome t)

end CFSG.OddStandard.AltStdSec
