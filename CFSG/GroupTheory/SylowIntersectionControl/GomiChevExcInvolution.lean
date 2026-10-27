module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

@[expose] def IsGomiChevExceptional (K : Type) [Group K] : Prop :=
  (∃ n f : ℕ, CFSG.Blueprint.LieModel K .Tits n 2 f) ∨
    Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel K .PSU 3 3 1

@[expose] def GomiChevExcInvolution : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G) (z : G), IsGomiChevTwo ↥L →
    IsGomiChevExceptional (↥L ⧸ center ↥L) → IsSylowOf 2 U L →
    z ∈ normalizer (L : Set G) → z ∈ normalizer (U : Set G) → z ∉ centralizer (L : Set G) →
    z ^ 2 ∈ centralizer (L : Set G) →
    (∀ A : Subgroup G, IsGomiAtom L U A → A ⊔ A.map (MulAut.conj z).toMonoidHom ≠ L) →
    pCoreOf 2 (L ⊓ centralizer ({z} : Set G)) ≠ ⊥

end CFSG.GroupTheory
