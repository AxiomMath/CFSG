module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.ComponentClassification.AschbacherKnownGroup

@[expose] def WeaklyClosedInNormalizer {G : Type*} [Group G] (Z : Subgroup G) : Prop :=
  ∀ h : G, Z.map (MulAut.conj h).toMonoidHom ≤ normalizer (Z : Set G) →
    Z.map (MulAut.conj h).toMonoidHom = Z

@[expose] def InZStar {G : Type*} [Group G] (z : G) : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧ ∀ g : G, g * z * g⁻¹ * z⁻¹ ∈ N

@[expose] def Asc76Lemma25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G), orderOf x = 4 →
    WeaklyClosedInNormalizer (zpowers x) →
    InZStar (x ^ 2) ∨
      HasDihedralSylowTwo (normalClosure {x ^ 2} : Subgroup G) ∨
      HasSemidihedralSylowTwo (normalClosure {x ^ 2} : Subgroup G)

end CFSG.EvenSporadicStandard.Finkelstein77
