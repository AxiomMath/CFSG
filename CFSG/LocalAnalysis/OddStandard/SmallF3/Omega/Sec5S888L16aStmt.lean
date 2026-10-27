module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def Asc82Lemma511CSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A →
      ∀ x ∈ S ⊓ centralizer (L : Set G),
        x ∈ zpowers t ∨ (x ∈ normalizer (A : Set G) ∧ ⁅A, zpowers x⁆ = zpowers t)

end CFSG.OddStandard.SmallF3.Omega
