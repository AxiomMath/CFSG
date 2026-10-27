module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Main

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section Generic

variable {G : Type*} [Group G]

@[expose] def IV3_K1 (x : G) (S T P : Subgroup G) : Prop :=
  T.relIndex S = 2 → ∀ V : Subgroup G, V ≤ P → IsFour V →
    (¬ ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) → ∀ s ∈ S, s ∉ T →
      s ∉ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)

theorem iv3_nn_of_K1 {x : G} {S T P : Subgroup G} (h : IV3_K1 x S T P) :
    IV3_12_8c_sylow_nn x S T P := by
  intro hS2 V hVP hV hVn ⟨a, haS, haT, haN⟩
  exact absurd haN (h hS2 V hVP hV hVn a haS haT)

end Generic

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G] {x : G}

@[expose] def IV3K1Leaf (x : G) (Kb : Subgroup (CentralizerBar x)) : Prop :=
  Conf12B G x Kb → ∀ [Kb.Normal] {F : Type} [Field F] [Finite F] (e : ↥Kb ≃* IVK.L2 F)
    (N : IVK.L2Notation e) (S : Subgroup G), IsSylow2In S ⊤ → SitFacts x Kb e N (S ⊓ Cx x) →
      IV3_K1 x S (S ⊓ Cx x) (Pg x Kb (S ⊓ Cx x))

theorem IV3K1Leaf.sylowLeaf {Kb : Subgroup (CentralizerBar x)} (h : IV3K1Leaf x Kb) :
    IV3SylowLeaf x Kb := by
  intro c _ F _ _ e N S hS hsit
  exact iv3_nn_of_K1 (h c e N S hS hsit)

end CFSG.GH74.GLS.Stage1.Thm6.Glue
