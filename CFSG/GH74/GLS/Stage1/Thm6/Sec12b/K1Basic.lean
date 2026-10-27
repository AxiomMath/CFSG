module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_8Aux
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section Generic

variable {G : Type*} [Group G]

@[expose] def IV3_12_8c_sylow_nn (x : G) (S T P : Subgroup G) : Prop :=
  T.relIndex S = 2 → ∀ V : Subgroup G, V ≤ P → IsFour V →
    (¬ ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
    (∃ a ∈ S, a ∉ T ∧
      a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) →
    IsSylow2In (S ⊓ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
      (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))

variable [Finite G] {x : G} {S T P Q Rd F : Subgroup G}

theorem normalIn_E_of_normalizes (h : HBase G x S T P Q Rd F) {V : Subgroup G} (hVP : V ≤ P)
    (hVn : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    NormalIn (V ⊔ Subgroup.zpowers x) T := by
  refine ⟨E_le_T h hVP, fun t ht n hn => ?_⟩
  have hle : V ⊔ Subgroup.zpowers x ≤ Hconj t (V ⊔ Subgroup.zpowers x) := by
    refine sup_le (fun v hv => mem_Hconj.2 (Subgroup.mem_sup_left (hVn t ht v hv)))
      ((Subgroup.zpowers_le).2 (mem_Hconj.2 ?_))
    have hx : t * x * t⁻¹ = x := by
      have := h.x_central t ht
      calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [this]
        _ = x := by group
    rw [hx]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  exact mem_Hconj.1 (hle hn)

theorem iv3_of_nn (h : HBase G x S T P Q Rd F) (hnn : IV3_12_8c_sylow_nn x S T P) :
    IV3_12_8c_sylow x S T P := by
  intro hS2 V hVP hV ⟨a, haS, haT, haN⟩
  by_cases hVn : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V
  · exact sylow_of_normal h haS haT haN (normalIn_E_of_normalizes h hVP hVn) hS2.le
  · exact hnn hS2 V hVP hV hVn ⟨a, haS, haT, haN⟩

end Generic

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
