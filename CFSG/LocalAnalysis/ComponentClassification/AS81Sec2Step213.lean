module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SCoord

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4
open scoped Pointwise

namespace Sec2

open Equiv

section Three

local instance decEqPerm5' : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

local instance decMemAlt5' :
    DecidablePred (fun σ : Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Perm.sign.decidableMemKer

@[expose] def ThreeData (β : Perm (Fin 5)) : Prop :=
  β ∈ alternatingGroup (Fin 5) → β ^ 3 = 1 → β ≠ 1 →
    (∃ ι : Perm (Fin 5), ι ∈ alternatingGroup (Fin 5) ∧ ι * β * ι⁻¹ = β⁻¹) ∧
      ∃ i j : Fin 5, act β (pair i j) ≠ pair i j

local instance (β : Perm (Fin 5)) : Decidable (ThreeData β) := by
  unfold ThreeData
  infer_instance

end Three

theorem act₂_add (σ : Perm (Fin 5)) (m m' : Pair) : act₂ σ (m + m') = act₂ σ m + act₂ σ m' :=
  rfl

theorem act₂_mul (σ τ : Perm (Fin 5)) (m : Pair) : act₂ σ (act₂ τ m) = act₂ (σ * τ) m := by
  simp only [act₂, act_mul]

theorem act₂_one (m : Pair) : act₂ 1 m = m := rfl

variable {G : Type} [Group G] {S Z H : Subgroup G}

theorem Coord.Ψ_conj_S (C : Coord S Z H) (hS : Special S Z) {s u : G} (hs : s ∈ S)
    (hu : u ∈ S) : C.Ψ (s * u * s⁻¹) = C.Ψ u := by
  have e : s * u * s⁻¹ = (s * u * s⁻¹ * u⁻¹) * u := by group
  rw [e, C.Ψ_mul hS (hS.le (hS.comm_mem hs hu)) hu,
    (C.Ψ_eq_zero_iff hS (hS.le (hS.comm_mem hs hu))).mpr (hS.comm_mem hs hu), zero_add]

end Sec2

open Sec2

end CFSG.ComponentClassification.AS81
