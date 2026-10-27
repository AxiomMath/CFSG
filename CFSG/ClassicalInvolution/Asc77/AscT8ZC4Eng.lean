module

public import CFSG.ClassicalInvolution.Asc77.AscIHLie
public import CFSG.ClassicalInvolution.Asc77.AscE184Graph
public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8ZZ

section Link

variable {X : Type} [Group X] {Ψ : Set (Subgroup X)} {k : Subgroup X}

@[expose] def linkFamE (Ψ : Set (Subgroup X)) (k : Subgroup X) : Set (Subgroup X) :=
  {B | B ∈ Ψ ∧ B ≠ k}

@[expose] def linkGenE (Ψ : Set (Subgroup X)) (k : Subgroup X) : Subgroup X :=
  omegaGen (linkFamE Ψ k)

variable [Finite X]

theorem link_pathE
    (hiff : ∀ {J K : Subgroup X}, J ∈ linkFamE Ψ k →
      (J ∈ omegaNbr (linkFamE Ψ k) K ↔ J ∈ omegaNbr Ψ K))
    (hconn : DConnected (restrictFamily (linkFamE Ψ k) (linkGenE Ψ k))) {B₀ B : Subgroup X}
    (hB₀ : B₀ ∈ linkFamE Ψ k) (hB : B ∈ linkFamE Ψ k) :
    Relation.ReflTransGen
      (fun A C => C ∈ linkFamE Ψ k ∧ (C ∈ omegaNbr Ψ A ∨ A ∈ omegaNbr Ψ C)) B₀ B := by
  set H := linkGenE Ψ k with hH
  have hLH : ∀ {A : Subgroup X}, A ∈ linkFamE Ψ k → A ≤ H := fun hA => le_omegaGen hA
  have hpath := hconn _ (subgroupOf_mem_restrictFamily hB₀ (hLH hB₀)) _
    (subgroupOf_mem_restrictFamily hB (hLH hB))
  have key : ∀ U : Subgroup ↥H, Relation.ReflTransGen
      (fun M N : Subgroup ↥H => N ∈ restrictFamily (linkFamE Ψ k) H ∧
        dAdj (restrictFamily (linkFamE Ψ k) H) M N) (B₀.subgroupOf H) U →
      ∃ A ∈ linkFamE Ψ k, U = A.subgroupOf H ∧ Relation.ReflTransGen
        (fun A C => C ∈ linkFamE Ψ k ∧ (C ∈ omegaNbr Ψ A ∨ A ∈ omegaNbr Ψ C)) B₀ A := by
    intro U hU
    induction hU with
    | refl => exact ⟨B₀, hB₀, rfl, Relation.ReflTransGen.refl⟩
    | tail hab hbc ih =>
      obtain ⟨A, hA, rfl, hrt⟩ := ih
      obtain ⟨hcΦ, hadj⟩ := hbc
      obtain ⟨C, hC, hCH, rfl⟩ := hcΦ
      refine ⟨C, hC, rfl, hrt.tail ⟨hC, ?_⟩⟩
      rcases hadj with h | h
      · left
        have h1 := omegaNbr_map h
        rw [Subgroup.map_subgroupOf_eq_of_le hCH,
          Subgroup.map_subgroupOf_eq_of_le (hLH hA)] at h1
        exact (hiff hC).mp h1
      · right
        have h1 := omegaNbr_map h
        rw [Subgroup.map_subgroupOf_eq_of_le hCH,
          Subgroup.map_subgroupOf_eq_of_le (hLH hA)] at h1
        exact (hiff hA).mp h1
  obtain ⟨A, hA, hAeq, hrt⟩ := key _ hpath
  have hAB : A = B := by
    have := Subgroup.subgroupOf_inj.mp hAeq.symm
    rwa [inf_eq_left.mpr (hLH hB), inf_eq_left.mpr (hLH hA)] at this
  rw [← hAB]
  exact hrt

end Link

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
