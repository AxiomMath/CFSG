module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Comp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvOut

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem ivk73_empty_of_comp_top
    {P : (X : Type) → [Group X] → Prop}
    (hOut : ∀ (L : Type) [Group L] [Finite L], P L → Nat.card (Outer L) ≤ 2)
    (htop : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      ∃ (C₀ : Type) (_ : Group C₀) (_ : Finite C₀) (_ : ↥(centralizer ({y} : Set L)) ≃* C₀),
        ∀ K : Subgroup C₀, IsComponent K → K = ⊤) :
    Ivk73Empty P := by
  intro N _ _ L K Q h hL
  refine h.false_of_comp_mem (GHInv.hOut_of_card_outer_le_two (hOut ↥L hL))
    fun y hy2 hy1 B hB => ?_
  obtain ⟨C₀, _, _, φ, hC₀⟩ := htop ↥L hL y hy2 hy1
  have hmap := hC₀ _ (LocalCores.isComponent_map_mulEquiv φ hB.2)
  have htop' : B.subgroupOf (centralizer ({y} : Set ↥L)) = ⊤ := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [hmap, Subgroup.map_top_of_surjective _ φ.surjective]
  have hy : (⟨y, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({y} : Set ↥L))) ∈
      B.subgroupOf (centralizer ({y} : Set ↥L)) := by
    rw [htop']
    exact Subgroup.mem_top _
  exact hy

end CFSG.GH74.GLS.IVK
