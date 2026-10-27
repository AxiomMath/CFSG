module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.MRowExistence
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.EvenSporadicStandard.TwoHS

variable {G : Type} [Group G] [Finite G]

theorem inducedByCentralizer_of_hsCover
    {L K : Subgroup G} {u : G} (hKC : K ≤ L ⊓ centralizer ({u} : Set G))
    (hcov : IsHSCover ↥(L ⊓ centralizer ({u} : Set G))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set G))))
    (hidx : (K.subgroupOf (L ⊓ centralizer ({u} : Set G))).index = 2) :
    InducedByCentralizer L K u := by
  have : (K.subgroupOf (L ⊓ centralizer ({u} : Set G))).Normal := hcov.normal
  exact inducedByCentralizer_of_conjNormal hKC
    (conjNormal_surjective_of_card_le (hcov.card_mulAut_mul_card_centralizer_le hidx))

theorem central_eq_of_hsCover {L K : Subgroup G} {u : G} (huL : u ∈ L) (hu2 : orderOf u = 2)
    (hcov : IsHSCover ↥(L ⊓ centralizer ({u} : Set G))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set G)))) :
    u ∈ K ∧ ∀ c ∈ L, (∀ k ∈ K, c * k = k * c) → c = 1 ∨ c = u := by
  set Cu : Subgroup G := L ⊓ centralizer ({u} : Set G) with hCu
  set E : Subgroup ↥Cu := K.subgroupOf Cu with hE
  let u' : ↥Cu := ⟨u, huL, mem_centralizer_singleton_iff.2 rfl⟩
  have hu'1 : u' ≠ 1 := fun h => by
    have h1 : u = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hu'c : ∀ y : ↥Cu, y * u' = u' * y := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2.2)
  have hu'E : u' ∈ E := hcov.centralizer_le (mem_centralizer_iff.2 fun y _ => hu'c y)
  have hcenU : (⟨u', hu'E⟩ : ↥E) ∈ center ↥E :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (hu'c y)
  have hx1 : (⟨⟨u', hu'E⟩, hcenU⟩ : ↥(center ↥E)) ≠ 1 := fun h => hu'1
    (congrArg (fun w : ↥(center ↥E) => ((w : ↥E) : ↥Cu)) h)
  refine ⟨mem_subgroupOf.1 hu'E, fun c hcL hc => ?_⟩
  have hcu : c * u = u * c := hc u (mem_subgroupOf.1 hu'E)
  have hcC : c ∈ Cu := ⟨hcL, mem_centralizer_singleton_iff.2 hcu⟩
  have hcE : (⟨c, hcC⟩ : ↥Cu) ∈ E := by
    refine hcov.centralizer_le (mem_centralizer_iff.2 fun y hy => ?_)
    exact Subtype.ext (hc _ (mem_subgroupOf.1 hy)).symm
  have hcen : (⟨⟨c, hcC⟩, hcE⟩ : ↥E) ∈ center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subtype.ext (hc _ (mem_subgroupOf.1 y.2)).symm)
  rcases eq_one_or_eq_of_card_eq_two hcov.card_center hx1 ⟨⟨⟨c, hcC⟩, hcE⟩, hcen⟩ with h | h
  · left
    exact congrArg (fun w : ↥(center ↥E) => (((w : ↥E) : ↥Cu) : G)) h
  · right
    exact congrArg (fun w : ↥(center ↥E) => (((w : ↥E) : ↥Cu) : G)) h

end CFSG.EvenSporadicStandard.Solomon78
