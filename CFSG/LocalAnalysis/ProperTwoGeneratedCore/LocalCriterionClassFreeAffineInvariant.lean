module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G] [Finite G]

theorem normalized_odd_central_quotient_invariant_sylow
    (p : ℕ) (hp : p.Prime) (J X : Subgroup G) [J.Normal]
    (t : G) (ht : orderOf t = 2) (hJodd : Odd (Nat.card J))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (G ⧸ J)) :
    ∃ P : Sylow p X,
      t ∈ Subgroup.normalizer
        (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let L := X ⊔ Subgroup.zpowers t
  let B := X.subgroupOf L
  let A := B ⊓ J.subgroupOf L
  have htL : t ∈ L := (show Subgroup.zpowers t ≤ L from le_sup_right)
    (Subgroup.mem_zpowers t)
  let tL : L := ⟨t, htL⟩
  have hXL : X ≤ L := le_sup_left
  obtain ⟨hBnormal, hAnormal, hAodd, hAB, _, hAcentral⟩ :=
    normalized_subgroup_odd_central_quotient J X t hJodd hXnorm hcentral
  let : B.Normal := hBnormal
  let : A.Normal := hAnormal
  have htorder : orderOf tL = 2 := (Subgroup.orderOf_coe tL).symm.trans ht
  obtain ⟨P₀, hPnorm⟩ := odd_central_quotient_invariant_sylow_exists
    p hp B A tL htorder hAodd hAB hAcentral
  let e := Subgroup.subgroupOfEquivOfLe hXL
  let P : Sylow p X := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have himage : (P : Subgroup X).map X.subtype =
      ((P₀ : Subgroup B).map B.subtype).map L.subtype := by
    change ((P₀ : Subgroup B).map e.toMonoidHom).map X.subtype = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  refine ⟨P, ?_⟩
  rw [himage]
  exact Subgroup.le_normalizer_map L.subtype
    (Subgroup.mem_map_of_mem L.subtype hPnorm)

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
