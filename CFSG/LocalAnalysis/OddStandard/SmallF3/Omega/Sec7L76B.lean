module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Fink5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74BT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Symm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem layerCent_le (L : Subgroup G) (s : G) : layerCent L s ≤ L :=
  (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)))).trans inf_le_left

theorem sec76_layer_eq [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    (hO : Asc82Outside) {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hα : ∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 1 1 α) :
    layerCent (CFSG.conjugate L g) t = layerCent L (g⁻¹ * t * g) ∧
      ∃ β : ℤˣ, InducesTypeSome (CFSG.conjugate L g) t 6 1 1 β := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := hA.orderOf_s
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) := hA.s_mem_normalizer h36
  have hctxg : Sec7Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := hctx.conjugate g
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hLP g
  have hX5 : IsOmega5 (layerCent L (g⁻¹ * t * g)) := hP.layer_i1 G L hLP _ hs2 hsN hα
  have hcomp : IsComponentIn (layerCent L (g⁻¹ * t * g))
      (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := isComponentIn_layerCent (Or.inl hX5)
  have hle : layerCent L (g⁻¹ * t * g) ≤ twoPrimeRes (layerCent L (g⁻¹ * t * g)) :=
    le_twoPrimeRes_of_isQuasisimple hcomp.isQuasisimple
  have hsub : twoPrimeRes (layerCent L (g⁻¹ * t * g)) ≤ CFSG.conjugate L g :=
    hO.thm2L G t L hctx.toSec3SettingLB
      (h72 G t L hctx.toSec3SettingLB hctx.omega6)
      (asc82OddInnerOm6_holds G L (Or.inr (Or.inl hLP))) 1 g hA.comm hA.ne
      (layerCent L (g⁻¹ * t * g)) (Or.inl rfl)
  have hXle' : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g := hle.trans hsub
  have hcomp' : IsComponentIn (layerCent L (g⁻¹ * t * g))
      (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) :=
    (isComponentIn_pair_layerCent h36 hctx (Or.inl hX5)).mono
      (le_inf hXle' ((layerCent_le L (g⁻¹ * t * g)).trans hctx.le_centralizer))
      (le_inf inf_le_right (inf_le_left.trans hctxg.le_centralizer))
  have hXle : layerCent L (g⁻¹ * t * g) ≤ layerCent (CFSG.conjugate L g) t := hcomp'.le_layerCent
  have hne : layerCent (CFSG.conjugate L g) t ≠ ⊥ := by
    intro hbot
    exact hcomp'.ne_bot (le_bot_iff.mp (hXle.trans (le_of_eq hbot)))
  have hshape := sec74_BT_shape h36 h72 hP hA hne
  have hE : IsComponentIn (layerCent (CFSG.conjugate L g) t)
      (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) := isComponentIn_layerCent hshape
  have hEq : layerCent (CFSG.conjugate L g) t = layerCent L (g⁻¹ * t * g) :=
    (hcomp'.eq_of_le hE hXle).symm
  refine ⟨hEq, ?_⟩
  have htC : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hA.comm).symm
  have htne : t ≠ g⁻¹ * t * g := fun h => hA.ne h.symm
  have htN : t ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    (sec7_not_central h36 h72 hctxg hctx.involution htC htne).1
  exact (hP.layer_om5_iff G (CFSG.conjugate L g) hLPg t hctx.involution htN).mp
    (by rw [hEq]; exact hX5)

theorem sec76_caseB [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h74 : Asc82Lemma74)
    (hP : Asc82Tab6P) (hO : Asc82Outside) (hF5 : Asc82Fink5) {t : G} {L S : Subgroup G}
    {z : G} (hctx : Sec7Ctx G t L S z) (hnc : ¬ IsConj t (t * z)) {x : G}
    (hx : x ∈ S ⊓ centralizer (L : Set G)) (hx4 : orderOf x = 4) : False := by
  obtain ⟨g, hg1, hcomm⟩ := hF5 G t L S z hctx x hx hx4
  have hx2 : x * x = t := sec76_sq_eq_t h72 hctx hx hx4
  have hcommt : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
    calc (g⁻¹ * t * g) * t = (g⁻¹ * t * g) * (x * x) := by rw [hx2]
      _ = ((g⁻¹ * t * g) * x) * x := by group
      _ = (x * (g⁻¹ * t * g)) * x := by rw [hcomm.symm]
      _ = x * ((g⁻¹ * t * g) * x) := by group
      _ = x * (x * (g⁻¹ * t * g)) := by rw [hcomm.symm]
      _ = (x * x) * (g⁻¹ * t * g) := by group
      _ = t * (g⁻¹ * t * g) := by rw [hx2]
  have hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcommt
  have hA : Sec74Ass G t L S z g := ⟨hctx, hsC, hg1, hnc⟩
  have hα : ∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 1 1 α :=
    (h74 G t L S z hctx).resolve_left hnc (g⁻¹ * t * g)
      (isConj_iff_inv_mul.mpr ⟨g, rfl⟩) hsC hg1
  obtain ⟨hlayer, β, hβ⟩ := sec76_layer_eq h36 h72 hP hO hA hα
  have hctxg : Sec7Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := hctx.conjugate g
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hctx.isOm6P g
  have htC : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have htne : t ≠ g⁻¹ * t * g := fun h => hg1 h.symm
  have htN : t ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    (sec7_not_central h36 h72 hctxg hctx.involution htC htne).1
  have hxC : x ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hxN : x ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hctxg.cent_le_normalizer h36 x hxC
  have hxZ : x ∈ centralizer ((layerCent (CFSG.conjugate L g) t : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [hlayer] at hh
    exact Subgroup.mem_centralizer_iff.mp hx.2 h (layerCent_le L (g⁻¹ * t * g) hh)
  have hR : zpowers x ≤ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) ⊓
      centralizer ((layerCent (CFSG.conjugate L g) t : Subgroup G) : Set G) :=
    le_inf (Subgroup.zpowers_le.mpr hxN) (Subgroup.zpowers_le.mpr hxZ)
  have hrel : (centralizer ((CFSG.conjugate L g : Subgroup G) :
      Set G)).relIndex (zpowers x) ≤ 2 :=
    hP.aut_cent_i1 G (CFSG.conjugate L g) hLPg t hctx.involution htN ⟨β, hβ⟩ (zpowers x) hR
  have hxx : x * x ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    sq_mem_of_relIndex_le_two hrel (Subgroup.mem_zpowers x)
  have htcent : t ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rwa [hx2] at hxx
  exact hP.nontrivial G (CFSG.conjugate L g) hLPg t hctx.involution htN
    (Or.inr (Or.inr (Or.inl ⟨β, hβ⟩))) htcent

end CFSG.OddStandard.SmallF3.Omega
