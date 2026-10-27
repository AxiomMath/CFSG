module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem centralizer_pair_le_right_clB (x y : G) :
    centralizer ({x, y} : Set G) ≤ centralizer ({y} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp))

private theorem le_centralizer_pair_clB {K : Subgroup G} {x y : G}
    (hx : K ≤ centralizer ({x} : Set G)) (hy : K ≤ centralizer ({y} : Set G)) :
    K ≤ centralizer ({x, y} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rcases hw with rfl | hw
  · exact Subgroup.mem_centralizer_iff.mp (hx hz) _ (Set.mem_singleton _)
  · rw [Set.mem_singleton_iff.mp hw]
    exact Subgroup.mem_centralizer_iff.mp (hy hz) _ (Set.mem_singleton _)

theorem sec4FCl_claimB [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G t L S z) {g : G} (hgc : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    {X : Subgroup G} (hX : IsComponentIn X (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)))
    (hXl : LieModel (X ⧸ oddCore X) .PSL 4 3 1) (hXL' : X ≤ CFSG.conjugate L g) :
    InducesTypeSome (CFSG.conjugate L g) t 7 1 6 1 := by
  let s : G := g⁻¹ * t * g
  let L' : Subgroup G := CFSG.conjugate L g
  have hctx' : Sec4Ctx G s L' (CFSG.conjugate S g) (g⁻¹ * z * g) := hctx.conjugate g
  have hS' : Sec3SettingLB G s L' := hctx'.toSec3SettingLB
  have hL' : IsOmega7Group L' := sec4_isOmega7Group hctx'.toSec4Setting
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hgc
  have htcs : t ∈ centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst.symm
  have hconj : CFSG.conjugate L' t = L' := conjugate_eq_self_of_lemma36 h36 hS' t htcs
  have hsn : t ∈ normalizer (L' : Set G) := mem_normalizer_of_conjugate_eq hconj
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hctx.involution, pow_two] at h
  have hs1 : t ∉ centralizer (L' : Set G) := by
    intro htcent
    have hL't : L' ≤ centralizer ({t} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp htcent x hx)
    have hpair : L' ≤ centralizer ({t, s} : Set G) :=
      le_centralizer_pair_clB hL't hS'.component.le
    have hL'c : IsComponentIn L' (centralizer ({t, s} : Set G)) :=
      hS'.component.mono hpair (centralizer_pair_le_right_clB t s)
    have hX' : IsComponentIn X (centralizer ({t, s} : Set G)) :=
      sec4FCl_isComponentIn_pair hctx.component hX
    have hXeq : X = L' := IsComponentIn.eq_of_le hX' hL'c hXL'
    have hcX : ctrQ X = 6065280 := ctrQ_of_l43 hX.isQuasisimple hXl
    have hcL : ctrQ L' = 4585351680 := ctrQ_of_omega7 hL'.1 hL'.2
    rw [hXeq] at hcX
    rw [hcX] at hcL
    exact (by norm_num : (6065280 : ℕ) ≠ 4585351680) hcL
  have hKs : X ≤ centralizer ({t} : Set G) :=
    hX.le.trans (inf_le_left.trans hctx.component.le)
  have h13 : 13 ∣ ctrQ X := by
    rw [ctrQ_of_l43 hX.isQuasisimple hXl]
    norm_num
  exact sec4FCl_inducesTypeSome_of_dvd hL' hsn ht2 hs1 hXL' hKs h13

end CFSG.OddStandard.SmallF3.Omega
