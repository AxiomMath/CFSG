module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSolBar

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

@[expose] def barH (G : Type) [Group G] : Subgroup (G ⧸ pPrimeCore 2 G) :=
  centralizer (barZ G : Set (G ⧸ pPrimeCore 2 G))

@[expose] def tY (G : Type) [Group G] : Subgroup (↥(barH G) ⧸ center ↥(barH G)) :=
  ((barY G).subgroupOf (barH G)).map (QuotientGroup.mk' (center ↥(barH G)))

variable {G : Type} [Group G]

theorem barY_le_barH : barY G ≤ barH G := fun y hy => by
  rw [barH, mem_centralizer_iff]
  intro w hw
  exact ((mem_barZ_iff.mp hw).2 y hy).symm

theorem center_barH [Finite G] : center ↥(barH G) = (barZ G).subgroupOf (barH G) := by
  ext ⟨h, hh⟩
  rw [mem_subgroupOf]
  constructor
  · intro hc
    apply centralizer_barY_le
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨y, barY_le_barH hy⟩)
  · intro hz
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp g.2 h hz).symm)

theorem tY_normal : (tY G).Normal := by
  have := barY_normal (G := G)
  exact (Subgroup.Normal.subgroupOf inferInstance (barH G)).map _
    (QuotientGroup.mk'_surjective _)

theorem ker_tY [Finite G] :
    ((QuotientGroup.mk' (center ↥(barH G))).comp
      ((barY G).subgroupOf (barH G)).subtype).ker =
      center ↥((barY G).subgroupOf (barH G)) := by
  ext ⟨⟨y, hyH⟩, hyY⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    center_barH, mem_subgroupOf, mem_center_iff]
  constructor
  · intro hz g
    obtain ⟨⟨g', hgH⟩, hgY⟩ := g
    exact Subtype.ext (Subtype.ext ((mem_barZ_iff.mp hz).2 g' hgY))
  · intro h
    refine mem_barZ_iff.mpr ⟨hyY, fun g' hg' => ?_⟩
    have h1 := h ⟨⟨g', barY_le_barH hg'⟩, hg'⟩
    exact congrArg (fun x : ↥((barY G).subgroupOf (barH G)) => ((x : ↥(barH G)) :
      G ⧸ pPrimeCore 2 G)) h1

noncomputable def tYEquiv [Finite G] :
    ↥((barY G).subgroupOf (barH G)) ⧸ center ↥((barY G).subgroupOf (barH G)) ≃* ↥(tY G) :=
  (QuotientGroup.quotientMulEquivOfEq ker_tY.symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, range_subtype]
      rfl)))

theorem isQuasisimple_barYH [Finite G] (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G)) :
    IsQuasisimple ↥((barY G).subgroupOf (barH G)) :=
  LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe barY_le_barH).symm
    (isQuasisimple_barY hY)

theorem isSimpleGroup_tY [Finite G] (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G)) :
    IsSimpleGroup ↥(tY G) := by
  have := (isQuasisimple_barYH hY).2.1
  exact tYEquiv.symm.isSimpleGroup

theorem tY_nonab [Finite G] (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G)) :
    ∃ a b : ↥(tY G), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := (isQuasisimple_barYH hY).2.2
  refine ⟨tYEquiv a, tYEquiv b, fun h => hab (tYEquiv.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem centralizer_tY [Finite G] (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G)) :
    centralizer (tY G : Set (↥(barH G) ⧸ center ↥(barH G))) = ⊥ := by
  have := barY_normal (G := G)
  have := barZ_normal (G := G)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (center ↥(barH G)) x
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, center_barH, mem_subgroupOf]
  apply centralizer_barY_le
  have : Group.IsPerfect ↥(barY G) := (isQuasisimple_barY hY).1
  have hcomm := commute_of_inv_mul_mem_center (E := barY G) (x := (h : G ⧸ pPrimeCore 2 G))
    (fun e he => (barY_normal).conj_mem e he h) (fun e => by
      have heH : (e : G ⧸ pPrimeCore 2 G) ∈ barH G := barY_le_barH e.2
      have hmem : QuotientGroup.mk' (center ↥(barH G)) (⟨e, heH⟩ : ↥(barH G)) ∈ tY G :=
        ⟨⟨e, heH⟩, e.2, rfl⟩
      have h1 := mem_centralizer_iff.mp hx _ hmem
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, center_barH, mem_subgroupOf] at h1
      have h2 : (e : G ⧸ pPrimeCore 2 G)⁻¹ * (h * e * (h : G ⧸ pPrimeCore 2 G)⁻¹) ∈ barZ G := by
        have h3 := (barZ_normal).conj_mem _ h1 h
        have h4 : (h : G ⧸ pPrimeCore 2 G) *
            (((⟨e, heH⟩ : ↥(barH G)) * h)⁻¹ * (h * (⟨e, heH⟩ : ↥(barH G))) :
              ↥(barH G)) * (h : G ⧸ pPrimeCore 2 G)⁻¹ =
            (e : G ⧸ pPrimeCore 2 G)⁻¹ * (h * e * (h : G ⧸ pPrimeCore 2 G)⁻¹) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rwa [h4] at h3
      exact mem_center_iff.mpr fun g => Subtype.ext ((mem_barZ_iff.mp h2).2 g g.2))
  rw [mem_centralizer_iff]
  intro y hy
  exact (hcomm y hy).symm

theorem genFittingFStar_eq_tY [Finite G] (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G)) :
    Open.genFittingFStar (↥(barH G) ⧸ center ↥(barH G)) = tY G := by
  have := tY_normal (G := G)
  have := isSimpleGroup_tY hY
  exact ClassicalInvolution.genFittingFStar_eq_of_normal_simple (tY G) (tY_nonab hY)
    (centralizer_tY hY)

theorem nonempty_fusionZStar_equiv_tY [Finite G] :
    Nonempty (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G) ≃*
      ↥(tY G)) := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥(GH74.GLS.oPrimeResidual 2 G)
  obtain ⟨eYb⟩ := nonempty_barY_equiv (G := G)
  let e₁ := QuotientGroup.congr _ _ eYb (OuterAutomorphisms.center_map_equiv eYb)
  let eS := (subgroupOfEquivOfLe (barY_le_barH (G := G))).symm
  let e₂ := QuotientGroup.congr _ _ eS (OuterAutomorphisms.center_map_equiv eS)
  exact ⟨((eZ.trans e₁).trans e₂).trans tYEquiv⟩

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
