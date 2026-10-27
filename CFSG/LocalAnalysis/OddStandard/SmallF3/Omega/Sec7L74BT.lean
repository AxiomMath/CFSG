module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Props
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec74_BT_component [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G}
    {z g : G} (hA : Sec74Ass G t L S z g) (hX29 : IsL29 (layerCent L (g⁻¹ * t * g)))
    (hle : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g) :
    IsComponentIn (layerCent L (g⁻¹ * t * g))
      (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) := by
  have hctx := hA.ctx
  have hcomp := isComponentIn_pair_layerCent h36 hctx (Or.inr (Or.inl hX29))
  have hlayerL : layerCent L (g⁻¹ * t * g) ≤ L :=
    (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({g⁻¹ * t * g} : Set G)))).trans
      inf_le_left
  refine hcomp.mono ?_ ?_
  · exact le_inf hle (hlayerL.trans hctx.le_centralizer)
  · exact le_inf inf_le_right (inf_le_left.trans (hctx.conjugate g).le_centralizer)

theorem sec74_BT_shape [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hne : layerCent (CFSG.conjugate L g) t ≠ ⊥) :
    IsOmega5 (layerCent (CFSG.conjugate L g) t) ∨ IsL29 (layerCent (CFSG.conjugate L g) t) ∨
      IsU33 (layerCent (CFSG.conjugate L g) t) ∨ IsL3Eps3 (layerCent (CFSG.conjugate L g) t) := by
  have hctx := hA.ctx
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hctx.isOm6P g
  have hctxg := hctx.conjugate g
  have ht2 : orderOf t = 2 := hctx.involution
  have htC : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hA.comm).symm
  have htne : t ≠ g⁻¹ * t * g := fun h => hA.ne h.symm
  obtain ⟨htN, htnC⟩ := sec7_not_central h36 h72 hctxg ht2 htC htne
  rcases hP.classify G (CFSG.conjugate L g) hLPg t ht2 htN with
    hCc | h4p | h2m | h1a | h3a | hout
  · exact absurd hCc htnC
  · exact absurd ((hP.layer_trivial G (CFSG.conjugate L g) hLPg t ht2 htN).mpr (Or.inl h4p)) hne
  · exact Or.inr (Or.inl (hP.layer_i2 G (CFSG.conjugate L g) hLPg t ht2 htN h2m))
  · exact Or.inl (hP.layer_i1 G (CFSG.conjugate L g) hLPg t ht2 htN h1a)
  · exact absurd ((hP.layer_trivial G (CFSG.conjugate L g) hLPg t ht2 htN).mpr (Or.inr h3a)) hne
  · rcases hP.layer_outer G (CFSG.conjugate L g) hLPg t ht2 htN hout with h3 | h29
    · exact Or.inr (Or.inr (Or.inr h3))
    · exact Or.inr (Or.inl h29)

theorem sec74_BT_layer [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hX29 : IsL29 (layerCent L (g⁻¹ * t * g)))
    (hle : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g) :
    layerCent (CFSG.conjugate L g) t = layerCent L (g⁻¹ * t * g) := by
  have hcomp := sec74_BT_component h36 hA hX29 hle
  have hXle : layerCent L (g⁻¹ * t * g) ≤ layerCent (CFSG.conjugate L g) t :=
    hcomp.le_layerCent
  have hne : layerCent (CFSG.conjugate L g) t ≠ ⊥ := by
    intro hbot
    exact hcomp.ne_bot (le_bot_iff.mp (hXle.trans (le_of_eq hbot)))
  have hshape := sec74_BT_shape h36 h72 hP hA hne
  have hE : IsComponentIn (layerCent (CFSG.conjugate L g) t)
      (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) := isComponentIn_layerCent hshape
  exact (hcomp.eq_of_le hE hXle).symm

theorem sec74_BT_type [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hX29 : IsL29 (layerCent L (g⁻¹ * t * g)))
    (hLg : ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 →
      InducesTypeSome (CFSG.conjugate L g) u 6 1 2 (-1))
    (hlayer : layerCent (CFSG.conjugate L g) t = layerCent L (g⁻¹ * t * g)) :
    InducesTypeSome (CFSG.conjugate L g) t 6 1 2 (-1) := by
  have hctx := hA.ctx
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hctx.isOm6P g
  have hctxg := hctx.conjugate g
  have ht2 : orderOf t = 2 := hctx.involution
  have htC : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hA.comm).symm
  have htne : t ≠ g⁻¹ * t * g := fun h => hA.ne h.symm
  obtain ⟨htN, -⟩ := sec7_not_central h36 h72 hctxg ht2 htC htne
  have hne : layerCent (CFSG.conjugate L g) t ≠ ⊥ := by
    rw [hlayer]
    exact ne_bot_of_shape (Or.inr (Or.inl hX29))
  have hxout : XOut (CFSG.conjugate L g) t = layerCent (CFSG.conjugate L g) t :=
    hP.xout_eq G (CFSG.conjugate L g) hLPg t ht2 htN hne
  refine hP.i4m_of_inv G (CFSG.conjugate L g) hLPg t ht2 htN ?_ ?_
  · rw [hxout, hlayer]
    exact hX29
  · intro u hu hu2
    rw [hxout, hlayer] at hu
    exact hLg u hu hu2

theorem sec74BT_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    (hBX : Sec74BX) : Sec74BT := by
  intro G _ _ t L S z g hA hB
  obtain ⟨hX29, hle, hu⟩ := hBX G t L S z g hA hB
  have hLg : ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 →
      InducesTypeSome (CFSG.conjugate L g) u 6 1 2 (-1) :=
    fun u hu' hu2 => (hu u hu' hu2).2
  exact ⟨sec74_BT_type h36 h72 hP hA hX29 hLg (sec74_BT_layer h36 h72 hP hA hX29 hle),
    sec74_BT_layer h36 h72 hP hA hX29 hle⟩

end CFSG.OddStandard.SmallF3.Omega
