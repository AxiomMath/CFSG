module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Symm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem layerCent_le (L : Subgroup G) (s : G) : layerCent L s ≤ L :=
  (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)))).trans inf_le_left

theorem sec74_BX_le [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    (hO : Asc82Outside) {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hB : InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1)) :
    IsL29 (layerCent L (g⁻¹ * t * g)) ∧ layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := hA.orderOf_s
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) := hA.s_mem_normalizer h36
  have hX29 : IsL29 (layerCent L (g⁻¹ * t * g)) :=
    hP.layer_i2 G L hLP _ hs2 hsN hB
  refine ⟨hX29, ?_⟩
  have hcomp : IsComponentIn (layerCent L (g⁻¹ * t * g))
      (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) :=
    isComponentIn_layerCent (Or.inr (Or.inl hX29))
  have hle : layerCent L (g⁻¹ * t * g) ≤ twoPrimeRes (layerCent L (g⁻¹ * t * g)) :=
    le_twoPrimeRes_of_isQuasisimple hcomp.isQuasisimple
  have hsub : twoPrimeRes (layerCent L (g⁻¹ * t * g)) ≤ CFSG.conjugate L g :=
    hO.thm2L G t L hctx.toSec3SettingLB
      (h72 G t L hctx.toSec3SettingLB hctx.omega6)
      (asc82OddInnerOm6_holds G L (Or.inr (Or.inl hLP))) 1 g hA.comm hA.ne
      (layerCent L (g⁻¹ * t * g)) (Or.inl rfl)
  exact hle.trans hsub

theorem sec74_BX_typeL [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hB : InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1)) :
    ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 → InducesTypeSome L u 6 1 2 (-1) := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := hA.orderOf_s
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) := hA.s_mem_normalizer h36
  have hX29 : IsL29 (layerCent L (g⁻¹ * t * g)) :=
    hP.layer_i2 G L hLP _ hs2 hsN hB
  have hne : layerCent L (g⁻¹ * t * g) ≠ ⊥ := ne_bot_of_shape (Or.inr (Or.inl hX29))
  have hxout : XOut L (g⁻¹ * t * g) = layerCent L (g⁻¹ * t * g) :=
    hP.xout_eq G L hLP _ hs2 hsN hne
  intro u hu hu2
  have huX : u ∈ XOut L (g⁻¹ * t * g) := by rw [hxout]; exact hu
  exact hP.inv_of_i4m G L hLP _ hs2 hsN hB u huX hu2

theorem sec74_BX_typeLg [Finite G] (h73 : Asc82Lemma73) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hle : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g)
    (hL : ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 → InducesTypeSome L u 6 1 2 (-1)) :
    ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 →
      InducesTypeSome (CFSG.conjugate L g) u 6 1 2 (-1) := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  intro u hu hu2
  have huLg : u ∈ CFSG.conjugate L g := hle hu
  have huL : u ∈ L := layerCent_le L (g⁻¹ * t * g) hu
  rcases sec7_involution_types hP (isOm6P_conjugate hLP g) huLg hu2 with hu4g | hu2g
  · exfalso
    have hz : orderOf z = 2 ∧ InducesTypeSome L z 6 1 4 1 := sec7_z_type hF hctx
    have hzL : z ∈ L := hctx.z_mem_L
    have hzgLg : g⁻¹ * z * g ∈ CFSG.conjugate L g := by
      rw [mem_conjugate_iff]
      have hgz : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rwa [hgz]
    have hzg : InducesTypeSome (CFSG.conjugate L g) (g⁻¹ * z * g) 6 1 4 1 :=
      inducesTypeSome_conjugate hz.2 g
    have hzg2 : orderOf (g⁻¹ * z * g) = 2 := by
      rw [orderOf_conj_inv]; exact hz.1
    have hc : u ∈ conjClassIn (CFSG.conjugate L g) (g⁻¹ * z * g) :=
      hP.i4_one_class G (CFSG.conjugate L g) (isOm6P_conjugate hLP g)
        (g⁻¹ * z * g) u hzgLg huLg hzg2 hu2 hzg hu4g
    have hzu : IsConj z u :=
      (isConj_iff_inv_mul.mpr ⟨g, rfl⟩).trans (isConj_of_mem_conjClassIn hc)
    obtain ⟨h, hh⟩ := isConj_iff_inv_mul.mp hzu
    have huCt : u ∈ centralizer ({t} : Set G) := hctx.le_centralizer huL
    have hmem : h⁻¹ * z * h ∈ centralizer ({t} : Set G) := by rwa [hh]
    rcases h73 G t L S z hctx h hmem with ⟨α, hα⟩ | h4
    · rw [hh] at hα
      have hK3 : KindP L u 3 := ⟨α, hα⟩
      have hK1 : KindP L u 1 := hL u hu hu2
      exact (hP.excl G L hLP u hu2 (Subgroup.le_normalizer huL) 3 1
        (by norm_num) (by norm_num) (by norm_num) hK3) hK1
    · rw [hh] at h4
      have hK0 : KindP L u 0 := h4
      have hK1 : KindP L u 1 := hL u hu hu2
      exact (hP.excl G L hLP u hu2 (Subgroup.le_normalizer huL) 0 1
        (by norm_num) (by norm_num) (by norm_num) hK0) hK1
  · exact hu2g

theorem sec74BX_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) (hO : Asc82Outside) : Sec74BX := by
  intro G _ _ t L S z g hA hB
  have h1 := sec74_BX_le h36 h72 hP hO hA hB
  have h2 := sec74_BX_typeL h36 hP hA hB
  have h3 := sec74_BX_typeLg h73 hP hF hA h1.2 h2
  exact ⟨h1.1, h1.2, fun u hu hu2 => ⟨h2 u hu hu2, h3 u hu hu2⟩⟩

end CFSG.OddStandard.SmallF3.Omega
