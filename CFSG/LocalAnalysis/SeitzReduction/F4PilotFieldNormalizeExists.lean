module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotFieldNormalizeExistsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Models


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def c3LeviConjEquiv : ↥(C3Levi K) ≃* ↥(C3Levi1242 K) :=
  ((MulAut.conj (n1242 K)).subgroupMap (C3Levi K)).trans
    (MulEquiv.subgroupCongr map_conj_n1242_C3Levi)

omit
  [Finite K] [CharP K 2] in
theorem coe_c3LeviConjEquiv (g : C3Levi K) :
    (((c3LeviConjEquiv K g : C3Levi1242 K) : adjointGroup .F4 K) : ModGL .F4 K) =
      (n1242 K : ModGL .F4 K) * ((g : adjointGroup .F4 K) : ModGL .F4 K) *
        (n1242 K : ModGL .F4 K)⁻¹ :=
  rfl

@[expose] noncomputable def neighbourLeviEquiv :
    (N : AmalgamNeighbour) → (↥(StatedSp 3 K) ≃* ↥(N.levi K))
  | .X => c3LeviEquiv K
  | .Y =>
    have : CharP K ReeTag.F4.prime := ‹CharP K 2›
    (c3LeviEquiv K).trans (c3LeviEquivB3Levi K)
  | .X' => (c3LeviEquiv K).trans (c3LeviConjEquiv K)

variable {K}

theorem leviInclusion_neighbourLeviEquiv (σ : K ≃+* K) (N : AmalgamNeighbour)
    (g : StatedSp 3 (fixSubfield σ)) :
    leviInclusion σ N (neighbourLeviEquiv (fixSubfield σ) N g) =
      neighbourLeviEquiv K N (statedSpMap (fixSubfield σ).subtype 3 g) := by
  have hX : ∀ g : StatedSp 3 (fixSubfield σ),
      baseChangeGL (fixSubfield σ).subtype
          (((c3LeviEquiv (fixSubfield σ) g : C3Levi (fixSubfield σ)) :
            adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) =
        (((c3LeviEquiv K (statedSpMap (fixSubfield σ).subtype 3 g) : C3Levi K) :
          adjointGroup .F4 K) : ModGL .F4 K) := fun g => by
    rw [← c3LeviBaseChange_c3LeviEquiv, coe_c3LeviBaseChange]
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_leviInclusion]
  cases N
  · exact hX g
  ·
    have : CharP K ReeTag.F4.prime := ‹CharP K 2›
    have : CharP (fixSubfield σ) ReeTag.F4.prime := inferInstance
    set y : adjointGroup .F4 (fixSubfield σ) :=
      ((c3LeviEquiv (fixSubfield σ) g : C3Levi (fixSubfield σ)) : adjointGroup .F4 (fixSubfield σ))
      with hy
    have h1 : ReeTag.F4.finiteExceptionalAut K (fixedFieldInclusion σ y) =
        fixedFieldInclusion σ (ReeTag.F4.finiteExceptionalAut (fixSubfield σ) y) :=
      DFunLike.congr_fun (finiteExceptionalAut_comp_fixedFieldInclusion σ) y
    have hιy : fixedFieldInclusion σ y =
        ((c3LeviEquiv K (statedSpMap (fixSubfield σ).subtype 3 g) : C3Levi K) :
          adjointGroup .F4 K) :=
      Subtype.ext (by rw [coe_fixedFieldInclusion]; exact hX g)
    change baseChangeGL (fixSubfield σ).subtype ((graphAutF4 (fixSubfield σ) y :
        adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) =
      ((graphAutF4 K ((c3LeviEquiv K (statedSpMap (fixSubfield σ).subtype 3 g) : C3Levi K) :
        adjointGroup .F4 K) : adjointGroup .F4 K) : ModGL .F4 K)
    exact ((coe_fixedFieldInclusion σ _).symm.trans (congrArg Subtype.val h1).symm).trans
      (congrArg (fun z => ((ReeTag.F4.finiteExceptionalAut K z : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K)) hιy)
  ·
    change baseChangeGL (fixSubfield σ).subtype ((n1242 (fixSubfield σ) :
        ModGL .F4 (fixSubfield σ)) * (((c3LeviEquiv (fixSubfield σ) g : C3Levi (fixSubfield σ)) :
          adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) *
            (n1242 (fixSubfield σ) : ModGL .F4 (fixSubfield σ))⁻¹) =
      (n1242 K : ModGL .F4 K) * (((c3LeviEquiv K (statedSpMap (fixSubfield σ).subtype 3 g) :
        C3Levi K) : adjointGroup .F4 K) : ModGL .F4 K) * (n1242 K : ModGL .F4 K)⁻¹
    rw [map_mul, map_mul, map_inv, baseChangeGL_n1242, hX g]

end Models

section Aux

theorem apply_eq_iff_mem_range_fixSubfield_subtype {K : Type} [Field K] (σ : K ≃+* K) (x : K) :
    σ x = x ↔ x ∈ Set.range (fixSubfield σ).subtype :=
  ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

theorem map_eqLocus_normalizerMonoidHom {G : Type*} [Group G] {E : Subgroup G} {t : G}
    (hN : t ∈ normalizer (E : Set G)) :
    (MonoidHom.eqLocus (E.normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id E)).map
      E.subtype = E ⊓ centralizer ({t} : Set G) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨y.2, ?_⟩
    have h1 : t * (y : G) * t⁻¹ = y := by
      rw [← Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨t, hN⟩ y]
      exact congrArg Subtype.val hy
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro hg
    obtain ⟨hgE, hgt⟩ := mem_inf.1 hg
    refine ⟨⟨g, hgE⟩, Subtype.ext ?_, rfl⟩
    change ((E.normalizerMonoidHom ⟨t, hN⟩ ⟨g, hgE⟩ : E) : G) = g
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [mem_centralizer_singleton_iff] at hgt
    rw [← hgt, mul_inv_cancel_right]

end Aux

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem nonempty_fieldNeighbourIso (N : AmalgamNeighbour)
    (hψ : Nonempty (N.levi K ≃* neighbourCore e N)) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hσ : orderOf σ = 2)
    (hfix : perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .F4 (fixSubfield σ)).subtype)) :
    Nonempty (FieldNeighbourIso σ e N) := by
  obtain ⟨ψ₀⟩ := hψ
  have hN : t ∈ normalizer (neighbourCore e N : Set G) := le_normalizer_neighbourCore e htL N
  have ht : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hθθ : (neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e N : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext ht, map_one]
  have hD : modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .F4 (fixSubfield σ)).subtype) ≤
      neighbourCore e N := by
    rw [← hfix]
    exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  set ε₀ : StatedSp 3 (fixSubfield σ) →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((N.levi (fixSubfield σ)).subtype.comp (neighbourLeviEquiv (fixSubfield σ) N).toMonoidHom))
    with hε₀
  have hε₀M : ∀ g, ε₀ g ∈ neighbourCore e N := fun g =>
    hD (symm_mem_modelToG e ⟨_, (neighbourLeviEquiv (fixSubfield σ) N g).2, rfl⟩)
  set ε : StatedSp 3 (fixSubfield σ) →* neighbourCore e N := ε₀.codRestrict _ hε₀M with hε
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h
    apply (neighbourLeviEquiv (fixSubfield σ) N).injective
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : neighbourCore e N => (z : G)) h
  have hεrange : ε.range.map (neighbourCore e N).subtype =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .F4 (fixSubfield σ)).subtype) := by
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact symm_mem_modelToG e ⟨_, (neighbourLeviEquiv (fixSubfield σ) N g').2, rfl⟩
    · intro hg
      obtain ⟨x, ⟨y, hy, hyx⟩, rfl⟩ := (mem_modelToG e).1 hg
      have hxy : x = y := Subtype.ext hyx.symm
      subst hxy
      obtain ⟨g', hg'⟩ := (neighbourLeviEquiv (fixSubfield σ) N).surjective ⟨x, hy⟩
      refine ⟨ε g', ⟨g', rfl⟩, ?_⟩
      change ((e.symm ((neighbourLeviEquiv (fixSubfield σ) N g' : N.levi (fixSubfield σ)) :
        adjointGroup .F4 (fixSubfield σ)) : L) : G) = _
      rw [hg']
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      ((neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective (neighbourCore e N).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, map_eqLocus_normalizerMonoidHom hN, hfix, hεrange]
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_statedSpMap_eq_of_involution (fixSubfield σ).subtype hσ
    (apply_eq_iff_mem_range_fixSubfield_subtype σ) ((neighbourLeviEquiv K N).trans ψ₀) hθθ ε
    hεinj hεr
  refine ⟨⟨(neighbourLeviEquiv K N).symm.trans ψ', fun x => ?_⟩⟩
  obtain ⟨g, rfl⟩ := (neighbourLeviEquiv (fixSubfield σ) N).surjective x
  rw [MulEquiv.trans_apply, leviInclusion_neighbourLeviEquiv, MulEquiv.symm_apply_apply, hψ']
  rfl

end Main

section ToX'


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem leviInclusion_c3LeviConjEquiv (x : C3Levi (fixSubfield σ)) :
    leviInclusion σ .X' (c3LeviConjEquiv (fixSubfield σ) x) =
      c3LeviConjEquiv K (leviInclusion σ .X x) := by
  refine Subtype.ext (Subtype.ext ?_)
  change baseChangeGL (fixSubfield σ).subtype ((n1242 (fixSubfield σ) :
      ModGL .F4 (fixSubfield σ)) * ((x : adjointGroup .F4 (fixSubfield σ)) :
        ModGL .F4 (fixSubfield σ)) * (n1242 (fixSubfield σ) : ModGL .F4 (fixSubfield σ))⁻¹) =
    (n1242 K : ModGL .F4 K) * baseChangeGL (fixSubfield σ).subtype
      ((x : adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) *
        (n1242 K : ModGL .F4 K)⁻¹
  rw [map_mul, map_mul, map_inv, baseChangeGL_n1242]

@[expose] noncomputable def FieldNeighbourIso.toX' (h : FieldNeighbourIso σ e .X) :
    FieldNeighbourIso σ e .X' where
  Φ := (((c3LeviConjEquiv K).symm.trans h.Φ).trans
    ((MulAut.conj ((e.symm (n1242 (fixSubfield σ)) : L) : G)).subgroupMap
      (neighbourCore e .X))).trans (MulEquiv.subgroupCongr (neighbourCore_X'_eq_map_conj e).symm)
  fix x := by
    obtain ⟨x₀, rfl⟩ := (c3LeviConjEquiv (fixSubfield σ)).surjective x
    change ((e.symm (n1242 (fixSubfield σ)) : L) : G) *
        (h.Φ ((c3LeviConjEquiv K).symm (leviInclusion σ .X' (c3LeviConjEquiv (fixSubfield σ) x₀))) :
          G) * ((e.symm (n1242 (fixSubfield σ)) : L) : G)⁻¹ =
      ((e.symm (n1242 (fixSubfield σ) * (x₀ : adjointGroup .F4 (fixSubfield σ)) *
        (n1242 (fixSubfield σ))⁻¹) : L) : G)
    rw [leviInclusion_c3LeviConjEquiv]
    have h1 : (c3LeviConjEquiv K).symm (c3LeviConjEquiv K (leviInclusion σ .X x₀)) =
        leviInclusion σ .X x₀ := (c3LeviConjEquiv K).symm_apply_apply _
    rw [h1, h.fix x₀, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

end ToX'

end CFSG.SeitzReduction.F4Pilot
