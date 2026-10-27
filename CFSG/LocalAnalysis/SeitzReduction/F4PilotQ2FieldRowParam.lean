module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwist

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotQ2FieldRowParamNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Param

variable {K : Type} [Field K] (σ : K ≃+* K) {G : Type} [Group G] {L : Subgroup G}
  (e : L ≃* adjointGroup .F4 (fixSubfield σ))

structure Q2FieldParam (N : AmalgamNeighbour) (E : Subgroup G) where
  Φ : N.levi K ≃* E
  fix : ∀ x : N.levi (fixSubfield σ), ((Φ (leviInclusion σ N x) : E) : G) =
    ((e.symm (x : adjointGroup .F4 (fixSubfield σ)) : L) : G)

variable {σ e}

@[expose] noncomputable def Q2FieldParam.restrict {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J →* G :=
  E.subtype.comp (h.Φ.toMonoidHom.comp (Subgroup.inclusion (levi_le_neighbourLevi hJ)))

theorem Q2FieldParam.restrict_apply {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    h.restrict hJ x = (h.Φ ⟨x, levi_le_neighbourLevi hJ x.2⟩ : G) :=
  rfl

theorem Q2FieldParam.restrict_injective {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    Function.Injective (h.restrict hJ) :=
  Subtype.val_injective.comp (h.Φ.injective.comp (Subgroup.inclusion_injective _))

theorem Q2FieldParam.restrict_eq_of_coe_eq {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {I J : Finset (Fin (Tag.rank .F4))} (hI : I ⊆ N.nodes)
    (hJ : J ⊆ N.nodes) (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : (x : adjointGroup .F4 K) = y) : h.restrict hI x = h.restrict hJ y := by
  rw [h.restrict_apply, h.restrict_apply]
  exact congrArg (fun z => (h.Φ z : G)) (Subtype.ext hxy)

theorem Q2FieldParam.commute_restrict {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {I J : Finset (Fin (Tag.rank .F4))} (hI : I ⊆ N.nodes)
    (hJ : J ⊆ N.nodes) (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : Commute (x : adjointGroup .F4 K) y) : Commute (h.restrict hI x) (h.restrict hJ y) := by
  rw [h.restrict_apply, h.restrict_apply]
  have hc : Commute (⟨x, levi_le_neighbourLevi hI x.2⟩ : N.levi K)
      ⟨y, levi_le_neighbourLevi hJ y.2⟩ := Subtype.ext hxy.eq
  exact (hc.map h.Φ).map E.subtype

theorem Q2FieldParam.restrict_fix {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    {x : adjointGroup .F4 (fixSubfield σ)}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup J)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .F4 (fixSubfield σ))) :
    h.restrict hJ y = ((e.symm x : L) : G) := by
  have hxN : x ∈ N.levi (fixSubfield σ) := levi_le_neighbourLevi hJ hx
  have h1 : (⟨y, levi_le_neighbourLevi hJ y.2⟩ : N.levi K) = leviInclusion σ N ⟨x, hxN⟩ :=
    Subtype.ext (Subtype.ext (by rw [coe_leviInclusion]; exact hxy))
  rw [h.restrict_apply, h1]
  exact h.fix ⟨x, hxN⟩

theorem Q2FieldParam.range_restrict_eq_map {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    (h.restrict hJ).range =
      ((CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J).subgroupOf
        (N.levi K)).map (E.subtype.comp h.Φ.toMonoidHom) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, levi_le_neighbourLevi hJ x.2⟩, x.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

@[expose] noncomputable def Q2FieldParam.twist [Finite K] {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    Q2FieldParam σ e N E where
  Φ := (leviEntrywiseEquiv ρ N).trans h.Φ
  fix x := by
    have hx : leviEntrywiseEquiv ρ N (leviInclusion σ N x) = leviInclusion σ N x := by
      refine Subtype.ext (Subtype.ext ?_)
      have hcomp : (ρ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
        RingHom.ext fun c => hρ c
      rw [coe_leviEntrywiseEquiv, coe_leviInclusion, baseChangeGL_baseChangeGL, hcomp]
    rw [MulEquiv.trans_apply, hx]
    exact h.fix x

theorem Q2FieldParam.twist_apply [Finite K] {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) (x : N.levi K) :
    (h.twist ρ hρ).Φ x = h.Φ (leviEntrywiseEquiv ρ N x) :=
  rfl

end Param

section ToX'

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

@[expose] noncomputable def Q2FieldParam.toX' {E : Subgroup G} (h : Q2FieldParam σ e .X E) :
    Q2FieldParam σ e .X'
      (E.map (MulAut.conj ((e.symm (n1242 (fixSubfield σ)) : L) : G)).toMonoidHom) where
  Φ := ((c3LeviConjEquiv K).symm.trans h.Φ).trans
    ((MulAut.conj ((e.symm (n1242 (fixSubfield σ)) : L) : G)).subgroupMap E)
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

section Normalize

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem nonempty_q2FieldParam (N : AmalgamNeighbour) {E : Subgroup G}
    (hψ : Nonempty (N.levi K ≃* E)) {t : G} (hN : t ∈ normalizer (E : Set G))
    (ht2 : orderOf t = 2) (hσ : orderOf σ = 2)
    (hfix : perfectCore (E ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .F4 (fixSubfield σ)).subtype)) :
    Nonempty (Q2FieldParam σ e N E) := by
  obtain ⟨ψ₀⟩ := hψ
  have ht : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hθθ : E.normalizerMonoidHom ⟨t, hN⟩ * E.normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (E : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext ht, map_one]
  have hD : modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .F4 (fixSubfield σ)).subtype) ≤
      E := by
    rw [← hfix]
    exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  set ε₀ : StatedSp 3 (fixSubfield σ) →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((N.levi (fixSubfield σ)).subtype.comp (neighbourLeviEquiv (fixSubfield σ) N).toMonoidHom))
    with hε₀
  have hε₀M : ∀ g, ε₀ g ∈ E := fun g =>
    hD (symm_mem_modelToG e ⟨_, (neighbourLeviEquiv (fixSubfield σ) N g).2, rfl⟩)
  set ε : StatedSp 3 (fixSubfield σ) →* E := ε₀.codRestrict _ hε₀M with hε
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h
    apply (neighbourLeviEquiv (fixSubfield σ) N).injective
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : E => (z : G)) h
  have hεrange : ε.range.map E.subtype =
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
      (E.normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective E.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, map_eqLocus_normalizerMonoidHom hN, hfix, hεrange]
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_statedSpMap_eq_of_involution (fixSubfield σ).subtype hσ
    (apply_eq_iff_mem_range_fixSubfield_subtype σ) ((neighbourLeviEquiv K N).trans ψ₀) hθθ ε
    hεinj hεr
  refine ⟨⟨(neighbourLeviEquiv K N).symm.trans ψ', fun x => ?_⟩⟩
  obtain ⟨g, rfl⟩ := (neighbourLeviEquiv (fixSubfield σ) N).surjective x
  rw [MulEquiv.trans_apply, leviInclusion_neighbourLeviEquiv, MulEquiv.symm_apply_apply, hψ']
  rfl

end Normalize

end CFSG.SeitzReduction.F4Pilot
