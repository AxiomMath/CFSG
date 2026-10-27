module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFJr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private theorem map_subgroupOf_equivMapOfInjective (hf : Function.Injective f)
    (V N : Subgroup Γ₁) :
    (N.subgroupOf V).map (Subgroup.equivMapOfInjective V f hf) =
      (N.map f).subgroupOf (V.map f) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨(x : Γ₁), hx, (Subgroup.coe_equivMapOfInjective_apply V f hf x).symm.trans
      (congrArg Subtype.val hxy)⟩
  · rintro ⟨n, hn, hny⟩
    refine ⟨(Subgroup.equivMapOfInjective V f hf).symm y, ?_, by simp⟩
    have h1 : f (((Subgroup.equivMapOfInjective V f hf).symm y : ↥V) : Γ₁) = (y : Γ₂) := by
      rw [← Subgroup.coe_equivMapOfInjective_apply V f hf]
      simp
    have h2 : ((Subgroup.equivMapOfInjective V f hf).symm y : ↥V) = n := hf (by rw [h1, hny])
    rw [h2]
    exact hn

private theorem normal_subgroupOf_of_map (hf : Function.Injective f) (V N : Subgroup Γ₁)
    (h' : ((N.map f).subgroupOf (V.map f)).Normal) : (N.subgroupOf V).Normal := by
  have hmap : ((N.subgroupOf V).map
      (Subgroup.equivMapOfInjective V f hf : ↥V →* ↥(V.map f))).Normal := by
    rwa [map_subgroupOf_equivMapOfInjective hf V N]
  have := hmap.comap (Subgroup.equivMapOfInjective V f hf : ↥V →* ↥(V.map f))
  rwa [Subgroup.comap_map_eq_self_of_injective
    (Subgroup.equivMapOfInjective V f hf).injective] at this

private theorem normal_map_subgroupOf (hf : Function.Injective f) (V N : Subgroup Γ₁)
    (h : (N.subgroupOf V).Normal) : ((N.map f).subgroupOf (V.map f)).Normal := by
  have hmap : ((N.subgroupOf V).map
      (Subgroup.equivMapOfInjective V f hf : ↥V →* ↥(V.map f))).Normal :=
    h.map (Subgroup.equivMapOfInjective V f hf : ↥V →* ↥(V.map f))
      (Subgroup.equivMapOfInjective V f hf).surjective
  rwa [map_subgroupOf_equivMapOfInjective hf V N] at hmap

private noncomputable def quotientCongr (hf : Function.Injective f) (V N : Subgroup Γ₁)
    [hN : (N.subgroupOf V).Normal] [hN' : ((N.map f).subgroupOf (V.map f)).Normal] :
    (↥V ⧸ N.subgroupOf V) ≃*
      (↥(V.map f) ⧸ (N.map f).subgroupOf (V.map f)) :=
  QuotientGroup.congr (N.subgroupOf V) ((N.map f).subgroupOf (V.map f))
    (Subgroup.equivMapOfInjective V f hf) (map_subgroupOf_equivMapOfInjective hf V N)

private theorem quotientCongr_mk' (hf : Function.Injective f) (V N : Subgroup Γ₁)
    [hN : (N.subgroupOf V).Normal] [hN' : ((N.map f).subgroupOf (V.map f)).Normal]
    (x : ↥V) :
    quotientCongr hf V N (QuotientGroup.mk' (N.subgroupOf V) x) =
      QuotientGroup.mk' ((N.map f).subgroupOf (V.map f))
        (Subgroup.equivMapOfInjective V f hf x) :=
  QuotientGroup.congr_mk' (N.subgroupOf V) ((N.map f).subgroupOf (V.map f))
    (Subgroup.equivMapOfInjective V f hf) (map_subgroupOf_equivMapOfInjective hf V N) x

private theorem quotientCongr_comp (hf : Function.Injective f) (V N : Subgroup Γ₁)
    [hN : (N.subgroupOf V).Normal] [hN' : ((N.map f).subgroupOf (V.map f)).Normal] :
    (quotientCongr hf V N).toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf V)) =
      (QuotientGroup.mk' ((N.map f).subgroupOf (V.map f))).comp
        (Subgroup.equivMapOfInjective V f hf) := by
  ext x
  exact quotientCongr_mk' hf V N x

attribute [irreducible] quotientCongr

private theorem map_subgroupOf_quotient (hf : Function.Injective f) (V N X : Subgroup Γ₁)
    [hN : (N.subgroupOf V).Normal] [hN' : ((N.map f).subgroupOf (V.map f)).Normal] :
    ((X.map f).subgroupOf (V.map f)).map
        (QuotientGroup.mk' ((N.map f).subgroupOf (V.map f))) =
      ((X.subgroupOf V).map (QuotientGroup.mk' (N.subgroupOf V))).map
        (quotientCongr hf V N).toMonoidHom := by
  rw [← map_subgroupOf_equivMapOfInjective hf V X, Subgroup.map_map, Subgroup.map_map,
    ← quotientCongr_comp hf V N]

private theorem isElemAbelian_map_iff {G H : Type*} [Group G] [Group H] {p : ℕ}
    (e : G ≃* H) (E : Subgroup G) :
    IsElemAbelian p (E.map e.toMonoidHom) ↔ IsElemAbelian p E := by
  refine ⟨fun h => ?_, fun h => h.map e.toMonoidHom⟩
  have h' : IsElemAbelian p ((E.map e.toMonoidHom).comap e.toMonoidHom) := h.comap e.injective
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective E] at h'

private theorem maxElemAbelian_map {G H : Type} [Group G] [Group H]
    (e : G ≃* H) :
    Set.image (Subgroup.map e.toMonoidHom) (maxElemAbelian (⊤ : Subgroup G)) =
      maxElemAbelian (⊤ : Subgroup H) := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨le_top, (isElemAbelian_map_iff e A).mpr hA.2.1, ?_⟩
    intro B' hB' _ hB'c
    have hle : A ≤ B'.comap e.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hB'
    have hAc : IsElemAbelian 2 (B'.comap e.toMonoidHom) := hB'c.comap e.injective
    have hAeq : B'.comap e.toMonoidHom = A := hA.2.2 _ hle le_top hAc
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective B', hAeq]
  · rintro ⟨_, hBc, hBmax⟩
    refine ⟨B.comap e.toMonoidHom, ⟨le_top, hBc.comap e.injective, ?_⟩,
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective B⟩
    intro A' hA' hA'T hA'c
    have hmax := hBmax (A'.map e.toMonoidHom) (by
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective B]
      exact Subgroup.map_mono hA') le_top (hA'c.map e.toMonoidHom)
    exact Subgroup.map_injective e.injective (hmax.trans
      (Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective B).symm)

theorem secProp_map_type (hf : Function.Injective f) (V N : Subgroup Γ₁)
    (Q : (Y : Type) → [Group Y] → Prop)
    (hQ : ∀ (Y Y' : Type) [Group Y] [Group Y'], (Y ≃* Y') → (Q Y ↔ Q Y')) :
    SecProp (V.map f) (N.map f) (fun Y _ _ _ => Q Y) ↔ SecProp V N (fun Y _ _ _ => Q Y) := by
  constructor
  · rintro ⟨h', hq'⟩
    have hN := normal_subgroupOf_of_map hf V N h'
    haveI := hN
    haveI := h'
    exact ⟨hN, (hQ _ _ (quotientCongr hf V N)).mpr hq'⟩
  · rintro ⟨h, hq⟩
    have hN' := normal_map_subgroupOf hf V N h
    haveI := h
    haveI := hN'
    exact ⟨hN', (hQ _ _ (quotientCongr hf V N)).mp hq⟩

theorem secProp_maxElem_map (hf : Function.Injective f) (V N X₁ X₂ : Subgroup Γ₁) :
    SecProp (V.map f) (N.map f) (fun Y _ _ π => maxElemAbelian (⊤ : Subgroup Y) =
        {((X₁.map f).subgroupOf (V.map f)).map π, ((X₂.map f).subgroupOf (V.map f)).map π}) ↔
      SecProp V N (fun Y _ _ π => maxElemAbelian (⊤ : Subgroup Y) =
        {(X₁.subgroupOf V).map π, (X₂.subgroupOf V).map π}) := by
  constructor
  · rintro ⟨h', hp'⟩
    have hN := normal_subgroupOf_of_map hf V N h'
    haveI := hN
    haveI := h'
    refine ⟨hN, ?_⟩
    dsimp only
    apply (Subgroup.map_injective (f := (quotientCongr hf V N).toMonoidHom)
      (quotientCongr hf V N).injective).image_injective
    rw [maxElemAbelian_map (quotientCongr hf V N), hp', Set.image_pair,
      ← map_subgroupOf_quotient hf V N X₁, ← map_subgroupOf_quotient hf V N X₂]
  · rintro ⟨h, hp⟩
    have hN' := normal_map_subgroupOf hf V N h
    haveI := h
    haveI := hN'
    refine ⟨hN', ?_⟩
    dsimp only
    rw [← maxElemAbelian_map (quotientCongr hf V N), hp, Set.image_pair,
      map_subgroupOf_quotient hf V N X₁, map_subgroupOf_quotient hf V N X₂]

theorem secProp_thompsonRank_map (hf : Function.Injective f) (V N X : Subgroup Γ₁) :
    SecProp (V.map f) (N.map f) (fun Y _ _ π =>
        thompsonRank (⊤ : Subgroup Y) = ((X.map f).subgroupOf (V.map f)).map π) ↔
      SecProp V N (fun Y _ _ π => thompsonRank (⊤ : Subgroup Y) = (X.subgroupOf V).map π) := by
  constructor
  · rintro ⟨h', hp'⟩
    have hN := normal_subgroupOf_of_map hf V N h'
    haveI := hN
    haveI := h'
    refine ⟨hN, ?_⟩
    dsimp only
    apply Subgroup.map_injective (f := (quotientCongr hf V N).toMonoidHom)
      (quotientCongr hf V N).injective
    rw [thompsonRank_top_map_equiv (quotientCongr hf V N), hp',
      ← map_subgroupOf_quotient hf V N X]
  · rintro ⟨h, hp⟩
    have hN' := normal_map_subgroupOf hf V N h
    haveI := h
    haveI := hN'
    refine ⟨hN', ?_⟩
    dsimp only
    rw [← thompsonRank_top_map_equiv (quotientCongr hf V N), hp,
      map_subgroupOf_quotient hf V N X]

end CFSG.OddStandard.HigherRank.YamadaG23
