module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwist

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.CurtisTits (IsCompatible IsUniversalCompletion)
open CFSG.Quasithin (perfectCore)

local instance f4PilotCTFieldNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Recognition


variable (K : Type) [Field K]

theorem exists_surjective_of_isCompatible_f4 {G : Type} [Group G]
    (φ : ∀ J, (Adjoint.f4Datum K).leviAmalgam J →* G)
    (hφ : IsCompatible (Adjoint.f4Datum K).leviAmalgam φ) (hgen : ⨆ J, (φ J).range = ⊤)
    (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    ∃ ψ : adjointGroup .F4 K →* G, (∀ J (x : (Adjoint.f4Datum K).leviAmalgam J), ψ x = φ J x) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ center (adjointGroup .F4 K) := by
  have hct := Adjoint.f4_isCTGroupDatum K
  have hext := Adjoint.f4_steinbergExtras K
  have hgenK : ⨆ J, (Adjoint.f4Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem (Adjoint.f4Datum K).isFiniteType
        (Adjoint.f4Datum K).divisible) hct
  have hU : IsUniversalCompletion.{0, 0, 0} (Adjoint.f4Datum K).leviAmalgam :=
    (Adjoint.f4Datum K).isUniversalCompletion_of_steinbergPresentation hct
      (steinbergPresentation_of_extras hct hext)
  obtain ⟨ψ, hψ, hsurj, hker, -⟩ :=
    CFSG.LieType.CurtisTits.recognition_of_isUniversalCompletion hgenK
      (Adjoint.isQuasisimple_f4 K) hU φ hφ hgen hnt
  exact ⟨ψ, hψ, hsurj, hker⟩

end Recognition

section Generators


variable {k : Type} [Field k]

theorem xElement_mem_levi_singleton
    (i : Fin (Tag.rank .F4)) (c : k) :
    xElement i c ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum k).rootGroup {i} := by
  rw [levi_f4Datum_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .F4 k γ)
    (Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩ le_rfl
    (xUnit_mem_rootSubgroup i c)

theorem yElement_mem_levi_singleton
    (i : Fin (Tag.rank .F4)) (c : k) :
    yElement i c ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum k).rootGroup {i} := by
  rw [levi_f4Datum_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .F4 k γ)
    (-Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inr rfl⟩ le_rfl
    (yUnit_mem_rootSubgroup i c)

end Generators

theorem mem_normalizer_iSup {M ι : Type*} [Group M] {H : ι → Subgroup M} {t : M}
    (ht : ∀ i, t ∈ normalizer (H i : Set M)) : t ∈ normalizer ((⨆ i, H i : Subgroup M) : Set M) := by
  have hmap : ∀ i, (H i).map (MulAut.conj t).toMonoidHom = H i := fun i => by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 (ht i) x).1 hx
    · intro hy
      refine ⟨t⁻¹ * y * t, (mem_normalizer_iff.1 (ht i) _).2 ?_, ?_⟩
      · rwa [show t * (t⁻¹ * y * t) * t⁻¹ = y by group]
      · change t * (t⁻¹ * y * t) * t⁻¹ = y
        group
  have hsup : (⨆ i, H i).map (MulAut.conj t).toMonoidHom = ⨆ i, H i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hmap
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hsup]
    exact ⟨x, hx, rfl⟩
  · rw [← hsup] at hx
    obtain ⟨x', hx', hxx'⟩ := hx
    have : x' = x := by
      change t * x' * t⁻¹ = t * x * t⁻¹ at hxx'
      simpa using hxx'
    exact this ▸ hx'

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem exists_injective_fieldRow (hX : FieldNeighbourIso σ e .X) (hY : FieldNeighbourIso σ e .Y)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ψ : adjointGroup .F4 K →* G, Function.Injective ψ ∧
      ψ.range = ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 ∧
      (∀ J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2},
        ((Adjoint.f4Datum K).leviAmalgam J).map ψ = pieceCore e J.1) ∧
      ∀ x : adjointGroup .F4 (fixSubfield σ), ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
  obtain ⟨φ, hcomp, hrange, hfix⟩ := exists_isCompatible_field hX hY hq
  have hcard : ∀ i : Fin (Tag.rank .F4),
      ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2 := fun i => by simp
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (Adjoint.f4Datum K).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (Adjoint.f4Datum K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hcomp i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hX0 := (Adjoint.f4_steinbergExtras (fixSubfield σ)).ne_bot (Pi.single 0 1)
      ((CFSG.LieType.RootSystem.isCTRootSystem _ _).single_mem 0)
    obtain ⟨u, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX0
    have hu0 : (u : adjointGroup .F4 (fixSubfield σ)) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {0} := by
      rw [CFSG.LieType.CurtisTits.levi_singleton]
      exact mem_sup_left u.2
    obtain ⟨y, hy⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype hu0
    refine ⟨⟨{0}, hcard 0⟩, y, fun h => hu ?_⟩
    have h1 : φ ⟨{0}, hcard 0⟩ y = 1 := congrArg Subtype.val h
    rw [hfix ⟨{0}, hcard 0⟩ _ hu0 y hy] at h1
    have h2 : e.symm (u : adjointGroup .F4 (fixSubfield σ)) = 1 := Subtype.ext h1
    have h3 : (u : adjointGroup .F4 (fixSubfield σ)) = 1 := by
      rw [← map_one e.symm] at h2
      exact e.symm.injective h2
    exact Subtype.ext h3
  obtain ⟨ψ₀, hψ₀, hsurj, hker⟩ := exists_surjective_of_isCompatible_f4 K φ' hφ' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans center_adjointGroup_eq_bot.le
  have hψφ : ∀ J (x : (Adjoint.f4Datum K).leviAmalgam J), (G₀.subtype.comp ψ₀) x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  refine ⟨G₀.subtype.comp ψ₀, G₀.subtype_injective.comp hinj₀, ?_, fun J => ?_, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hG₀]
    exact iSup_congr fun J => hrange J
  · have h1 : (G₀.subtype.comp ψ₀).comp ((Adjoint.f4Datum K).leviAmalgam J).subtype = φ J :=
      MonoidHom.ext fun x => hψφ J x
    rw [← hrange J, ← h1, MonoidHom.range_comp, Subgroup.range_subtype]
  · have key : ∀ (i : Fin (Tag.rank .F4)) (x : adjointGroup .F4 (fixSubfield σ)),
        x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {i} →
        (G₀.subtype.comp ψ₀) (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
      intro i x hx
      obtain ⟨y, hy⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype hx
      have hyx : (y : adjointGroup .F4 K) = fixedFieldInclusion σ x := Subtype.ext hy
      rw [← hyx]
      exact (hψφ ⟨{i}, hcard i⟩ y).trans (hfix ⟨{i}, hcard i⟩ x hx y hy)
    have h := CFSG.LieType.Ree.adjointGroup_hom_ext
      (f := (G₀.subtype.comp ψ₀).comp (fixedFieldInclusion σ))
      (g := L.subtype.comp e.symm.toMonoidHom)
      (fun i c => key i _ (xElement_mem_levi_singleton i c))
      (fun i c => key i _ (yElement_mem_levi_singleton i c))
    exact DFunLike.congr_fun h x

theorem nonempty_mulEquiv_fieldRow (hX : FieldNeighbourIso σ e .X)
    (hY : FieldNeighbourIso σ e .Y) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ Ψ : adjointGroup .F4 K ≃*
        ↥(⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1),
      ∀ x : adjointGroup .F4 (fixSubfield σ),
        ((Ψ (fixedFieldInclusion σ x) : G)) = ((e.symm x : L) : G) := by
  obtain ⟨ψ, hinj, hrange, -, hfix⟩ := exists_injective_fieldRow hX hY hq
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun x => hfix x⟩

end Main

section Normalizer

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem mem_normalizer_iSup_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer ((⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 :
      Subgroup G) : Set G) :=
  mem_normalizer_iSup fun J => le_normalizer_pieceCore e ht J.1

end Normalizer

end CFSG.SeitzReduction.F4Pilot
