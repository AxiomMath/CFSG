module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleBQAct
public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup
open CFSG.AGLEmbeddingD2.Tits.GN516

variable {G : Type} [Group G]

private theorem map_conjAut_subgroupOf {L : Subgroup G} {t : G}
    (ht : t ∈ normalizer (L : Set G)) (X : Subgroup G) :
    (X.subgroupOf L).map (SimpleBQ.conjAut L t ht).toMonoidHom =
      (X.map (MulAut.conj t).toMonoidHom).subgroupOf L := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨(x : G), hx, ?_⟩
    change (MulAut.conj t) (x : G) = ((SimpleBQ.conjAut L t ht x : ↥L) : G)
    rw [SimpleBQ.coe_conjAut, MulAut.conj_apply]
  · rintro y hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hy
    obtain ⟨a, ha, hax⟩ := hy
    have haL : a ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) y).mp y.2
      rw [inv_inv] at h
      have haeq : a = t⁻¹ * (y : G) * t := by
        rw [← hax]
        change a = t⁻¹ * (MulAut.conj t a) * t
        rw [MulAut.conj_apply]
        group
      rwa [haeq]
    refine ⟨⟨a, haL⟩, ha, ?_⟩
    apply Subtype.ext
    change (MulAut.conj t) a = (y : G)
    simpa [MulAut.conj_apply] using hax

theorem map_mapQuotient_conjAut {L : Subgroup G} {t : G} (ht : t ∈ normalizer (L : Set G))
    (X : Subgroup G) :
    ((X.subgroupOf L).map (QuotientGroup.mk' (center ↥L))).map
        (MulAut.mapQuotient (center ↥L) (SimpleBQ.conjAut L t ht)).toMonoidHom =
      ((X.map (MulAut.conj t).toMonoidHom).subgroupOf L).map (QuotientGroup.mk' (center ↥L)) := by
  have hcomp : ((MulAut.mapQuotient (center ↥L) (SimpleBQ.conjAut L t ht)).toMonoidHom).comp
        (QuotientGroup.mk' (center ↥L)) =
      (QuotientGroup.mk' (center ↥L)).comp (SimpleBQ.conjAut L t ht).toMonoidHom :=
    MonoidHom.ext fun x => by simp [MulAut.mapQuotient_mk]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_conjAut_subgroupOf ht X]

theorem eq_of_map_mk'_subgroupOf_eq {L U X Y : Subgroup G} (hX : X ≤ L) (hY : Y ≤ L)
    (hUX : normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ X.subgroupOf L)
    (hUY : normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ Y.subgroupOf L)
    (h : (X.subgroupOf L).map (QuotientGroup.mk' (center ↥L)) =
      (Y.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) : X = Y := by
  have hX' := comap_map_mk'_eq_of_normalizer_le (center ↥L) le_rfl hUX
  have hY' := comap_map_mk'_eq_of_normalizer_le (center ↥L) le_rfl hUY
  have hsub : X.subgroupOf L = Y.subgroupOf L := by rw [← hX', ← hY', h]
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hX, inf_eq_left.2 hY] at hsub
  exact hsub

theorem eq_of_isGomiAtom_of_map_mk'_subgroupOf_eq {L U X Y : Subgroup G} (hU : U ≤ L)
    (hX : IsGomiAtom L U X) (hY : IsGomiAtom L U Y)
    (h : (X.subgroupOf L).map (QuotientGroup.mk' (center ↥L)) =
      (Y.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) : X = Y := by
  have hUX : normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ X.subgroupOf L :=
    (Subgroup.map_le_iff_le_comap).1 <| by
      rw [← inf_normalizer_eq_map_normalizer_subgroupOf hU]
      exact hX.1.le
  have hUY : normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ Y.subgroupOf L :=
    (Subgroup.map_le_iff_le_comap).1 <| by
      rw [← inf_normalizer_eq_map_normalizer_subgroupOf hU]
      exact hY.1.le
  exact eq_of_map_mk'_subgroupOf_eq hX.2.1 hY.2.1 hUX hUY h

theorem isSylowOf_map_mk'_subgroupOf [Finite G] {L U : Subgroup G} (hU : IsSylowOf 2 U L) :
    IsSylowOf 2 ((U.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) ⊤ :=
  isSylowOf_top_map_of_surjective (QuotientGroup.mk'_surjective (center ↥L))
    ((isSylowOf_top_subgroupOf_iff hU.le).2 hU)

theorem isGomiAtom_map_mk'_subgroupOf [Finite G] {L U A : Subgroup G} (hL : IsGomiChevTwo ↥L)
    (hU : IsSylowOf 2 U L) (hA : IsGomiAtom L U A) :
    IsGomiAtom ⊤ ((U.subgroupOf L).map (QuotientGroup.mk' (center ↥L)))
      ((A.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) :=
  IsGomiAtom.map_mk' (center ↥L) le_rfl hL.coprime_card_center
    ((isSylowOf_top_subgroupOf_iff hU.le).2 hU).isPGroup
    ((isGomiAtom_iff_subgroupOf hU.le hA.2.1).1 hA)

private theorem map_mapQuotient_actHom {L R : Subgroup G}
    (hRN : R ≤ normalizer (L : Set G)) (r : ↥R) (X : Subgroup G) :
    ((X.subgroupOf L).map (QuotientGroup.mk' (center ↥L))).map
        (((MulAut.mapQuotient (center ↥L)).comp (SimpleBQ.actHom hRN)) r).toMonoidHom =
      ((X.map (MulAut.conj (r : G)).toMonoidHom).subgroupOf L).map
        (QuotientGroup.mk' (center ↥L)) :=
  map_mapQuotient_conjAut (hRN r.2) X

theorem gomiChevAtomOrbit_of_top
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      IsChevTwo K → GomiAtomOrbitTop K) : GomiChevAtomOrbit := by
  intro G _ _ L U T A hL hU hT hTL hTU hA t₁ ht₁ t₂ ht₂
  let Z : Subgroup ↥L := center ↥L
  let π : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  let S : Subgroup (↥L ⧸ Z) := (U.subgroupOf L).map π
  let A' : Subgroup (↥L ⧸ Z) := (A.subgroupOf L).map π
  let g : ↥T →* MulAut (↥L ⧸ Z) := (MulAut.mapQuotient Z).comp (SimpleBQ.actHom hTL)
  let 𝒜 : Subgroup (MulAut (↥L ⧸ Z)) := g.range
  let α₁ : MulAut (↥L ⧸ Z) := MulAut.mapQuotient Z (SimpleBQ.conjAut L t₁ (hTL ht₁))
  let α₂ : MulAut (↥L ⧸ Z) := MulAut.mapQuotient Z (SimpleBQ.conjAut L t₂ (hTL ht₂))
  have hS : IsSylowOf 2 S ⊤ := isSylowOf_map_mk'_subgroupOf hU
  have hA' : IsGomiAtom ⊤ S A' := isGomiAtom_map_mk'_subgroupOf hL hU hA
  have h𝒜 : IsPGroup 2 𝒜 :=
    hT.of_surjective g.rangeRestrict (MonoidHom.rangeRestrict_surjective g)
  have hfix : ∀ α ∈ 𝒜, S.map α.toMonoidHom = S := by
    intro α hα
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hα
    have hr : U.map (MulAut.conj (r : G)).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTU r.2)
    rw [map_mapQuotient_actHom hTL r U, hr]
  have hα₁ : α₁ ∈ 𝒜 := ⟨⟨t₁, ht₁⟩, rfl⟩
  have hα₂ : α₂ ∈ 𝒜 := ⟨⟨t₂, ht₂⟩, rfl⟩
  rcases h (↥L ⧸ Z) hL.isSimpleGroup hL.exists_mul_ne_mul hL.isChevTwo S A' 𝒜 hS h𝒜 hfix
      hA' α₁ hα₁ α₂ hα₂ with h1 | h2 | h3
  · left
    exact eq_of_isGomiAtom_of_map_mk'_subgroupOf_eq hU.le
      (IsGomiAtom.map_conj hA (hTL ht₁) (hTU ht₁)) hA
      (by rw [← map_mapQuotient_conjAut (hTL ht₁) A, h1])
  · right; left
    exact eq_of_isGomiAtom_of_map_mk'_subgroupOf_eq hU.le
      (IsGomiAtom.map_conj hA (hTL ht₂) (hTU ht₂)) hA
      (by rw [← map_mapQuotient_conjAut (hTL ht₂) A, h2])
  · right; right
    exact eq_of_isGomiAtom_of_map_mk'_subgroupOf_eq hU.le
      (IsGomiAtom.map_conj hA (hTL ht₁) (hTU ht₁))
      (IsGomiAtom.map_conj hA (hTL ht₂) (hTU ht₂))
      (by rw [← map_mapQuotient_conjAut (hTL ht₁) A, h3,
        map_mapQuotient_conjAut (hTL ht₂) A])

theorem gomiChevSwap_of_top
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      IsChevTwo K → GomiSwapTop K) : GomiChevSwap := by
  intro G _ _ L U A hL hU hA g hg hne hsup
  let Z : Subgroup ↥L := center ↥L
  let π : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  let S : Subgroup (↥L ⧸ Z) := (U.subgroupOf L).map π
  let A' : Subgroup (↥L ⧸ Z) := (A.subgroupOf L).map π
  let α : MulAut (↥L ⧸ Z) := MulAut.mapQuotient Z (SimpleBQ.conjAut L g hg.1)
  have hS : IsSylowOf 2 S ⊤ := isSylowOf_map_mk'_subgroupOf hU
  have hfix : S.map α.toMonoidHom = S := by
    have hgU : U.map (MulAut.conj g).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg.2
    rw [map_mapQuotient_conjAut hg.1 U, hgU]
  have hA' : IsGomiAtom ⊤ S A' := isGomiAtom_map_mk'_subgroupOf hL hU hA
  have hne' : A'.map α.toMonoidHom ≠ A' := by
    intro he
    exact hne (eq_of_isGomiAtom_of_map_mk'_subgroupOf_eq hU.le
      (IsGomiAtom.map_conj hA hg.1 hg.2) hA ((map_mapQuotient_conjAut hg.1 A).symm.trans he))
  have hsup' : A' ⊔ A'.map α.toMonoidHom = ⊤ := by
    have hsupL : (A.subgroupOf L) ⊔ ((A.map (MulAut.conj g).toMonoidHom).subgroupOf L) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA.2.1 (IsGomiAtom.map_conj hA hg.1 hg.2).2.1, hsup,
        Subgroup.subgroupOf_self]
    rw [map_mapQuotient_conjAut hg.1 A, ← Subgroup.map_sup, hsupL,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Z)]
  exact h (↥L ⧸ Z) hL.isSimpleGroup hL.exists_mul_ne_mul hL.isChevTwo S A' α hS hfix hA' hne'
    hsup'

end CFSG.GroupTheory
