module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
public import CFSG.GroupTheory.TitsSystem.Basic
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GroupTheory.TitsSystem.Atoms

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

@[expose] def GomiAtomGenerationTop (X : Type) [Group X] : Prop :=
  ∀ U Q : Subgroup X, IsSylowOf 2 U ⊤ → normalizer (U : Set X) ≤ Q →
    Q ≤ normalizer (U : Set X) ⊔ sSup {A | IsGomiAtom ⊤ U A ∧ A ≤ Q}

theorem GomiAtomGenerationTop.of_quotient {X : Type} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (hZ : Z ≤ center X) (hZr : Nat.Coprime (Nat.card Z) 2)
    (h : GomiAtomGenerationTop (X ⧸ Z)) : GomiAtomGenerationTop X := by
  intro U Q hU hQ
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hUs : IsSylowOf 2 (U.map π) ⊤ := isSylowOf_top_map_of_surjective hπ hU
  have hN : (normalizer (U : Set X)).map π = normalizer (U.map π : Set (X ⧸ Z)) :=
    map_mk'_normalizer_eq Z hZ hZr hU.isPGroup
  have hNQ : normalizer (U.map π : Set (X ⧸ Z)) ≤ Q.map π := by
    rw [← hN]
    exact Subgroup.map_mono hQ
  have hkey := h (U.map π) (Q.map π) hUs hNQ
  let W : Subgroup X := normalizer (U : Set X) ⊔ sSup {A | IsGomiAtom ⊤ U A ∧ A ≤ Q}
  change Q ≤ W
  have hWmap : Q.map π ≤ W.map π := by
    refine hkey.trans (sup_le ?_ ?_)
    · rw [← hN]
      exact Subgroup.map_mono le_sup_left
    · refine sSup_le ?_
      intro Ā hĀ
      obtain ⟨hĀatom, hĀQ⟩ := hĀ
      have hAc : IsGomiAtom ⊤ U (Ā.comap π) :=
        (isGomiAtom_top_comap_mk'_iff Z hZ hZr hU.isPGroup Ā).2 hĀatom
      have hAQc : Ā.comap π ≤ Q :=
        (Subgroup.comap_mono hĀQ).trans (le_of_eq (comap_map_mk'_eq_of_normalizer_le Z hZ hQ))
      have hAmem : (Ā.comap π) ∈ {A | IsGomiAtom ⊤ U A ∧ A ≤ Q} := ⟨hAc, hAQc⟩
      have hAleW : Ā.comap π ≤ W := (le_sSup hAmem).trans le_sup_right
      calc Ā = (Ā.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ Ā).symm
        _ ≤ W.map π := Subgroup.map_mono hAleW
  have hQeq : (Q.map π).comap π = Q := comap_map_mk'_eq_of_normalizer_le Z hZ hQ
  calc Q = (Q.map π).comap π := hQeq.symm
    _ ≤ (W.map π).comap π := Subgroup.comap_mono hWmap
    _ = W := comap_map_mk'_eq_of_normalizer_le Z hZ le_sup_left

theorem gomiChevAtomGeneration_of_top
    (h : ∀ (L : Type) [Group L] [Finite L], IsGomiChevTwo L → GomiAtomGenerationTop L) :
    GomiChevAtomGeneration := by
  intro G _ _ L U Q hL hU hQ₁ hQ₂
  let ι : ↥L →* G := L.subtype
  let U' : Subgroup ↥L := U.subgroupOf L
  let Q' : Subgroup ↥L := Q.subgroupOf L
  have hUle : U ≤ L := hU.le
  have hU's : IsSylowOf 2 U' ⊤ := (isSylowOf_top_subgroupOf_iff hUle).2 hU
  have hNmap : (normalizer (U' : Set ↥L)).map ι = L ⊓ normalizer (U : Set G) :=
    (inf_normalizer_eq_map_normalizer_subgroupOf hUle).symm
  have hNQ' : normalizer (U' : Set ↥L) ≤ Q' := by
    show normalizer (U.subgroupOf L : Set ↥L) ≤ Q.comap L.subtype
    rw [← Subgroup.map_le_iff_le_comap]
    rw [← inf_normalizer_eq_map_normalizer_subgroupOf hUle]
    exact hQ₁
  have hkey := h ↥L hL U' Q' hU's hNQ'
  let R : Subgroup G := L ⊓ normalizer (U : Set G) ⊔ sSup {A | IsGomiAtom L U A ∧ A ≤ Q}
  change Q ≤ R
  have hQ'R : Q' ≤ R.comap ι := by
    refine hkey.trans (sup_le ?_ ?_)
    · have hmap : (normalizer (U' : Set ↥L)).map ι ≤ R := by
        rw [hNmap]
        exact le_sup_left
      exact (Subgroup.map_le_iff_le_comap).mp hmap
    · refine sSup_le ?_
      intro A' hA'
      obtain ⟨hA'atom, hA'Q⟩ := hA'
      have hUmap : U'.map ι = U := Subgroup.map_subgroupOf_eq_of_le hUle
      have hQmap : Q'.map ι = Q := Subgroup.map_subgroupOf_eq_of_le hQ₂
      have hA'atomG : IsGomiAtom L U (A'.map ι) := by
        simpa only [← hUmap] using (isGomiAtom_map_subtype_iff L U' A').2 hA'atom
      have hA'Q' : A'.map ι ≤ Q := by
        rw [← hQmap]
        exact Subgroup.map_mono hA'Q
      have hAmem : A'.map ι ∈ {A | IsGomiAtom L U A ∧ A ≤ Q} := ⟨hA'atomG, hA'Q'⟩
      have hAleR : A'.map ι ≤ R := (le_sSup hAmem).trans le_sup_right
      exact (Subgroup.map_le_iff_le_comap).mp hAleR
  have hQmap : Q'.map ι = Q := Subgroup.map_subgroupOf_eq_of_le hQ₂
  calc Q = Q'.map ι := hQmap.symm
    _ ≤ R := (Subgroup.map_le_iff_le_comap).mpr hQ'R

theorem gomiChevAtomGeneration_of_simple
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → IsChevTwo K →
      GomiAtomGenerationTop K) : GomiChevAtomGeneration :=
  gomiChevAtomGeneration_of_top fun L _ _ hL => GomiAtomGenerationTop.of_quotient (center L)
    le_rfl hL.coprime_card_center (h _ hL.isSimpleGroup hL.isChevTwo)

theorem le_normalizer_sup_sSup_isGomiAtom_of_isBNPair {X : Type} [Group X] {B N : Subgroup X}
    [(CFSG.GH74.BNPair.cartan B N).Normal] {S : Set (CFSG.GH74.BNPair.WeylGroup B N)}
    (hBN : TitsSystem.IsBNPair B N S) {U Q : Subgroup X} (hUB : normalizer (U : Set X) = B)
    (hBQ : B ≤ Q) : Q ≤ normalizer (U : Set X) ⊔ sSup {A | IsGomiAtom ⊤ U A ∧ A ≤ Q} := by
  subst hUB
  simpa only [isGomiAtom_top_iff_covBy] using hBN.le_sup_sSup_covBy hBQ

end CFSG.GroupTheory
