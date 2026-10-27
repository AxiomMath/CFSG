module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevFixedTypes
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRankOne
import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Tools

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools Subgroup

private theorem gomiChevAtom_moved_of_fixedTypes (hBT : GomiChevBorelTits) (hB : GomiBender)
    (hOrb : GomiChevAtomOrbit) (hFix : GomiChevFixedTypes) {G : Type} [Group G] [Finite G]
    {L I U : Subgroup G} (hL : IsGomiChevTwo ↥L)
    (h1 : ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨
      IsGomiSz (↥L ⧸ center ↥L)))
    (hI : IsPGroup 2 I) (hIL : I ≤ normalizer (L : Set G)) (hU : IsSylowOf 2 U L)
    (hIU : I ≤ normalizer (U : Set G))
    (hiso : IsPIsolatedOver 2 (L ⊓ centralizer (I : Set G)) ⊥) :
    ∃ a ∈ I, ∃ A : Subgroup G, IsGomiAtom L U A ∧
      A.map (MulAut.conj a).toMonoidHom ≠ A ∧
      A ⊔ A.map (MulAut.conj a).toMonoidHom = L := by
  have hgen : ∃ A : Subgroup G, IsGomiAtom L U A ∧
      (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) = L := by
    by_contra hno
    push Not at hno
    exact (hFix G L I U hL h1 hI hIL hU hIU hno) hiso
  obtain ⟨A, hA, hAgen⟩ := hgen
  by_cases hfix : ∀ i ∈ I, A.map (MulAut.conj i).toMonoidHom = A
  · have hsup_le : (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≤ A :=
      iSup₂_le fun i hi => le_of_eq (hfix i hi)
    have hAL : A = L := le_antisymm hA.2.1 (by rw [← hAgen]; exact hsup_le)
    exact absurd (isGomiL2_or_isGomiU3_or_isGomiSz_of_isGomiAtom_self hBT hB hL hU
      (hAL ▸ hA)) h1
  · push Not at hfix
    obtain ⟨a, ha, hAa⟩ := hfix
    have hle : (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≤
        A ⊔ A.map (MulAut.conj a).toMonoidHom := by
      refine iSup₂_le fun i hi => ?_
      rcases hOrb G L U I A hL hU hI hIL hIU hA i hi a ha with h | h | h
      · rw [h]; exact le_sup_left
      · exact absurd h hAa
      · rw [h]; exact le_sup_right
    have hsup : A ⊔ A.map (MulAut.conj a).toMonoidHom = L := by
      refine le_antisymm (sup_le hA.2.1 ?_) (by rw [← hAgen]; exact hle)
      calc A.map (MulAut.conj a).toMonoidHom
          ≤ L.map (MulAut.conj a).toMonoidHom :=
            Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hA.2.1
        _ = L := (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hIL ha)
    exact ⟨a, ha, A, hA, hAa, hsup⟩

theorem gomiChevIsolated_of_gomiChevFixedTypes (hBT : GomiChevBorelTits) (hB : GomiBender)
    (hOrb : GomiChevAtomOrbit) (hSwap : GomiChevSwap) (hFix : GomiChevFixedTypes) :
    GomiChevIsolated := by
  intro G _ _ L I hL hI hIL hiso
  by_cases h1 : IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨
      IsGomiSz (↥L ⧸ center ↥L)
  · left; exact h1
  · right
    refine ⟨?_, ?_⟩
    · obtain ⟨U₀, hU₀, hIU₀⟩ :=
        CFSG.ComponentClassification.Asc76.Sec4.exists_isSylowOf_normalized hI hIL
      obtain ⟨a, ha, A, hA, hmove, hsup⟩ :=
        gomiChevAtom_moved_of_fixedTypes hBT hB hOrb hFix hL h1 hI hIL hU₀ hIU₀ hiso
      exact hSwap G L U₀ A hL hU₀ hA a ⟨hIL ha, hIU₀ ha⟩ hmove hsup
    · intro U hU hIU
      obtain ⟨a, ha, A, hA, hmove, hsup⟩ :=
        gomiChevAtom_moved_of_fixedTypes hBT hB hOrb hFix hL h1 hI hIL hU hIU hiso
      refine ⟨a, ha, A, hA.1, ?_, ?_⟩
      · refine lt_of_le_of_ne hA.2.1 ?_
        intro hAL
        apply hmove
        rw [hAL]
        exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hIL ha)
      · intro hna
        exact hmove ((Subgroup.mem_normalizer_iff_map_conj_eq).mp hna)

end CFSG.GroupTheory
