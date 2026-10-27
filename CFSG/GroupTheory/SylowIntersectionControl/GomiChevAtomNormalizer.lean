module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

private theorem mem_normalizer_of_map_conj_le_can {G : Type} [Group G] [Finite G]
    {P : Subgroup G} {s : G} (h : P.map (MulAut.conj s).toMonoidHom ≤ P) :
    s ∈ normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge h ?_
  exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj s).injective).symm

private theorem map_conj_le_of_isGomiAtom_can (hOrb : GomiChevAtomOrbit)
    {G : Type} [Group G] [Finite G] {L U T H P A : Subgroup G}
    (hL : IsGomiChevTwo ↥L) (hU : IsSylowOf 2 U L) (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hHT : H ≤ T) (hHP : H ≤ normalizer (P : Set G))
    (hA : IsGomiAtom L U A) (hAP : A ≤ P)
    (hmoveA : ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A) {s : G} (hs : s ∈ T) :
    A.map (MulAut.conj s).toMonoidHom ≤ P := by
  obtain ⟨h, hhH, hhne⟩ := hmoveA
  have hhT : h ∈ T := hHT hhH
  rcases hOrb G L U T A hL hU hT hTL hTU hA h hhT s hs with h1 | h2 | h3
  · exact absurd h1 hhne
  · rwa [h2]
  · rw [← h3]
    calc A.map (MulAut.conj h).toMonoidHom ≤ P.map (MulAut.conj h).toMonoidHom :=
          Subgroup.map_mono hAP
      _ = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hhH)

theorem le_normalizer_of_forall_isGomiAtom (hGen : GomiChevAtomGeneration)
    (hOrb : GomiChevAtomOrbit) {G : Type} [Group G] [Finite G] {L U T H P : Subgroup G}
    (hL : IsGomiChevTwo ↥L) (hU : IsSylowOf 2 U L) (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G)) (hHT : H ≤ T)
    (hHP : H ≤ normalizer (P : Set G)) (hUP : L ⊓ normalizer (U : Set G) ≤ P) (hPL : P ≤ L)
    (hmove : ∀ A : Subgroup G, IsGomiAtom L U A → A ≤ P →
      ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A) :
    T ≤ normalizer (P : Set G) := by
  intro s hs
  refine mem_normalizer_of_map_conj_le_can ?_
  have hLN : (L ⊓ normalizer (U : Set G)).map (MulAut.conj s).toMonoidHom ≤ P := by
    have hLs : L.map (MulAut.conj s).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTL hs)
    have hUs : U.map (MulAut.conj s).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTU hs)
    have hNs : s ∈ normalizer (normalizer (U : Set G)) :=
      (show normalizer (U : Set G) ≤ normalizer (normalizer (U : Set G)) from
        Subgroup.le_normalizer) (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hUs)
    have hNmap : (normalizer (U : Set G)).map (MulAut.conj s).toMonoidHom =
        normalizer (U : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hNs
    refine (le_inf ?_ ?_).trans hUP
    · calc (L ⊓ normalizer (U : Set G)).map (MulAut.conj s).toMonoidHom
          ≤ L.map (MulAut.conj s).toMonoidHom := Subgroup.map_mono inf_le_left
        _ = L := hLs
    · calc (L ⊓ normalizer (U : Set G)).map (MulAut.conj s).toMonoidHom
          ≤ (normalizer (U : Set G)).map (MulAut.conj s).toMonoidHom :=
            Subgroup.map_mono inf_le_right
        _ = normalizer (U : Set G) := hNmap
  have hSsup : (sSup {A | IsGomiAtom L U A ∧ A ≤ P}).map
      (MulAut.conj s).toMonoidHom ≤ P := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro A hA
    rw [← Subgroup.map_le_iff_le_comap]
    exact map_conj_le_of_isGomiAtom_can hOrb hL hU hT hTL hTU hHT hHP hA.1 hA.2
      (hmove A hA.1 hA.2) hs
  have hgen := hGen G L U P hL hU hUP hPL
  refine (Subgroup.map_mono hgen).trans ?_
  rw [Subgroup.map_sup]
  exact sup_le hLN hSsup

theorem le_normalizer_sup_map_conj (hOrb : GomiChevAtomOrbit) {G : Type} [Group G] [Finite G]
    {L U T A : Subgroup G} (hL : IsGomiChevTwo ↥L) (hU : IsSylowOf 2 U L) (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hA : IsGomiAtom L U A) {t : G} (ht : t ∈ T)
    (hAt : A.map (MulAut.conj t).toMonoidHom ≠ A) :
    T ≤ normalizer ((A ⊔ A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro s hs
  refine mem_normalizer_of_map_conj_le_can ?_
  rw [Subgroup.map_sup, Subgroup.map_conj_map_conj]
  refine sup_le ?_ ?_
  · rcases hOrb G L U T A hL hU hT hTL hTU hA t ht s hs with h1 | h2 | h3
    · exact absurd h1 hAt
    · rw [h2]; exact le_sup_left
    · rw [h3]; exact le_sup_right
  · have hst : s * t ∈ T := T.mul_mem hs ht
    rcases hOrb G L U T A hL hU hT hTL hTU hA t ht (s * t) hst with h1 | h2 | h3
    · exact absurd h1 hAt
    · rw [h2]; exact le_sup_left
    · rw [h3]; exact le_sup_right

end CFSG.GroupTheory
