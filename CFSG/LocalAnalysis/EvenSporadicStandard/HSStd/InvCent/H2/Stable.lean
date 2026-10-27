module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.StableA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.StableB

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem mem_normalizer_of_mem_kleinV [Finite G] (cfg : H2Cfg G t v J)
    (hF : fittingSubgroup G = ⊥) {L : Subgroup G} (hL : IsComponent L) {w : G}
    (hw : w ∈ kleinV t v) : w ∈ normalizer (L : Set G) := by
  by_contra hwL
  have hw1 : w ≠ 1 := fun h => hwL (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨u, hu, hu1, huw⟩ := cfg.exists_other hw hw1
  have hwu1 : w * u ≠ 1 := by
    intro h
    have h2 : w * (w * u) = w * 1 := by rw [h]
    rw [← mul_assoc, cfg.sq_eq_one_of_mem hw, one_mul, mul_one] at h2
    exact huw h2
  by_cases huL : u ∈ normalizer (L : Set G)
  · exact stable_aux_A cfg hF hL hw hu hu1 hwL huL
  · by_cases hwuL : w * u ∈ normalizer (L : Set G)
    · exact stable_aux_A cfg hF hL hw (mul_mem hw hu) hwu1 hwL hwuL
    · exact stable_aux_B cfg hF hL hw hu hwL huL hwuL

theorem conj_mem_of_component [Finite G] (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    {L : Subgroup G} (hL : IsComponent L) {x : G} (hx : x ∈ L) : t * x * t⁻¹ ∈ L := by
  have ht : t ∈ normalizer (L : Set G) :=
    mem_normalizer_of_mem_kleinV cfg hF hL cfg.t_mem_kleinV
  exact ((Subgroup.mem_normalizer_iff (H := L)).1 ht x).1 hx

theorem conj_mem_rest [Finite G] (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    {L : Subgroup G} {x : G} (hx : x ∈ Rest G L L) : t * x * t⁻¹ ∈ Rest G L L := by
  have hle : Rest G L L ≤ (Rest G L L).comap (MulAut.conj t).toMonoidHom := by
    refine sSup_le fun M ⟨hM, hML1, hML2⟩ => ?_
    intro y hy
    have hMle : M ≤ Rest G L L :=
      le_sSup (s := {N : Subgroup G | IsComponent N ∧ N ≠ L ∧ N ≠ L}) ⟨hM, hML1, hML2⟩
    exact hMle (conj_mem_of_component cfg hF hM hy)
  exact hle hx

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
