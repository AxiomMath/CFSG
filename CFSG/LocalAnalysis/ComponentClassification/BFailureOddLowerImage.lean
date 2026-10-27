module

public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents

public section

namespace CFSG.ComponentClassification.BFailureOdd

open CFSG CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem badSubgroup_eq_badTwoComponentSubgroup (X : Type*) [Group X] :
    TwoComponents.badSubgroup X = badTwoComponentSubgroup X := by
  unfold TwoComponents.badSubgroup badTwoComponentSubgroup
  congr 1
  ext L
  exact and_congr (CatalogueBAlternating.pComponent_two_iff L).symm
    (not_congr CatalogueBAlternating.quasisimple_iff_native.symm)

theorem badTwoComponentSubgroup_le_map_of_odd_kernel {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) :
    badTwoComponentSubgroup H ≤ (badTwoComponentSubgroup G).map f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker2 : ¬ 2 ∣ Nat.card f.ker := by
    obtain ⟨m, hm⟩ := hker
    omega
  have hbij := (prime_complement_quotient_p_component_bijection f hf hker2).1
  refine sSup_le fun M hM => ?_
  obtain ⟨L, hL, hLM⟩ := hbij.surjOn hM.1
  have hrange : (f.comp L.subtype).range = M := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hLM
  have hLq : ¬ IsQuasisimple L := by
    intro hq
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq (f.comp L.subtype)
      with hbot | himage
    · exact pComponent_ne_bot hM.1 (hrange ▸ hbot)
    · exact hM.2 (hrange ▸ himage)
  rw [← hLM]
  exact Subgroup.map_mono (le_sSup ⟨hL, hLq⟩)

theorem odd_quotient_bad_subgroup_lower_image {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] (f : G →* H) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) :
    TwoComponents.badSubgroup H ≤ (TwoComponents.badSubgroup G).map f := by
  rw [badSubgroup_eq_badTwoComponentSubgroup, badSubgroup_eq_badTwoComponentSubgroup]
  exact badTwoComponentSubgroup_le_map_of_odd_kernel f hf hker

end CFSG.ComponentClassification.BFailureOdd
