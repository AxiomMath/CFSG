module

public import CFSG.LargeExtraspecial.AS35CS63Res
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.Quasithin.Background.KnownMultOdd
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S63

theorem isPGroup_two_ker_of_J2 {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* Blueprint.NativeSporadic.J2) (hπ : Function.Surjective π)
    (hC : π.ker ≤ center E) : IsPGroup 2 π.ker := by
  have : Finite Blueprint.NativeSporadic.J2 := Finite.of_surjective π hπ
  have hcard := Sporadic.J2.card_J2
  refine Quasithin.isPGroup_two_of_forall_odd_sylow_eq_bot fun r hr hr2 _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
      SectionRank.J2_sylow3_cubic_witness
    exact SectionRank.OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy
      hQ (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  by_cases h5 : r = 5
  · subst h5
    obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := SectionRank.J2_sylow5_square_witness
    exact SectionRank.sylow_kernel_eq_bot_of_square_witness π hπ hC hx hy hxy hQ
      (by rw [hcard]; decide) hhx hhy (by decide +revert) Cp
  have hsq : ¬ r ^ 2 ∣ Nat.card Blueprint.NativeSporadic.J2 := by
    rw [hcard, show 604800 = (2 ^ 7 * 3 ^ 3 * 5 ^ 2) * [7].prod by norm_num]
    exact SectionRank.not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (SectionRank.coprime_pow_of_ne hr Nat.prime_two hr2 _)
        (SectionRank.coprime_pow_of_ne hr Nat.prime_three h3 _))
      (SectionRank.coprime_pow_of_ne hr (by norm_num) h5 _)) _ (by norm_num) (by decide)
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r Blueprint.NativeSporadic.J2))
  exact ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cp Q
    (SectionRank.sylow_isCyclic_of_not_sq_dvd hsq Q)

theorem j2SchurInput : J2SchurInput := by
  intro Y _ _ hperf hJ
  obtain ⟨e⟩ := hJ
  have : Group.IsPerfect Y := Group.isPerfect_def.2 hperf
  let π : Y →* Blueprint.NativeSporadic.J2 := e.toMonoidHom.comp (QuotientGroup.mk' (center Y))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center Y := Quasithin.ker_mk_comp_mulEquiv (center Y) e
  have h2 : IsPGroup 2 (center Y) := hker ▸ isPGroup_two_ker_of_J2 π hπ hker.le
  have hs : IsSimpleGroup (Y ⧸ center Y) :=
    @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.J2.isSimpleGroup_J2 e
  exact ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound Y
    ⟨hperf, hs⟩ h2 (Or.inr ⟨e⟩)

end S63

end CFSG.LargeExtraspecial
