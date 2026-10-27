module

public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily
public import CFSG.LocalAnalysis.ComponentClassification.CoprimeInvariantSylow

public section

namespace CFSG.ComponentClassification.TwoActionInvariantSylow

theorem exists_invariant {Acting Ambient : Type*} [Group Acting] [Group Ambient] [Finite Ambient]
    (htwo : IsPGroup 2 Acting) (homomorphism : Acting →* MulAut Ambient) :
    ∃ sylow : Sylow 2 Ambient, ∀ actor : Acting,
      (sylow : Subgroup Ambient).map (homomorphism actor).toMonoidHom = sylow := by
  let := CoprimeInvariantSylow.action 2 homomorphism
  have hnot : ¬ 2 ∣ Nat.card (Sylow 2 Ambient) := by
    have hmod := card_sylow_modEq_one 2 Ambient
    intro hdivides
    have hzero := Nat.mod_eq_zero_of_dvd hdivides
    change Nat.card (Sylow 2 Ambient) % 2 = 1 % 2 at hmod
    omega
  obtain ⟨fixed, hfixed⟩ := htwo.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 Ambient) hnot
  refine ⟨fixed, fun actor => ?_⟩
  have heq := MulAction.mem_fixedPoints.mp hfixed actor
  have hsubgroup := congrArg (fun sylow : Sylow 2 Ambient => (sylow : Subgroup Ambient)) heq
  exact (CoprimeInvariantSylow.image_subgroup 2 (homomorphism actor) fixed).symm.trans hsubgroup

theorem subgroup {G : Type*} [Group G] [Finite G] (ambient acting : Subgroup G)
    (htwo : IsPGroup 2 acting) (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G)) :
    ∃ sylow : Sylow 2 ambient,
      acting ≤ Subgroup.normalizer ((((sylow : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G)) := by
  let action := ambient.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes)
  obtain ⟨sylow, hinvariant⟩ := exists_invariant htwo action
  refine ⟨sylow, ?_⟩
  intro actor hactor
  apply (CommutingComponentFamily.normalizer_iff_conjugate_eq _ actor).mpr
  have hmap := congrArg (Subgroup.map ambient.subtype) (hinvariant (⟨actor, hactor⟩ : acting))
  rw [Subgroup.map_map]
  rw [Subgroup.map_map] at hmap
  convert hmap using 1
  congr 1

end CFSG.ComponentClassification.TwoActionInvariantSylow
