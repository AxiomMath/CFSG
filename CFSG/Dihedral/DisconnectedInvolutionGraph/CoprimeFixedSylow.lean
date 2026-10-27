module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeConjugators

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]
variable {A : Type*} [Group A] [MulDistribMulAction A G]

theorem coprime_pgroup_fixed_sylow [Finite G]
    (actorPrime sylowPrime : ℕ) [Fact (Nat.Prime actorPrime)] [Fact (Nat.Prime sylowPrime)]
    (hpgroup : IsPGroup actorPrime A) (hcoprime : ¬ actorPrime ∣ Nat.card G)
    (sylow : Sylow sylowPrime G)
    (hinvariant : InvariantSubgroup (A := A) (sylow : Subgroup G)) :
    ∃ fixedSylow : Sylow sylowPrime (FixedPoints.subgroup A G),
      (fixedSylow : Subgroup (FixedPoints.subgroup A G)) =
        (sylow : Subgroup G).subgroupOf (FixedPoints.subgroup A G) := by
  let fixed := FixedPoints.subgroup A G
  let restricted := (sylow : Subgroup G).subgroupOf fixed
  have hrestrictedP : IsPGroup sylowPrime restricted := sylow.isPGroup'.comap_subtype
  obtain ⟨fixedSylow, hcontained⟩ := hrestrictedP.exists_le_sylow
  let embedded := (fixedSylow : Subgroup fixed).map fixed.subtype
  have hembeddedP : IsPGroup sylowPrime embedded :=
    fixedSylow.isPGroup'.map fixed.subtype
  have hembeddedFixed : embedded ≤ fixed := by
    rintro element ⟨original, _, rfl⟩
    exact original.property
  have hembeddedInvariant : InvariantSubgroup (A := A) embedded := by
    intro actor element hmem
    rw [FixedPoints.mem_subgroup A G element |>.mp (hembeddedFixed hmem) actor]
    exact hmem
  obtain ⟨larger, hembeddedLe, hlargerInvariant⟩ :=
    coprime_pgroup_invariant_sylow_containment actorPrime sylowPrime hpgroup hcoprime
      embedded hembeddedP hembeddedInvariant
  obtain ⟨conjugator, hfixed, hconjugates⟩ := coprime_pgroup_invariant_sylows_conjugate
    actorPrime sylowPrime hpgroup hcoprime sylow larger hinvariant hlargerInvariant
  have hnormalizes : conjugator ∈ Subgroup.normalizer (fixed : Set G) :=
    fixed.le_normalizer ((FixedPoints.mem_subgroup A G conjugator).mpr hfixed)
  have hmapFixed : fixed.map (MulAut.conj conjugator).toMonoidHom = fixed :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormalizes
  have hmapSylow : (sylow : Subgroup G).map (MulAut.conj conjugator).toMonoidHom =
      (larger : Subgroup G) := by
    rw [← sylow_smul_subgroup_eq_map, hconjugates]
  have hmapIntersection : ((sylow : Subgroup G) ⊓ fixed).map
      (MulAut.conj conjugator).toMonoidHom = (larger : Subgroup G) ⊓ fixed := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj conjugator).injective, hmapSylow, hmapFixed]
  have hcardIntersections : Nat.card ↥((larger : Subgroup G) ⊓ fixed) =
      Nat.card ↥((sylow : Subgroup G) ⊓ fixed) := by
    rw [← hmapIntersection]
    exact Subgroup.card_map_of_injective (MulAut.conj conjugator).injective
  have hrestrictedMap : restricted.map fixed.subtype = (sylow : Subgroup G) ⊓ fixed := by
    ext element
    constructor
    · rintro ⟨original, horiginal, rfl⟩
      exact ⟨horiginal, original.property⟩
    · rintro ⟨hsylow, hfixed⟩
      exact Subgroup.mem_map.mpr ⟨⟨element, hfixed⟩, hsylow, rfl⟩
  have hembeddedLeIntersection : embedded ≤ (larger : Subgroup G) ⊓ fixed :=
    le_inf hembeddedLe hembeddedFixed
  have hcardRestricted : Nat.card ↥((sylow : Subgroup G) ⊓ fixed) =
      Nat.card restricted := by
    rw [← hrestrictedMap]
    exact Subgroup.card_map_of_injective fixed.subtype_injective
  have hcardEmbedded : Nat.card embedded = Nat.card fixedSylow :=
    Subgroup.card_map_of_injective fixed.subtype_injective
  have hcardLe : Nat.card fixedSylow ≤ Nat.card restricted := by
    rw [← hcardEmbedded, ← hcardRestricted, ← hcardIntersections]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hembeddedLeIntersection)
      (Subgroup.inclusion_injective hembeddedLeIntersection)
  exact ⟨fixedSylow, (Subgroup.eq_of_le_of_card_ge hcontained hcardLe).symm⟩

end CFSG.DisconnectedInvolutionGraph.Helpers
