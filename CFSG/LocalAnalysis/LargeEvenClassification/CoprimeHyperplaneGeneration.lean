module

public import CFSG.LocalAnalysis.LargeEvenClassification.PGroupHyperplaneGeneration

public section

namespace CFSG.LargeEvenClassification.Helpers

universe actingUniverse groupUniverse

@[expose] def invariantSubgroupAction {Acting : Type actingUniverse} [Group Acting]
    {Ambient : Type groupUniverse} [Group Ambient] (action : Acting →* MulAut Ambient)
    (Invariant : Subgroup Ambient)
    (hstable : ∀ element : Acting, ∀ source : Ambient, source ∈ Invariant → action element source ∈ Invariant) :
    Acting →* MulAut Invariant where
  toFun := fun element => {
    toFun := fun source => ⟨action element source, hstable element source source.property⟩
    invFun := fun source => ⟨action element⁻¹ source, hstable element⁻¹ source source.property⟩
    left_inv := by
      intro source
      apply Subtype.ext
      change action element⁻¹ (action element source) = source
      rw [map_inv]
      exact (action element).symm_apply_apply source
    right_inv := by
      intro source
      apply Subtype.ext
      change action element (action element⁻¹ source) = source
      rw [map_inv]
      exact (action element).apply_symm_apply source
    map_mul' := by
      intro first second
      apply Subtype.ext
      exact map_mul (action element) first.val second.val }
  map_one' := by
    apply MulEquiv.ext
    intro source
    apply Subtype.ext
    change action 1 source = source
    rw [map_one]
    rfl
  map_mul' := by
    intro first second
    apply MulEquiv.ext
    intro source
    apply Subtype.ext
    change action (first * second) source = action first (action second source)
    rw [map_mul]
    rfl

theorem coprime_hyperplane_fixed_generation {Acting : Type actingUniverse} [CommGroup Acting]
    [Finite Acting] {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpacting : IsPGroup prime Acting)
    (hexponent : ∀ element : Acting, element ^ prime = 1) (action : Acting →* MulAut Ambient)
    (hcoprime : ¬prime ∣ Nat.card Ambient) : hyperplaneFixedSpan prime action = ⊤ := by
  let Generators := hyperplaneFixedSpan prime action
  apply Subgroup.index_eq_one.mp
  by_contra hindex
  obtain ⟨sylowPrime, hsylowPrime, hdividesIndex⟩ := Nat.exists_prime_and_dvd hindex
  let : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  have hneq : prime ≠ sylowPrime := by
    intro heq
    exact hcoprime (heq ▸ hdividesIndex.trans (Subgroup.index_dvd_card Generators))
  obtain ⟨SylowSubgroup, hstable⟩ := coprime_action_invariant_sylow hprime hsylowPrime hpacting action hcoprime
  let restrictedAction := invariantSubgroupAction action (SylowSubgroup : Subgroup Ambient) (by
    intro element source hsource
    have hmem : action element source ∈ (SylowSubgroup : Subgroup Ambient).map
        (action element).toMonoidHom := Subgroup.mem_map.mpr ⟨source, hsource, rfl⟩
    rw [hstable element] at hmem
    exact hmem)
  have hgenerates := pGroup_hyperplane_fixed_generation hprime hsylowPrime hneq hpacting hexponent
    SylowSubgroup.isPGroup' restrictedAction
  have hspanLe : hyperplaneFixedSpan prime restrictedAction ≤ Generators.comap (SylowSubgroup : Subgroup Ambient).subtype := by
    apply iSup_le
    intro Fixers source hsource
    apply fixed_subgroup_le_hyperplane_span action Fixers.val Fixers.property
    intro element
    exact congrArg (fun entry : (SylowSubgroup : Subgroup Ambient) => entry.val) (hsource element)
  rw [hgenerates] at hspanLe
  have hsylowLe : (SylowSubgroup : Subgroup Ambient) ≤ Generators := by
    intro source hsource
    exact hspanLe (Subgroup.mem_top (⟨source, hsource⟩ : (SylowSubgroup : Subgroup Ambient)))
  exact SylowSubgroup.not_dvd_index (hdividesIndex.trans (Subgroup.index_dvd_of_le hsylowLe))

end CFSG.LargeEvenClassification.Helpers
