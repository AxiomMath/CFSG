module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinSubnormal

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem core_ne_top {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    pPrimeCore p L ≠ ⊤ := by
  intro htop
  let : Nontrivial (L ⧸ pPrimeCore p L) := Quasisimple.nontrivial
    (CatalogueBAlternating.quasisimple_iff_native.mp
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple p L hL))
  have hsubsingleton : Subsingleton (L ⧸ pPrimeCore p L) :=
    QuotientGroup.subsingleton_iff.mpr htop
  exact not_subsingleton _ hsubsingleton

theorem quasisimple_iff_core_central {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L ↔ pPrimeCore p L ≤ Subgroup.center L := by
  constructor
  · intro hquasisimple
    exact Quasisimple.normal_le_center_of_ne_top
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasisimple) _ (core_ne_top p L hL)
  · intro hcentral
    let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
    exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (CentralExtensions.quasisimple_of_surjective
        (CatalogueBAlternating.quasisimple_iff_native.mp
          (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple p L hL))
        (QuotientGroup.mk' (pPrimeCore p L)) (QuotientGroup.mk'_surjective _)
        (by rwa [QuotientGroup.ker_mk']))

theorem mutual_normalization_core_commutation {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (K L : Subgroup G)
    (hK : CFSG.IsPComponent p K) (hL : CFSG.IsPComponent p L) (hne : K ≠ L) :
    L ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅K, L⁆ ≤ (pPrimeCore p K).map K.subtype ⊓ (pPrimeCore p L).map L.subtype := by
  have hKnotLe : ¬ K ≤ L := fun hle => hne (eq_of_le p K L hK hL hle)
  have hLnotLe : ¬ L ≤ K := fun hle => hne (eq_of_le p L K hL hK hle).symm
  obtain ⟨hLnormalizes, hKcore⟩ :=
    (contains_or_normalizes_core p K L hK hL.choose_spec.2.1).resolve_left hKnotLe
  obtain ⟨hKnormalizes, hLcore⟩ :=
    (contains_or_normalizes_core p L K hL hK.choose_spec.2.1).resolve_left hLnotLe
  rw [Subgroup.commutator_comm L K] at hLcore
  exact ⟨hLnormalizes, hKnormalizes, le_inf hKcore hLcore⟩

theorem commutes_of_quasisimple_left {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (K L : Subgroup G)
    (hK : CFSG.IsPComponent p K) (hL : CFSG.IsPComponent p L) (hne : K ≠ L)
    (hquasisimple : CFSG.IsQuasisimple K) : ⁅K, L⁆ = ⊥ := by
  have hcore := (mutual_normalization_core_commutation p K L hK hL hne).2.2
  have hcentral := (quasisimple_iff_core_central p K hK).mp hquasisimple
  have hcenter : ⁅K, L⁆ ≤ (Subgroup.center K).map K.subtype :=
    (hcore.trans inf_le_left).trans (Subgroup.map_mono hcentral)
  have hdouble : ⁅⁅K, L⁆, K⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    apply hcenter.trans
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy (⟨z, hz⟩ : K))
  let : Group.IsPerfect K := CatalogueBAlternating.pComponent_perfect hK
  exact Quasisimple.perfect_double_commutator K L hdouble

theorem commutes_of_quasisimple {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (K L : Subgroup G)
    (hK : CFSG.IsPComponent p K) (hL : CFSG.IsPComponent p L) (hne : K ≠ L)
    (hquasisimple : CFSG.IsQuasisimple K ∨ CFSG.IsQuasisimple L) : ⁅K, L⁆ = ⊥ := by
  rcases hquasisimple with hKquasisimple | hLquasisimple
  · exact commutes_of_quasisimple_left p K L hK hL hne hKquasisimple
  · rw [Subgroup.commutator_comm]
    exact commutes_of_quasisimple_left p L K hL hK hne.symm hLquasisimple

theorem distinct_p_components_core_commutation {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (K L : Subgroup G)
    (hK : CFSG.IsPComponent p K) (hL : CFSG.IsPComponent p L) :
    (K ≤ L → K = L) ∧ (K ≠ L →
      L ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅K, L⁆ ≤ (pPrimeCore p K).map K.subtype ⊓ (pPrimeCore p L).map L.subtype ∧
      (CFSG.IsQuasisimple K ∨ CFSG.IsQuasisimple L → ⁅K, L⁆ = ⊥)) := by
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨fun hle => eq_of_le p K L hK hL hle, ?_⟩
  intro hne
  obtain ⟨hLnormalizes, hKnormalizes, hcore⟩ :=
    mutual_normalization_core_commutation p K L hK hL hne
  exact ⟨hLnormalizes, hKnormalizes, hcore,
    fun hquasisimple => commutes_of_quasisimple p K L hK hL hne hquasisimple⟩

end CFSG.ComponentClassification.CatalogueBPrimeJoin
