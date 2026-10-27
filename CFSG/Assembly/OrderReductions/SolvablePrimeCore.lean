module

public import CFSG.Assembly.OrderReductions.PrimeCore

public section

namespace CFSG.OrderReductions.SolvablePrimeCore

theorem centralizer_characteristic {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] :
    (Subgroup.centralizer (subgroup : Set group)).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro automorphism
  have image_le := Subgroup.map_centralizer_le_centralizer_image (subgroup : Set group)
    automorphism.toMonoidHom
  have image_eq : automorphism.toMonoidHom '' (subgroup : Set group) = subgroup := by
    rw [← Subgroup.coe_map]
    exact congrArg (fun current : Subgroup group => (current : Set group))
      ((Subgroup.characteristic_iff_map_eq.mp (inferInstance : subgroup.Characteristic)) automorphism)
  rwa [image_eq] at image_le

theorem nilpotent_of_commutator_le_center {group : Type*} [Group group]
    (commutator_central : commutator group ≤ Subgroup.center group) :
    Group.IsNilpotent group := by
  apply Subgroup.isNilpotent_of_ker_le_center (Abelianization.of (G := group))
  rwa [Abelianization.ker_of]

theorem subgroup_nilpotent_of_commutator_central {group : Type*} [Group group]
    (subgroup : Subgroup group)
    (commutator_central : subgroup ≤ Subgroup.centralizer (↑⁅subgroup, subgroup⁆ : Set group)) :
    Group.IsNilpotent subgroup := by
  apply nilpotent_of_commutator_le_center
  intro element element_mem
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply Subtype.ext
  have image_mem : subgroup.subtype element ∈ ⁅subgroup, subgroup⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map.mpr ⟨element, element_mem, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp (commutator_central other.property) element.val image_mem).symm

theorem centralizer_primeCore_le {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group = ⊥) :
    Subgroup.centralizer (CFSG.OrderReductions.PrimeCore.primeCore prime group : Set group) ≤
      CFSG.OrderReductions.PrimeCore.primeCore prime group := by
  let core := CFSG.OrderReductions.PrimeCore.primeCore prime group
  let centralizer := Subgroup.centralizer (core : Set group)
  have : centralizer.Characteristic := centralizer_characteristic core
  let series := fun depth => (derivedSeries centralizer depth).map centralizer.subtype
  have series_normal : ∀ depth, (series depth).Normal := by
    intro depth
    exact CFSG.OrderReductions.OddCore.characteristic_subgroup_map_normal centralizer _
  have series_le : ∀ depth, series depth ≤ centralizer :=
    fun depth => Subgroup.map_subtype_le (derivedSeries centralizer depth)
  have downward : ∀ depth, series (depth + 1) ≤ core → series depth ≤ core := by
    intro depth next_le
    have : (series depth).Normal := series_normal depth
    have commutator_le : ⁅series depth, series depth⁆ ≤ core := by
      change ⁅(derivedSeries centralizer depth).map centralizer.subtype,
        (derivedSeries centralizer depth).map centralizer.subtype⁆ ≤ core
      rw [← Subgroup.map_commutator, ← derivedSeries_succ]
      exact next_le
    have commutator_central : series depth ≤
        Subgroup.centralizer (↑⁅series depth, series depth⁆ : Set group) :=
      (series_le depth).trans (Subgroup.centralizer_le commutator_le)
    have : Group.IsNilpotent (series depth) :=
      subgroup_nilpotent_of_commutator_central (series depth) commutator_central
    exact CFSG.OrderReductions.PrimeCore.nilpotent_normal_le_primeCore prime core_bot (series depth)
  obtain ⟨bound, series_bot⟩ := (Group.isSolvable_def centralizer).mp inferInstance
  have descend : ∀ distance depth, depth + distance = bound → series depth ≤ core := by
    intro distance
    induction distance with
    | zero =>
        intro depth equation
        have equal_depth : depth = bound := by omega
        dsimp [series]
        rw [equal_depth, series_bot, Subgroup.map_bot]
        exact bot_le
    | succ distance induction_hypothesis =>
        intro depth equation
        exact downward depth (induction_hypothesis (depth + 1) (by omega))
  have result := descend bound 0 (by omega)
  simpa [series, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.subtype_range] using result

theorem quotient_centralizer_primeCore_le {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] :
    Subgroup.centralizer (CFSG.OrderReductions.PrimeCore.primeCore prime
      (group ⧸ CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group) :
        Set (group ⧸ CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group)) ≤
      CFSG.OrderReductions.PrimeCore.primeCore prime
        (group ⧸ CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group) :=
  centralizer_primeCore_le prime (CFSG.OrderReductions.PrimeComplementCore.core_quotient_eq_bot prime group)

end CFSG.OrderReductions.SolvablePrimeCore
