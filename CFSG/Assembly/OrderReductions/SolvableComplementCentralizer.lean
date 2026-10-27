module

public import CFSG.Assembly.OrderReductions.SolvablePrimeCore

public section

namespace CFSG.OrderReductions.SolvableComplementCentralizer

open CFSG.OrderReductions.PrimeCore CFSG.OrderReductions.PrimeComplementCore

theorem nilpotent_normal_le_complementCore {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (core_bot : primeCore prime group = ⊥)
    (normal : Subgroup group) [normal.Normal] [Group.IsNilpotent normal] :
    normal ≤ primeComplementCore prime group := by
  apply normal_le_primeComplementCore prime normal
  intro divides
  obtain ⟨sylow⟩ := Sylow.nonempty (p := prime) (G := normal)
  have : (sylow : Subgroup normal).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent sylow
  have : (sylow : Subgroup normal).Characteristic := sylow.characteristic_of_normal inferInstance
  let image := (sylow : Subgroup normal).map normal.subtype
  have : image.Normal := CFSG.OrderReductions.OddCore.characteristic_subgroup_map_normal normal _
  have image_le := normal_le_primeCore prime image (sylow.isPGroup'.map normal.subtype)
  rw [core_bot] at image_le
  have image_bot := le_bot_iff.mp image_le
  have concrete_image_bot : (sylow : Subgroup normal).map normal.subtype = ⊥ := image_bot
  have card_one : Nat.card (sylow : Subgroup normal) = 1 := by
    rw [← Subgroup.card_map_of_injective (f := normal.subtype) Subtype.val_injective, concrete_image_bot,
      Subgroup.card_bot]
  have sylow_divides := sylow.dvd_card_of_dvd_card divides
  rw [card_one] at sylow_divides
  exact (Fact.out : Nat.Prime prime).not_dvd_one sylow_divides

theorem centralizer_complementCore_le {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : primeCore prime group = ⊥) :
    Subgroup.centralizer (primeComplementCore prime group : Set group) ≤
      primeComplementCore prime group := by
  let core := primeComplementCore prime group
  let centralizer := Subgroup.centralizer (core : Set group)
  have : centralizer.Characteristic := CFSG.OrderReductions.SolvablePrimeCore.centralizer_characteristic core
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
      CFSG.OrderReductions.SolvablePrimeCore.subgroup_nilpotent_of_commutator_central (series depth) commutator_central
    exact nilpotent_normal_le_complementCore prime core_bot (series depth)
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

end CFSG.OrderReductions.SolvableComplementCentralizer
