module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ComponentClassification.SolvableRadical
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.ComponentClassification
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem abelian_normal_eq_bot (hO : pPrimeCore 2 X = ⊥) (hO2 : pCore 2 X = ⊥) (M : Subgroup X)
    [hMn : M.Normal] (hM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) : M = ⊥ := by
  by_cases h2 : 2 ∣ Nat.card M
  · exfalso
    let P : Sylow 2 M := default
    have hcM : ∀ a b : M, a * b = b * a := fun a b => Subtype.ext (hM a a.2 b b.2)
    have hPn : (P : Subgroup M).Normal := ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by rw [hcM g n, mul_inv_cancel_right]
      rw [this]
      exact hn⟩
    have hPc : (P : Subgroup M).Characteristic := Sylow.characteristic_of_normal P hPn
    have hXn : ((P : Subgroup M).map M.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hP2 : IsPGroup 2 ((P : Subgroup M).map M.subtype) := P.isPGroup'.map M.subtype
    have hle : (P : Subgroup M).map M.subtype ≤ pCore 2 X := le_sSup ⟨hXn, hP2⟩
    rw [hO2, le_bot_iff] at hle
    have hP1 : (P : Subgroup M) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 hle
    have hdvd : 2 ∣ Nat.card (P : Subgroup M) := Sylow.dvd_card_of_dvd_card P h2
    rw [hP1, Subgroup.card_bot] at hdvd
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by norm_num)
  · have hcop : Nat.Coprime 2 (Nat.card M) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2
    have := le_pPrimeCore_of_normal_coprime hMn hcop
    rw [hO] at this
    exact le_bot_iff.1 this

theorem free_of_cores (hO : pPrimeCore 2 X = ⊥) (hO2 : pCore 2 X = ⊥) :
    SolvableRadical.Free X := by
  classical
  intro N hNn hNs
  have := hNn
  by_contra hne
  have hnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  have hex : ∃ n, derivedSeries N n = ⊥ := hNs.solvable
  have hk : derivedSeries N (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at hk
    exact top_ne_bot hk
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  have hjne : derivedSeries N j ≠ ⊥ := Nat.find_min hex (by omega : j < Nat.find hex)
  rw [hj, derivedSeries_succ] at hk
  have hMab : ∀ x ∈ derivedSeries N j, ∀ y ∈ derivedSeries N j, x * y = y * x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ ⁅derivedSeries N j, derivedSeries N j⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    rw [hk, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hM'n : ((derivedSeries N j).map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hM'ab : ∀ x ∈ (derivedSeries N j).map N.subtype, ∀ y ∈ (derivedSeries N j).map N.subtype,
      x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hMab a ha b hb)
  have hbot := abelian_normal_eq_bot hO hO2 _ hM'ab
  exact hjne ((Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 hbot)

end CFSG.OddStandard.ThmC.Core
