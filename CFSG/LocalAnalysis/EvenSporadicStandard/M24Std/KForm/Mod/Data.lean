module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Foundations.Basic
public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

structure Z2S6ModData (S : Type) [Group S] (σ : MulAut S)
    (J : Subgroup ↥(fixedSubgroup σ)) : Prop where
  order_two : orderOf σ = 2
  normal : J.Normal
  isPComponent : IsPComponent 2 J
  iso : Nonempty (↥J ⧸ fusionOddCore ↥J ≃* alternatingGroup (Fin 6))
  perfect_le : ∀ P : Subgroup ↥(fixedSubgroup σ), ⁅P, P⁆ = P → P ≤ J
  odd_quotient : ∃ N : Subgroup ↥(fixedSubgroup σ), N.Normal ∧ Odd (Nat.card N) ∧
    Nat.card (↥(fixedSubgroup σ) ⧸ N) ∣ 1440
  dvd_card : 360 ∣ Nat.card ↥(fixedSubgroup σ)
  not_two_pow_six : ¬ 2 ^ 6 ∣ Nat.card ↥(fixedSubgroup σ)
  no_eight : ∀ x : ↥(fixedSubgroup σ), orderOf x ≠ 8
  cent_two : ∀ U : Subgroup ↥(fixedSubgroup σ), IsPGroup 2 U →
    U ≤ centralizer (J : Set ↥(fixedSubgroup σ)) → Nat.card U ≤ 2
  pCore_le_center : CFSG.pCore 2 ↥(fixedSubgroup σ) ≤ center ↥(fixedSubgroup σ)

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
