module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2L52Data
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearModelSchreier
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResArith

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem card_of_statedClassicalModel_psl_five_two {E : Type} [Group E]
    (hc : StatedClassicalModel E .PSL 5 2 1) : Nat.card E = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hc

theorem eData_L52
    {E : Type} [Group E]
    (h : LieModel E .PSL 5 2 1) : EData E := by
  have hc : StatedClassicalModel E .PSL 5 2 1 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hcard := card_of_statedClassicalModel_psl_five_two hc
  have : IsSimpleGroup E := (CFSG.LieType.Simplicity.fam_PSL_simplicity E 5 2 1 hc).2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  refine eData_of_parts hcard (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_classical_model_schreier
      (by norm_num) hc).2
  · obtain ⟨ψ, hψ⟩ := CResH2.exists_hom_psl (K := K)
    have h2 : ∀ a : Multiplicative (Matrix (Fin 2) (Fin 3) K), a * a = 1 := fun a => by
      apply Multiplicative.toAdd.injective
      ext i j
      exact CharTwo.add_self_eq_zero _
    obtain ⟨hab, h2', hS⟩ := range_elemAb_of_injective (e.symm.toMonoidHom.comp ψ)
      (e.symm.injective.comp hψ) h2
    refine ⟨6, ⟨_, hab, h2', ?_⟩, Or.inl fun p r hp hp2 hdvd => rank_L52 p r hp hp2 (hcard ▸ hdvd)⟩
    rw [hS, Nat.card_congr Multiplicative.toAdd]
    show Nat.card (Fin 2 → Fin 3 → K) = 2 ^ 6
    rw [Nat.card_fun, Nat.card_fun, hK]
    simp
  · obtain ⟨-, ⟨f⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hc
    rw [Nat.card_congr f.toEquiv, card_generic_prod_exceptional]
    simp [genericOrders, exceptionalOrders]

end CFSG.EvenSporadicStandard.M24Std
