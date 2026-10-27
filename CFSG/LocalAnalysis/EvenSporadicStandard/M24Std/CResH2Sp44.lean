module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Sp44Data
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoSchreier
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResArith

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem card_of_statedClassicalModel_psp_two_two {E : Type} [Group E]
    (hc : StatedClassicalModel E .PSp 2 2 2) : Nat.card E = 979200 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl]
  norm_num [CFSG.Open.ordBC, Finset.prod_Icc_succ_top]

theorem eData_Sp44
    {E : Type} [Group E] (h : LieModel E .PSp 2 2 2) : EData E := by
  have hc : StatedClassicalModel E .PSp 2 2 2 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hcard := card_of_statedClassicalModel_psp_two_two hc
  have : IsSimpleGroup E :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp E 2 2 2 hc
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hK
  refine eData_of_parts hcard (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    (CFSG.ComponentClassification.CatalogueBSymplecticTwo.classical_model_two_schreier hc).2
  · obtain ⟨ψ, hψ⟩ := CResH2.exists_hom_psp (K := K)
    have h2 : ∀ a : Multiplicative (K × K × K), a * a = 1 := fun a => by
      apply Multiplicative.toAdd.injective
      exact Prod.ext (CharTwo.add_self_eq_zero _) (Prod.ext (CharTwo.add_self_eq_zero _)
        (CharTwo.add_self_eq_zero _))
    obtain ⟨hab, h2', hS⟩ := range_elemAb_of_injective (e.symm.toMonoidHom.comp ψ)
      (e.symm.injective.comp hψ) h2
    refine ⟨6, ⟨_, hab, h2', ?_⟩, Or.inl fun p r hp hp2 hdvd => rank_Sp44 p r hp hp2 (hcard ▸ hdvd)⟩
    rw [hS, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, hK]
    norm_num
  · obtain ⟨-, ⟨f⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hc
      (Or.inr (Or.inl (by norm_num)))
    rw [Nat.card_congr f.toEquiv, card_generic_prod_exceptional]
    simp [genericOrders, exceptionalOrders]

end CFSG.EvenSporadicStandard.M24Std
