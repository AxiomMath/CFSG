module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2A8Data
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternating
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.Alternating.Multipliers.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResArith

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.ComponentClassification

theorem mul_self_eq_one_multiplicative (n : ℕ) (a : Multiplicative (Fin n → ZMod 2)) :
    a * a = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  exact CharTwo.add_self_eq_zero _

theorem card_multiplicative_fin_zmod_two (n : ℕ) :
    Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem card_alternatingGroup_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_hopfMultiplier_of_alternating_eight {E : Type} [Group E]
    (e : E ≃* alternatingGroup (Fin 8)) : Nat.card (griessHopfMultiplier E) = 2 := by
  rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv,
    Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  exact CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup le_rfl

theorem eData_A8 {E : Type} [Group E] (h : Nonempty (E ≃* alternatingGroup (Fin 8))) :
    EData E := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup E := MulEquiv.isSimpleGroup e
  have hcard : Nat.card E = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_eight]
  refine eData_of_parts hcard (by norm_num) (by norm_num) (by norm_num) ?_
    (by rw [card_hopfMultiplier_of_alternating_eight e])
    (CatalogueSchreierAlternating.alternating_schreier_of_nonempty_equiv 8 (by norm_num) ⟨e⟩)
  obtain ⟨ψ4, hψ4⟩ := CResH2.exists_hom_rank_four
  obtain ⟨ψ3, hψ3, hconj⟩ := CResH2.exists_hom_translations
  obtain ⟨hab0, h20, hS0⟩ := range_elemAb_of_injective (e.symm.toMonoidHom.comp ψ4)
    (e.symm.injective.comp hψ4) (mul_self_eq_one_multiplicative 4)
  obtain ⟨hab8, h28, hS8⟩ := range_elemAb_of_injective (e.symm.toMonoidHom.comp ψ3)
    (e.symm.injective.comp hψ3) (mul_self_eq_one_multiplicative 3)
  refine ⟨4, ⟨_, hab0, h20, ?_⟩, Or.inr ⟨⟨_, hab8, h28, ?_, ?_⟩, ?_⟩⟩
  · rw [hS0, card_multiplicative_fin_zmod_two]
  · rw [hS8, card_multiplicative_fin_zmod_two]
    norm_num
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hx hy
    have hx1 : x ≠ 1 := fun h1 => hx (by rw [h1, map_one])
    have hy1 : y ≠ 1 := fun h1 => hy (by rw [h1, map_one])
    obtain ⟨g, hg⟩ := hconj x y hx1 hy1
    refine ⟨e.symm g, ?_⟩
    show e.symm g * e.symm (ψ3 x) * (e.symm g)⁻¹ = e.symm (ψ3 y)
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  · exact fun p r hp hp2 hdvd => rank_A8 p r hp hp2 (hcard ▸ hdvd)

end CFSG.EvenSporadicStandard.M24Std
