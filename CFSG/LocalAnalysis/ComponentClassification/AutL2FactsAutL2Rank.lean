module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsRank

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem sq_eq_one_map_autEquiv {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (e : Y ≃* PSL2 F) (E : Subgroup (MulAut Y)) (hE : ∀ x ∈ E, x * x = 1) :
    ∀ x ∈ E.map (autEquiv e).toMonoidHom, x * x = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  change autEquiv e x * autEquiv e x = 1
  rw [← map_mul, hE x hx, map_one]

theorem cfAutL2Rank : GSThmB.CFAutL2Rank := by
  intro Y _ _ hY E hE
  have key : ∀ p : ℕ, p.Prime → p ≠ 2 → Blueprint.LieModel Y .PSL 2 p 1 → Nat.card E ≤ 4 := by
    intro p hp hp2 hL
    obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
    rw [← Subgroup.card_map_of_injective (f := (autEquiv e).toMonoidHom)
      (autEquiv e).injective]
    exact pGammaL2_card_le_four_of_sq_of_prime hp hp2 (by rw [hF, pow_one]) _
      (sq_eq_one_map_autEquiv e E fun x hx => by rw [← pow_two]; exact hE x hx)
  rcases hY with h | h
  · exact key 5 (by norm_num) (by norm_num) h
  · exact key 7 (by norm_num) (by norm_num) h

end CFSG.ComponentClassification.AutL2Facts
