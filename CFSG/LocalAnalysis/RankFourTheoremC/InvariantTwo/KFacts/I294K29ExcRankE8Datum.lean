module

public import Certificates.Certificate425003
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE8Sound5
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankP

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC.ExcRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg


theorem typeCoverP_E8_of_datum (q : ℕ) (hq : orderOf ((q : ℕ) : ZMod 5) = 4) :
    TypeCoverP Tag.E8 5 3 q := by
  have hq4 : ((q : ℕ) : ZMod 5) ^ 4 = 1 := by
    have := pow_orderOf_eq_one ((q : ℕ) : ZMod 5)
    rwa [hq] at this
  have hq2 : ((q : ℕ) : ZMod 5) ^ 2 ≠ 1 := fun h2 => by
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hq] at this
    exact absurd this (by decide)
  have hq3 : ∀ a : ZMod 5, a ^ 4 = 1 → a ^ 2 ≠ 1 → a = 2 ∨ a = 3 := by decide
  intro x w hw
  obtain ⟨ω, hω⟩ := exists_word_of_premise x _ w hw
  obtain ⟨ω₀, Θ, hΘ, hx, hΘω⟩ :=
    Certificates.certificate425003 _ (hq3 _ hq4 hq2) x ω hω
  refine ⟨((coxeterSystem Tag.E8).wordProd ω₀)⁻¹, pPairing_of_pAct ω₀ x _ hx,
    eigSub ω₀ ((q : ℕ) : ZMod 5), mem_eigSub.2 hx, ?_,
    fun z hz v => pPairing_of_pAct ω₀ z _ (mem_eigSub.1 hz) v⟩
  let f : (Fin 3 → ZMod 5) → eigSub ω₀ ((q : ℕ) : ZMod 5) := fun c =>
    ⟨Θ c, mem_eigSub.2 (hΘω c)⟩
  have hf : Function.Injective f := fun c c' h => hΘ (congrArg Subtype.val h)
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Fin 3 → ZMod 5) = 5 ^ 3 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  rw [h2] at h1
  exact h1

end CFSG.LocalAnalysis.RankFourTheoremC.ExcRank
