module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Untw

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint

section Main


theorem e6RankLowerTw : E6RankLowerTw := by
  intro L _ _ n r f hm h3
  obtain ⟨hr, hf, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := twistedChevalleyModel_of_lieModel hm
  have hK' : Nat.card K = (r ^ f) ^ 2 := hK
  have : Fact r.Prime := ⟨hr⟩
  have := Fintype.ofFinite K
  have : CharP K r := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hK', ← pow_mul, mul_comm])
  have hc := center_twDerived_eq_bot σ hr hf hK' hσ
  let E := e.trans (derivedCentralQuotientEquiv σ hc)
  have : Finite ↥(twDerived σ) := Finite.of_equiv _ E.toEquiv
  refine ⟨fun hZ => ?_, fun h9 => ?_⟩
  · let π : L →* ↥(twDerived σ) := E.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hπ : Function.Surjective π := E.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center L := fun x => by
      change E (QuotientGroup.mk x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact six_le_pRank_of_cover_twE6 σ hf h3 hK' hσ π hπ hker hZ
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) E]
    exact six_le_pRank_twE6 σ hf h9 hK' hσ

end Main

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
