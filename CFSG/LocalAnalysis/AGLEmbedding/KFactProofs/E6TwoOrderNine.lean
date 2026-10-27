module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.E6WeylOrderNine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarResidualDefs
import CFSG.Adapters.TauCetiExceptional.EvenB1

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem exists_orderOf_nine_adjointQuotient (K : Type) [Field K] [CharP K 2] :
    ∃ g : AdjointQuotient Tag.E6 K, orderOf g = 9 := by
  obtain ⟨g, h9, h3⟩ := E6Nine.exists_pow_nine_not_central (K := K)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨QuotientGroup.mk g, ?_⟩
  have h3' : ¬ (QuotientGroup.mk g : AdjointQuotient Tag.E6 K) ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h3
  have h9' : (QuotientGroup.mk g : AdjointQuotient Tag.E6 K) ^ 3 ^ (1 + 1) = 1 := by
    rw [show 3 ^ (1 + 1) = 9 by norm_num, ← QuotientGroup.mk_pow, h9]
    exact QuotientGroup.mk_one _
  simpa using orderOf_eq_prime_pow h3' h9'

theorem e6TwoHasOrderNine
    : E6TwoHasOrderNine := by
  intro L _ _ d q hq hq1 hdq ⟨e⟩
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.E6 q := hdq
  have hm : ChevalleyExceptionalModel (CatGroup ⟨TauCeti.LieTypeIndex.E6 q, hv⟩)
      .E6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq (MulEquiv.refl _)⟩
  obtain ⟨K, hF, hFin, hK, ⟨eK⟩⟩ := hm.2
  rw [hq, hq1] at hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK
  obtain ⟨g, hg⟩ := exists_orderOf_nine_adjointQuotient K
  exact ⟨(e.trans eK).symm g, by rw [MulEquiv.orderOf_eq, hg]⟩

end CFSG.AGLEmbedding
