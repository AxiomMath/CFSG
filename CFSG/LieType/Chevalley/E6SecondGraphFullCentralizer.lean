module

public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizerTwisted

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley E6SecondGraphFull

theorem even_E6_twisted_E6_second_graph_full_centralizer_restriction
    (f : ℕ) (hf : 1 ≤ f)
    (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (∃ act : (k ≃+* k) → MulAut ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (RingHom.id k))),
      (∀ (φ : k ≃+* k) (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
        (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k))),
        (x : ModGL TwistTag.E6.tag k) = baseChangeGL (RingHom.id k) g →
          (act φ x : ModGL TwistTag.E6.tag k) =
            baseChangeGL (RingHom.id k) (Units.map (entrywiseHom φ.toRingHom) g)) ∧
      SecondGraphFullCentralizer (adjointGroup TwistTag.E6.tag k)
        ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)))
        (diagramMap TwistTag.E6 k) (pinnedX TwistTag.E6.tag k e6HighestRoot 1) act) ∧
    (∃ act : (k ≃+* k) → MulAut ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (algebraMap k K))),
      (∀ (φ : k ≃+* k) (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
        (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
          (baseChangeGL (algebraMap k K))),
        (x : ModGL TwistTag.E6.tag K) = baseChangeGL (algebraMap k K) g →
          (act φ x : ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap k K) (Units.map (entrywiseHom φ.toRingHom) g)) ∧
      SecondGraphFullCentralizer (graphFixedRootGroup TwistTag.E6 K σ)
        ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))
        (diagramMap TwistTag.E6 K) (pinnedX TwistTag.E6.tag K e6HighestRoot 1) act) :=
  ⟨⟨embeddedFieldAut _, coe_embeddedFieldAut _, secondGraphFullCentralizer_adjointGroup hf k hk⟩,
    ⟨embeddedFieldAut _, coe_embeddedFieldAut _,
      secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ⟩⟩

end CFSG.LieType.Chevalley
