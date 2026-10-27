module

public import CFSG.LieType.SeitzGeneration.HyperExParabolic
public import CFSG.LieType.SeitzGeneration.ExcParabolicTw
public import CFSG.LieType.Chevalley.FixedRootHyperplaneGeneration

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge

section Generic


theorem seitzExcParabolicHyperFor_twisted (t : TwistTag)
    (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (hchar : ∀ q, (c q).characteristic = q.p)
    (hB : Even.TwistedBridgeAll t c)
    (hS : ∀ q : TauCeti.PrimePower, (c q).Valid → ∀ (G : Type) [Group G],
      TwistedChevalleyModel G t (q.p ^ q.exponent) → IsSimpleGroup G) :
    SeitzExcParabolicHyperFor fun d => ∃ q, d = c q := by
  rintro ⟨d, hv⟩ p hp hpd ⟨q, rfl⟩ E hE hE1 ⟨R, hR1, hRp, hRn⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrp : q.p ≠ p := fun h => hpd (by simp [hchar, h])
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ t.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * t.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos t.order_pos).ne', pow_mul],
      inferInstance⟩
  obtain ⟨σ, hσ, hord, -⟩ := finite_graph_field_parameter_fields t q.prime_p q.exponent_pos K hK
  have hσo : σ ^ t.order = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := hB q hv K (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect t q.prime_p q.exponent_pos K hK σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  let e : Cat ⟨c q, hv⟩ ≃* ↥(graphFixedRootGroup t K σ.toRingHom) := φ.symm.trans ψ
  have hsimple : IsSimpleGroup (Cat ⟨c q, hv⟩) :=
    hS q hv _ ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ'', ⟨φ.symm⟩⟩
  have : IsSimpleGroup ↥(graphFixedRootGroup t K σ.toRingHom) := MulEquiv.isSimpleGroup e.symm
  have hgen : RootInvariantHyperGeneration (graphFixedRootGroup t K σ.toRingHom) q.p p := by
    intro A R hAC hA hA1 hRC hRr hR hAR
    have := hA
    exact fixed_root_invariant_prime_subgroup_hyperplane_generation t K q.p p hrp σ hσo A hAC
      hA1 R hRC hRr hR hAR
  exact hyperGen_of_native e hgen hE hE1 ⟨R, hR1, by simpa [hchar] using hRp, hRn⟩

end Generic

section All


theorem seitzExcParabolicHyperTw : SeitzExcParabolicHyperFor IsTwistedExcIndex :=
  SeitzExcParabolicHyperFor.union
    (seitzExcParabolicHyperFor_twisted .D4 TauCeti.LieTypeIndex.trialityD4
      (fun _ => TauCeti.LieTypeIndex.characteristic_trialityD4 _)
      Even.chevalleyBridgesAll.trialityD4
      fun q _ G _ h => (CFSG.LieType.Simplicity.fam_3d4_simplicity G q.p q.exponent
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, h⟩).2)
    (seitzExcParabolicHyperFor_twisted .E6 TauCeti.LieTypeIndex.twistedE6
      (fun _ => TauCeti.LieTypeIndex.characteristic_twistedE6 _)
      Even.chevalleyBridgesAll.twistedE6
      fun q _ G _ h => (CFSG.LieType.Simplicity.fam_2e6_simplicity G q.p q.exponent
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, h⟩).2)

end All

end CFSG.LieType.SeitzGeneration
