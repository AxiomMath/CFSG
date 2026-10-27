module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcParabolicTw
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti


theorem exists_catEquiv_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ (K : Type) (_ : Field K) (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
      (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
      Nonempty (Cat ⟨.twistedE6 q, hv⟩ ≃* twistedE6RootGroup K σ) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * TwistTag.E6.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos TwistTag.E6.order_pos).ne', pow_mul],
      inferInstance⟩
  obtain ⟨σ, hσ, hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 q.prime_p q.exponent_pos K hK
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos K hK
    σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  exact ⟨K, inferInstance, σ, hK, hσ, ⟨φ.symm.trans ψ⟩⟩

theorem rankLE1_cat_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p)
    (hcnt : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1) :
    RankLE1 p (Cat ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  rw [TauCeti.PrimePower.card_def] at hcnt
  exact RankLE1.of_mulEquiv e.symm
    (rankLE1_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp hpK hcnt)

theorem not_rankLE2_cat_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE2 p (Cat ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  rw [TauCeti.PrimePower.card_def] at hcnt
  exact fun h => not_rankLE2_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp hp3 hpK hcnt
    (RankLE2.of_mulEquiv e h)

end CFSG.LieType.SeitzGeneration
