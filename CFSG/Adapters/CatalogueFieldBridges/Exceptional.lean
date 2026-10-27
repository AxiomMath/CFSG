module

public import CFSG.LieType.SeitzGeneration.ExcParabolicTw

public section

namespace CFSG.Adapters.CatalogueFieldBridges

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.TauCetiBridge

theorem nonempty_adjointGroup_catEquiv
    {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) {q : TauCeti.PrimePower}
    (hv : (c q).Valid)
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = q.card) :
    Nonempty (↥(adjointGroup τ k) ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) := by
  obtain ⟨e⟩ := hB q hv k hk
  have hZ : Subgroup.center ↥(adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem nonempty_centerQuotient_catEquiv
    {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) {q : TauCeti.PrimePower}
    (hv : (c q).Valid)
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = q.card)
    {C : Type} [Group C] {J : Subgroup C} (eJ : ↥J ≃* ↥(adjointGroup τ k)) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) := by
  have hZk : Subgroup.center ↥(adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  have hZ : Subgroup.center ↥J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : eJ x ∈ Subgroup.center ↥(adjointGroup τ k) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := eJ.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
    rw [hZk, Subgroup.mem_bot] at hmem
    exact eJ.injective (by rw [hmem, map_one])
  obtain ⟨e⟩ := nonempty_adjointGroup_catEquiv hB hv hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot.trans (eJ.trans e))⟩

theorem nonempty_catEquiv_graphFixedRootGroup_trialityD4
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = q.card ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ q.card) :
    Nonempty ((TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩).Group ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ q.card := fun c => hσ c
  have hσ'' : ∀ c, σ.toRingHom c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [hσ' c, TauCeti.PrimePower.card_def]
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    rw [hK, TauCeti.PrimePower.card_def, show TwistTag.D4.order = 3 by decide]
  obtain ⟨φ⟩ : Nonempty (CFSG.Blueprint.DerivedCentralQuotient
      (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩).Group) := by
    by_cases h2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv h2 K hK σ.toRingHom hσ'
    · exact CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv h2 K hK σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.D4 q.prime_p q.exponent_pos K hK'
    σ.toRingHom hσ''
  have hZ := CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) (K := K)
    (σ := (σ : K →+* K)) (σ : K →+* K).surjective
  obtain ⟨ψ⟩ := CFSG.LieType.SeitzGeneration.nonempty_derivedCentralQuotient_equiv
    (twistedFixedGroup TwistTag.D4 K σ.toRingHom) (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    hperf.2.2.1 hZ
  exact ⟨φ.symm.trans ψ⟩

end CFSG.Adapters.CatalogueFieldBridges

end
