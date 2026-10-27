module

public import CFSG.LieType.SeitzGeneration.ExcParabolicTw
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
  CFSG.LieType.SeitzGeneration


theorem catEquiv_twistedE6_of_field (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.card ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ q.card) :
    Nonempty (Cat ⟨.twistedE6 q, hv⟩ ≃* twistedE6RootGroup K σ) := by
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    rw [hK, PrimePower.card_def]
    rfl
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, PrimePower.card_def]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K hK σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos K hK'
    σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  exact ⟨φ.symm.trans ψ⟩

theorem catEquiv_trialityD4_of_field (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.card ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ q.card) :
    Nonempty (Cat ⟨.trialityD4 q, hv⟩ ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    rw [hK, PrimePower.card_def]
    rfl
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, PrimePower.card_def]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.trialityD4 q hv K hK σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.D4 q.prime_p q.exponent_pos K hK'
    σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  exact ⟨φ.symm.trans ψ⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
