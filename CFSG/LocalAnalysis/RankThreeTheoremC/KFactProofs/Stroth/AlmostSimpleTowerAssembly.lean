module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerResidualProof
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.E8
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ExcFG
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TrialityD4
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedE6

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.AGLEmbedding CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

section Certificates


theorem exceptionalTowers : ExceptionalTowers where
  sporadic := fun s p hp hp2 =>
    outTowerAt_of_not_dvd_card_outer hp
      (CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
        CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s p hp hp2)
  lie := by
    rintro ⟨d, hv⟩ hd p hp hp2
    haveI : Fact p.Prime := ⟨hp⟩
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    cases d with
    | A m q => exact hd.elim
    | twistedA m q => exact hd.elim
    | B r q => exact hd.elim
    | C r q => exact hd.elim
    | D r q => exact hd.elim
    | twistedD r q => exact hd.elim
    | E6 q => exact outTowerAt_E6 hv hp3
    | E7 q => exact outTowerAt_E7 hv
    | E8 q =>
      obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
        (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 q hv
      exact OutTowerAt.of_mulEquiv e (outTowerAt_of_outerComm (outerComm_adjoint_E8 F))
    | F4 q =>
      obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
        (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv
      exact OutTowerAt.of_mulEquiv e (outTowerAt_of_outerComm (outerComm_adjoint_F4 F))
    | G2 q =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjoint_card
        (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv
      have h3 : 3 ≤ Nat.card F := by
        rw [hF]
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      exact OutTowerAt.of_mulEquiv e (outTowerAt_of_outerComm (outerComm_adjoint_G2 F h3))
    | twistedE6 q =>
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      let K := GaloisField q.p (2 * q.exponent)
      have hf : 1 ≤ q.exponent := q.exponent_pos
      have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
        change Nat.card (GaloisField q.p (2 * q.exponent)) = _
        rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
        change _ = (q.p ^ q.exponent) ^ 2
        rw [← pow_mul, mul_comm]
      obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
      have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eC⟩, -⟩ :=
        twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
      have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
      obtain ⟨eB⟩ : Nonempty (DerivedCentralQuotient
          (twistedFixedGroup TwistTag.E6 K σ.toRingHom) ≃*
          TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
        by_cases hq2 : q.p = 2
        · exact CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hq2 K
            (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
        · exact CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq2 K
            (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
      exact OutTowerAt.of_mulEquiv (eB.symm.trans eC)
        (outTowerAt_twistedE6RootGroup q.prime_p hf hK2 σ hσ hp3)
    | trialityD4 q =>
      obtain ⟨-, hm⟩ := CFSG.LieType.SeitzGeneration.chevalleyModel_cat_trialityD4 hv
      have hm' : TwistedChevalleyModel
          (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) .D4 (q.p ^ q.exponent) := hm
      obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
        exists_mulEquiv_graphFixedRootGroup_card .D4 q.prime_p q.exponent_pos hm'
      exact OutTowerAt.of_mulEquiv e (outTowerAt_of_outerComm
        (outerComm_graphFixedRootGroup_D4 q.prime_p q.exponent_pos K hK σ hσ))
    | suzuki m =>
      have hS := CFSG.HardMathSupport.Cooperstein.Coordinator.suzukiModel_of_lie hv
        (MulEquiv.refl _)
      exact outTowerAt_of_outerComm fun γ α =>
        CFSG.RankThree.PartTwo.KFacts.KP7.commutatorElement_mem_inner hS γ α
    | reeG2 m =>
      have hiso : CFSG.RankThree.PartOne.Census3.IsoLie
          (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group (.reeG2 m) := ⟨hv, ⟨MulEquiv.refl _⟩⟩
      obtain ⟨X, _, _, _, hm1, hXcard, ⟨e⟩⟩ :=
        CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model hiso
      have hcyc := CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.isCyclic_outer_reeG2
        hm1 hXcard
      exact outTowerAt_of_outerComm
        (OuterComm.of_mulEquiv e (outerComm_of_isCyclic_outer hcyc))
    | reeF4 m =>
      have hm := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
      have hX := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier
        (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group 2 (2 * m + 1) hm
      obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hm
      have hf3 : 3 ≤ 2 * m + 1 := hadm.2.2.2.2.2
      have ha : 1 ≤ a := by omega
      have hchar : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (by omega) hK
      have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
      obtain ⟨E⟩ := hX.2.2.2.2.2 a K hfa hK ⟨e⟩
      have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
      obtain ⟨-, -, -, hcyc, -⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
          a ha K hK'
      exact outTowerAt_of_outerComm
        (OuterComm.of_mulEquiv E (outerComm_of_isCyclic_outer hcyc))
    | tits =>
      have hR : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
        CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv (MulEquiv.refl _)
      have h2 : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :=
        (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1 hR).1
      exact outTowerAt_of_isPGroup_outer Nat.prime_two hp (Ne.symm hp2) h2

theorem almostSimplePartA_of_residual (h : AlmostSimpleTowerResidual) : AlmostSimplePartA :=
  almostSimplePartA_of_residual_of_towers exceptionalTowers h

theorem almostSimplePartA_holds : AlmostSimplePartA :=
  almostSimplePartA_of_residual almostSimpleTowerResidual_holds

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
