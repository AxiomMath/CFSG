module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcE27
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcAdjacent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedD4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenThree
public import CFSG.LieType.SteinbergBROddLinearThreeParabolic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSep
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Bridge.Over CFSG.Quasithin
  CFSG.ClassicalInvolution.ModelFacts.ChevAut CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint

@[expose] def MinParResidual (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨
  (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q) ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
  (∃ d : TauCeti.ValidLieTypeIndex,
    ((∃ m, d.1 = .suzuki m) ∨ (∃ m, d.1 = .reeF4 m) ∨ d.1 = .tits) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))

theorem HasBQ.of_hasBorelModel {Y : Type} [Group Y] (h : ChevGen.HasBorelModel Y) : HasBQ Y := by
  obtain ⟨K, _, _, D, n, H, π, M, hπ, -⟩ := h
  exact ⟨K, inferInstance, inferInstance, D, n, H, π, M, hπ⟩

set_option linter.unusedSectionVars false

theorem hasBQ_or_residual {Y : Type} [Group Y] (h : IsChevTwo Y) : HasBQ Y ∨ MinParResidual Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hdq, ⟨e⟩⟩
  · obtain ⟨i, hv⟩ := d
    cases i with
    | A r q => exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_lieIndex ⟨_, hv⟩ hd e))
    | twistedA r q =>
      exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_lieIndex ⟨_, hv⟩ hd e))
    | B r q => exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_lieIndex ⟨_, hv⟩ hd e))
    | C r q =>
      exfalso
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      rw [TauCeti.LieTypeIndex.inStandardRange_iff] at h
      exact h.2 hd
    | D r q => exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_lieIndex ⟨_, hv⟩ hd e))
    | twistedD r q =>
      exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_lieIndex ⟨_, hv⟩ hd e))
    | G2 q => exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_lieIndex ⟨_, hv⟩ hd e))
    | E6 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup e6Data_valid K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e6 φ⟩
    | E7 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(e7Data_valid.minGroup K) := finite_minGroup e7Data_valid K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e7 φ⟩
    | E8 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(adjointGroup .E8 K) := generated_group_finite .E8 K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e8 φ⟩
    | F4 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(adjointGroup .F4 K) := generated_group_finite .F4 K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_f4 φ⟩
    | twistedE6 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, σ, hσ, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e
      have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := hK
      have : CharP K 2 := by
        have h := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          q.prime_p (show 1 ≤ q.exponent * 2 by have := q.exponent_pos; omega)
          (show Nat.card K = q.p ^ (q.exponent * 2) by rw [hK', pow_mul])
        rwa [hq] at h
      have h2le : 2 ≤ q.p ^ q.exponent := by
        rw [hq]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
      have hθ := Exceptional.involutive_of_card hK' hσ
      haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup e6Data_valid K
      haveI : Finite ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ) := Subtype.finite
      have hK4 : 4 ≤ Nat.card K := by
        rw [hK']
        calc 4 ≤ 2 ^ 2 := by norm_num
          _ ≤ (q.p ^ q.exponent) ^ 2 := Nat.pow_le_pow_left h2le 2
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e6tw hθ hK4 hK' hσ φ⟩
    | trialityD4 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, σ, hσ, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e
      have hK' : Nat.card K = (q.p ^ q.exponent) ^ 3 := hK
      have : CharP K 2 := by
        have h := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          q.prime_p (show 1 ≤ q.exponent * 3 by have := q.exponent_pos; omega)
          (show Nat.card K = q.p ^ (q.exponent * 3) by rw [hK', pow_mul])
        rwa [hq] at h
      have h2le : 2 ≤ q.p ^ q.exponent := by
        rw [hq]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
      haveI : Finite ↥(adjointGroup d4 K) := generated_group_finite d4 K
      haveI : Finite ↥(twistedGroup σ) := Subtype.finite
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_d4tw h2le hK' hσ φ⟩
    | suzuki m => exact Or.inr (Or.inr (Or.inr ⟨⟨_, hv⟩, Or.inl ⟨m, rfl⟩, ⟨e⟩⟩))
    | reeG2 m => exact absurd hd (by simp [IsChevIndexTwo])
    | reeF4 m => exact Or.inr (Or.inr (Or.inr ⟨⟨_, hv⟩, Or.inr (Or.inl ⟨m, rfl⟩), ⟨e⟩⟩))
    | tits => exact Or.inr (Or.inr (Or.inr ⟨⟨_, hv⟩, Or.inr (Or.inr rfl), ⟨e⟩⟩))
  · rcases hn with rfl | rfl | rfl
    · exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_alt_five e))
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_alt_eight e))
  · rcases hdq with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      exact Or.inl (HasBQ.of_hasBorelModel (ChevGen.hasBorelModel_model_seven h))
    · exact Or.inr (Or.inr (Or.inl ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩))

@[expose] def MinParResidualCase : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R P : Subgroup Y), Open.IsQuasisimple ↥L →
    MinParResidual (↥L ⧸ Subgroup.center ↥L) → R ≤ Subgroup.normalizer (L : Set Y) →
    IsPGroup 2 R → IsSylowTwoOf (R ⊓ L) L → IsMinOverBorel L (R ⊓ L) P →
      (∃ M : Subgroup Y, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M) ∧
      (conjClosure P R ≠ L →
        ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
          twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥)

theorem kFactChevMinParabolic_of_residual (hres : MinParResidualCase) :
    CFSG.AGLEmbeddingD2.GN.KFactChevMinParabolic := by
  intro Y _ _ L R P hL hchev hR hR2 hS hP
  rcases hasBQ_or_residual hchev with h | h
  · exact kFact_of_hasBQ hL hR hR2 hS hP h
  · exact hres Y L R P hL h hR hR2 hS hP

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
