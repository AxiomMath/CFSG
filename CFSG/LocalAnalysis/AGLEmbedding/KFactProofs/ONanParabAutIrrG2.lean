module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OutStructure CFSG.AGLEmbedding.ParabHub

@[expose] def G2R2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    AutScalarTorus (adjointGroup .G2 K)

section G2


theorem exists_g2_field {Y : Type} [Group Y] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq : q.p = 2)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.G2 q, hv⟩).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f : ℕ),
      2 ≤ f ∧ Nat.card K = 2 ^ f ∧ Nonempty (Y ≃* adjointGroup .G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 q.exponent
  have hK : Nat.card K = q.card := by
    rw [GaloisField.card 2 q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def, hq]
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hf2 : 2 ≤ q.exponent := by
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [TauCeti.PrimePower.card_def, hq, h1] at hq3
    omega
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq K hK
  refine ⟨K, inferInstance, inferInstance, inferInstance, q.exponent, hf2, ?_,
    ⟨(e.trans b.symm).trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))).trans
      QuotientGroup.quotientBot)⟩⟩
  rw [hK, TauCeti.PrimePower.card_def, hq]

noncomputable def adjointQuotientEquiv (K : Type) [Field K] [Finite K] :
    AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))).trans
    QuotientGroup.quotientBot

theorem parabStruct_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* AdjointQuotient .G2 K) (hq4 : 4 ≤ Nat.card K) : ParabStruct Y := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  exact (borelQuotient_g2 e).parabStruct hq4 CFSG.AGLEmbedding.ParabPrime.rankOneNode_g2

theorem outPTwoGen_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y]
    (e : Y ≃* adjointGroup .G2 K) {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) : OutPTwoGen Y p := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  have hcard := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact OutPTwoGen.of_outPNice (OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker))

theorem yLevelIrrOn_g2 (hR2 : G2R2) : YLevelIrrOn IsG2Two := by
  intro Y _ _ ⟨q, hv, hq, ⟨e⟩⟩ hinj p r hp hp2 hr hr2 hr3 hrp S₀ J hJ hcyc U Z y hU hZ hirr hrel
    hpow hyU hUJ hyJ hyr
  obtain ⟨K, _, _, _, f, hf, hK, ⟨e'⟩⟩ := exists_g2_field q hv hq e
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have e'' : Y ≃* AdjointQuotient .G2 K := e'.trans (adjointQuotientEquiv K).symm
  exact false_of_large hinj (parabStruct_g2 e'' hq4) hp hp2 hr hr2 hr3 (outPTwoGen_g2 e' hf hK hp)
    (AutScalarTorus.of_mulEquiv e'.symm (hR2 K hq4)) S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ
    hyr

end G2

end CFSG.AGLEmbedding.ParabAutIrr
