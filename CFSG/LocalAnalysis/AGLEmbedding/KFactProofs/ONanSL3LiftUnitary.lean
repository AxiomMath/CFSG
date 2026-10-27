module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryCover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftMain
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def IsUnitaryInnerIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1 ∧ ¬ 3 ∣ q.exponent

@[expose] def IsUnitaryFieldIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1 ∧ 3 ∣ q.exponent

theorem kFactSL3LiftGenUnitaryInner :
    KFactSL3LiftGenFor IsUnitaryInnerIndex := by
  intro X _ _ R K _ z d _ hin hK ⟨e⟩ hzc hzK hz3 hΩ hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hqd, h3, h3e⟩ := hin
  simp only at hqd
  subst hqd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq3 : 3 ≤ q.card := hrange.2 rfl
  rw [TauCeti.PrimePower.card_def] at hq3 h3
  have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨-, F, _, _, hFcard, ⟨e'⟩⟩ := hm
  have hU : UnitaryFieldData q.p q.exponent F :=
    ⟨q.prime_p, q.exponent_pos, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hFcard' : Nat.card F = q.p ^ (2 * q.exponent) := hU.card
  have hσ : ∀ σ : F ≃+* F, σ ^ 3 = 1 → σ = 1 :=
    SL3Lift.no_ringAut_order_three hFcard' (by omega)
  have hcenne : Subgroup.center K ≠ ⊥ := by
    intro hbot
    have hmem : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 hzc g)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : z = 1 := congrArg Subtype.val hmem
    rw [this, orderOf_one] at hz3
    omega
  obtain ⟨ψ⟩ := exists_mulEquiv_unitarySU_three hU (by omega) hK.1
    (e'.trans (unitaryPSUEquiv hU (by norm_num)).symm) hcenne
  obtain ⟨A, hAR, hAe, hAcard, hAgen⟩ :=
    exists_generating_elemAbelian_unitary R K z hU h3 (by omega) hσ ψ hzc hz3 hΩ hrank
  exact ⟨A, hAR, hAe, SL3Lift.three_le_pRank_of_card hAe hAcard, hAgen⟩

theorem kFactSL3LiftGenUnitary_of_cases (hi : KFactSL3LiftGenFor IsUnitaryInnerIndex)
    (hf : KFactSL3LiftGenFor IsUnitaryFieldIndex) : KFactSL3LiftGenUnitary := by
  intro X _ _ R K _ z d hd hu hK he hzc hzK hz3 hΩ hrank
  obtain ⟨q, hqd, h3⟩ := hu
  by_cases h3e : 3 ∣ q.exponent
  · exact hf X R K z d hd ⟨q, hqd, h3, h3e⟩ hK he hzc hzK hz3 hΩ hrank
  · exact hi X R K z d hd ⟨q, hqd, h3, h3e⟩ hK he hzc hzK hz3 hΩ hrank

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
