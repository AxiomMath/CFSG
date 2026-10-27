module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTwisted
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SL2Pair

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem two_le_pRank_three_trialityD4
    {X : Type} [Group X] [Finite X] {q : PrimePower}
    {hv : (LieTypeIndex.trialityD4 q).Valid}
    (e : X ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * TwistTag.D4.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos TwistTag.D4.order_pos).ne', pow_mul],
      inferInstance⟩
  obtain ⟨σ, hσ'', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 q.prime_p q.exponent_pos K hK
  have hσo : σ ^ 3 = 1 := by
    rw [show 3 = TwistTag.D4.order from rfl, ← hord]
    exact pow_orderOf_eq_one σ
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.D4 q.prime_p q.exponent_pos K hK
    σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv' _ _ hperf.2.2.1 hZ
  let e' : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* X :=
    (ψ.symm.trans φ).trans e.symm
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσo
  refine Orth.two_le_pRank_three_of_commuting_sl2 (e'.toMonoidHom.comp ι)
    (e'.toMonoidHom.comp η) (e'.injective.comp hι) (e'.injective.comp hη) fun A B => ?_
  change e' (ι A) * e' (η B) = e' (η B) * e' (ι A)
  rw [← map_mul, ← map_mul, hcomm]

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
