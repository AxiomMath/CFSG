module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SL2Pair
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.RankThree.PartTwo.Census CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
open scoped MatrixGroups

theorem exists_commuting_injective_sl2_twistedE6
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ (F : Type) (_ : Field F) (φ ψ : SL(2, F) →* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩),
      Function.Injective φ ∧ Function.Injective ψ ∧ ∀ A B, Commute (φ A) (ψ B) := by
  let d : TypeTwistedE6LieIndex :=
    ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩
  have hfin : Finite d.1.fixedField := Nat.finite_of_card_ne_zero (by
    rw [ValidLieTypeIndex.card_fixedField]
    have h : (d.1 : ValidLieTypeIndex).fieldOrder = q.card := LieTypeIndex.fieldOrder_twistedE6 q
    rw [h, TauCeti.PrimePower.card_def]
    exact (pow_pos q.prime_p.pos _).ne')
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i : Fin 4, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  refine ⟨d.1.fixedField, inferInstance,
    (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj 0),
    (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj 1), hinj 0, hinj 1,
    fun A B => ?_⟩
  have h01 : Commute (te6SL2 (quadFrob d) (quadIncl d) hj 0 A)
      (te6SL2 (quadFrob d) (quadIncl d) hj 1 B) :=
    te6SL2_commute (quadFrob d) (quadIncl d) hj (i := 0) (i' := 1) (by decide) A B
  exact h01.map (toQuot (te6Embed d) hC)

theorem two_le_pRank_three_twistedE6
    {X : Type} [Group X] [Finite X] {q : PrimePower}
    {hv : (LieTypeIndex.twistedE6 q).Valid}
    (e : X ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨F, _, φ, ψ, hφ, hψ, hc⟩ := exists_commuting_injective_sl2_twistedE6 q hv
  refine Orth.two_le_pRank_three_of_commuting_sl2 (e.symm.toMonoidHom.comp φ)
    (e.symm.toMonoidHom.comp ψ) (e.symm.injective.comp hφ) (e.symm.injective.comp hψ)
    fun A B => ?_
  change e.symm (φ A) * e.symm (ψ B) = e.symm (ψ B) * e.symm (φ A)
  rw [← map_mul, ← map_mul, (hc A B).eq]

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
