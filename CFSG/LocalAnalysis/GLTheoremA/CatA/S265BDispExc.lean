module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankCarrier
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular
public import CFSG.RankThree.PartTwo.Census.Exceptional.E6E7
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open CFSG.RankThree.CentralCover (sl2Upper centralizer_le_normalizer_zpowers)
open CFSG.RankThree.PartTwo.Census.Exceptional (orderOf_sl2Upper_one)
open scoped MatrixGroups

private theorem liftDatum_of_six {S : Type*} [Group S] {F : Type*} [Field F]
    (hF : ringChar F = 2) (φ : Fin 6 → SL(2, F) →* S) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A) :
    ExcRank.LiftDatum S 4 := by
  have hu : orderOf (φ 5 (sl2Upper 1)) = 2 := by
    rw [orderOf_injective (φ 5) (hφ 5)]
    exact orderOf_sl2Upper_one hF
  have hu1 : φ 5 (sl2Upper 1) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  refine ExcRank.liftDatum_of_commuting_SL2_normalizing hF (m := 4) (fun i => φ i.castSucc)
    (fun i => hφ _) (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 5 h)) A B)
    (U := Subgroup.zpowers (φ 5 (sl2Upper 1))) (fun h => hu1 (Subgroup.zpowers_eq_bot.1 h))
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])) fun i A => ?_
  exact centralizer_le_normalizer_zpowers _ (Subgroup.mem_centralizer_singleton_iff.2
    (hcomm _ _ (Fin.castSucc_ne_last i) A _))

private theorem wit_of_liftDatum {G : Type} [Group G] [Finite G] (hL : ExcRank.LiftDatum G 4) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E := by
  obtain ⟨h, w, U, hcomm, hord, hinv, hfix, hU1, hU2, hN⟩ := hL
  refine ⟨Subgroup.closure (Set.range h), IsElemAbelian.closure_of_commute ?_ ?_,
    ExcRank.three_pow_le_card_closure h w hcomm hord hinv hfix, U, hU2, hU1,
    (Subgroup.closure_le _).2 ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  · rintro _ ⟨i, rfl⟩
    exact hord i ▸ pow_orderOf_eq_one (h i)
  · rintro _ ⟨i, rfl⟩
    exact hN i


open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Minuscule
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.TauCetiBridge TauCeti in
theorem exists_twoLocal_five_exc :
    (∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
      [Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group], q.card = 2 →
      ∃ E : Subgroup (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group,
        IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E) ∧
    ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
      [Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group], q.card = 2 →
      ∃ E : Subgroup (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group,
        IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E := by
  refine ⟨fun q hv _ hq => ?_, fun q hv _ hq => ?_⟩
  · let d : TypeE7LieIndex := ⟨⟨.E7 q, hv⟩, (LieTypeIndex.isTypeE7_iff _).2 trivial⟩
    have hq' : d.1.fieldOrder = 2 := by
      change (LieTypeIndex.E7 q).fieldOrder = 2
      rw [LieTypeIndex.fieldOrder_E7]
      exact hq
    have hC : commutator ↥(e7Data_valid.minGroup d.1.fixedField) = ⊤ :=
      (CFSG.LieType.CurtisTits.isQuasisimple_e7 d.1.fixedField).1.commutator_eq_top
    obtain ⟨ρ, -, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e7Data_valid d.1.fixedField
      neighbour_cartan_E7 ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1], ![2, 2, 3, 4, 3, 2, 1],
        ![0, 1, 1, 2, 1, 0, 0]] (by decide +kernel)
    have hL := liftDatum_of_six (ringChar_fixedField_eq_two hq')
      (fun i => (toQuot (e7Embed d) hC).comp (ρ i))
      (fun i => toQuot_comp_injective (e7Embed_injective d) hC (ρ i) (hcen i))
      fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]
    exact wit_of_liftDatum (G := (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group) hL
  · let d : ValidLieTypeIndex := ⟨.E8 q, hv⟩
    haveI := ExcRank.finite_fixedField d
    have hq' : d.fieldOrder = 2 := by
      change (LieTypeIndex.E8 q).fieldOrder = 2
      rw [LieTypeIndex.fieldOrder_E8]
      exact hq
    have hC : commutator ↥(adjointGroup .E8 d.fixedField) = ⊤ :=
      single_edge_perfect .E8 d.fixedField (by simp)
    obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .E8
      ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0], ![2, 3, 4, 6, 5, 4, 3, 2], ![0, 1, 1, 2, 1, 0, 0, 0]]
      (by decide +kernel)
    have hinj := toQuot_injective (geckEmbed_injective d geckMatchE8) hC center_adjointGroup_eq_bot
    have hL := liftDatum_of_six (ringChar_fixedField_eq_two hq')
      (fun i => (toQuot (geckEmbed d geckMatchE8) hC).comp (ι i)) (fun i => hinj.comp (hι i))
      fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]
    exact wit_of_liftDatum (G := (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) hL

end CFSG.LocalAnalysis.GLTheoremA.S265

end
