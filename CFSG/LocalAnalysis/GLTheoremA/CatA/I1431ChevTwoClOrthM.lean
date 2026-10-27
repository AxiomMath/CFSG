module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.ComponentClassification.OuterAutomorphisms

theorem orthm_not_three_pow_five_dvd_orderTwistedD_four_two :
    ¬ 3 ^ 5 ∣ CFSG.Open.orderTwistedD 4 2 := by
  have h : CFSG.Open.orderTwistedD 4 2 = 197406720 := by decide +kernel
  rw [h]
  norm_num

theorem orthm_mem_inner_of_congr {S G : Type} [Group S] [Group G] (φ : S ≃* G) {α : MulAut S}
    (h : MulAut.congr φ α ∈ inner G) : α ∈ inner S := by
  rw [← inner_map_congr φ] at h
  exact (Subgroup.mem_map_iff_mem (MulAut.congr φ).injective).1 h

theorem orthm_mem_inner_of_twistedD_four {S : Type} [Group S] [Finite S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD 4 q).Valid) (hp : q.p = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group) {α : MulAut S}
    (hα : α ∈ innAutDerived S) (h3 : α ^ 3 = 1) : α ∈ inner S := by
  have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hp e
  have hG' := hG
  obtain ⟨-, K, hfield, hfinite, hK, b, c, hirr, ⟨e₀⟩⟩ := hG'
  letI := hfield
  letI := hfinite
  have hn1 : 1 ≤ 4 := by norm_num
  obtain ⟨-, -, -, hinner⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.matrixModel_facts_pomegaMinus hG hK hn1 b c hirr e₀
  have h1 := (mem_innAutDerived_congr
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv K hn1
      b c e₀)).2 hα
  exact orthm_mem_inner_of_congr _ (hinner 3 Nat.prime_three (by norm_num) _ h1
    (by rw [← map_pow, h3, map_one]))

theorem false_of_twistedD_four (hLO : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hn : ∃ a b : S, a * b ≠ b * a)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedD 4 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group)
    {α : MulAut S} (hα : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S)
    (hP : U42Pumpup S α) : False := by
  have hcard : Nat.card S = CFSG.Open.orderTwistedD 4 q.card := hLO ⟨.twistedD 4 q, hv⟩ S ⟨e⟩
  have h5 : ¬ 3 ^ 5 ∣ Nat.card S := by
    rw [hcard, hq]
    exact orthm_not_three_pow_five_dvd_orderTwistedD_four_two
  exact false_of_pumpup_of_inner (cl_center_eq_bot_of_simple hn) hP
    (orthm_mem_inner_of_twistedD_four hv (cl_primePower_card_two hq).1 e hα hP.1) h5

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
