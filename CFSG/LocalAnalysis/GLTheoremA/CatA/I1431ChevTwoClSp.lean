module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner innAutDerived)

theorem sp_orderBC_three_two : orderBC 3 2 = 1451520 := by
  decide +kernel

theorem sp_mem_inner_of_statedModel {S : Type} [Group S] {r ℓ f : ℕ}
    (hG : StatedClassicalModel S .PSp r ℓ f) {α : MulAut S} (hα : α ∈ innAutDerived S)
    (hα3 : α ^ 3 = 1) : α ∈ inner S := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨φ⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hne : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => hadm.2.2.2 (by rw [h.1, h.2])
  have hβ : MulAut.congr φ α ∈ innAutDerived (StatedProj (StatedSp r K)) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr φ).2 hα
  have hβ3 : MulAut.congr φ α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  obtain ⟨y, hy⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.mem_inner_of_mem_innAutDerived_statedSp
      Nat.prime_three (by norm_num) hadm.1 hadm.2.1 hK hadm.2.2.1 hne hβ hβ3
  refine ⟨φ.symm y, (MulAut.congr φ).injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]

theorem false_of_B_three (hLO : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hn : ∃ a b : S, a * b ≠ b * a)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B 3 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group)
    {α : MulAut S} (hα : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S)
    (hP : U42Pumpup S α) : False := by
  have hcard : Nat.card S = 1451520 := by
    rw [hLO ⟨.B 3 q, hv⟩ S ⟨e⟩]
    exact (congrArg (orderBC 3) hq).trans sp_orderBC_three_two
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv
    (cl_primePower_card_two hq).1 (le_refl 3) e
  exact false_of_pumpup_of_inner (cl_center_eq_bot_of_simple hn) hP
    (sp_mem_inner_of_statedModel hmodel hα hP.1) (by rw [hcard]; norm_num)

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
