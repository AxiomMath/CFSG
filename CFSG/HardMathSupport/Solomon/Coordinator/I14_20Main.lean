module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Open

theorem catalog_of_quasisimple {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K) (hK : CFSG.Open.IsKGroup K) :
    (∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a) ∧ IsCatalogGroup (K ⧸ Subgroup.center K) := by
  obtain ⟨hperf, hsimple⟩ := hq
  have hnab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hcomm : ∀ a b : K, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center K := by
      intro a b
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hab (a : K ⧸ Subgroup.center K) b]
      group
    have hle : commutator K ≤ Subgroup.center K := by
      rw [commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def]
      exact hcomm a b
    rw [hperf, top_le_iff] at hle
    have hall : ∀ q : K ⧸ Subgroup.center K, q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x => exact (QuotientGroup.eq_one_iff x).2 (hle ▸ Subgroup.mem_top x)
    have := hsimple
    obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
    exact hab ((hall a).trans (hall b).symm)
  refine ⟨hnab, ?_⟩
  have hnorm : ((Subgroup.center K).subgroupOf (⊤ : Subgroup K)).Normal :=
    Subgroup.Normal.subgroupOf inferInstance _
  have e : (↥(⊤ : Subgroup K) ⧸ (Subgroup.center K).subgroupOf (⊤ : Subgroup K)) ≃*
      (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf])
  have hs : IsSimpleGroup (↥(⊤ : Subgroup K) ⧸ (Subgroup.center K).subgroupOf (⊤ : Subgroup K)) :=
    e.isSimpleGroup_congr.2 hsimple
  have hna : ∃ a b : ↥(⊤ : Subgroup K) ⧸ (Subgroup.center K).subgroupOf (⊤ : Subgroup K),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨φ⟩⟩ := hK ⊤ (Subgroup.center K) le_top hs hna
  exact ⟨i, ⟨e.symm.trans φ⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
