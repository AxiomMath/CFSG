module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetAlgebra
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Index

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe v

variable {G : Type v} [Group G]

@[expose, instance_reducible] def cosetAmbientConjugation (Delta : Set G) :
    MulAction (Subgroup.normalizer Delta) G :=
  MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp (Subgroup.normalizer Delta).subtype)

@[expose] def cosetConjugationSet (Delta : Set G) :
    letI := cosetAmbientConjugation Delta
    SubMulAction (Subgroup.normalizer Delta) G := by
  letI := cosetAmbientConjugation Delta
  exact {
    carrier := Delta
    smul_mem' := fun n x hx => n.property x |>.mp hx }

@[expose, instance_reducible] def cosetNormalizerAction (Delta : Set G) :
    MulAction (Subgroup.normalizer Delta) Delta := by
  letI := cosetAmbientConjugation Delta
  exact (cosetConjugationSet Delta).mulAction

@[expose] def cosetNormalizerPerm (Delta : Set G) :
    Subgroup.normalizer Delta →* Equiv.Perm Delta := by
  letI := cosetNormalizerAction Delta
  exact MulAction.toPermHom (Subgroup.normalizer Delta) Delta

theorem cosetNormalizerPerm_apply (Delta : Set G)
    (n : Subgroup.normalizer Delta) (x : Delta) :
    ((cosetNormalizerPerm Delta n x : Delta) : G) =
      (n : G) * (x : G) * (n : G)⁻¹ := rfl

theorem cosetNormalizerPerm_ker_eq_entire_centralizer (Delta : Set G) :
    (cosetNormalizerPerm Delta).ker =
      (Subgroup.centralizer Delta).subgroupOf (Subgroup.normalizer Delta) := by
  ext n
  change cosetNormalizerPerm Delta n = 1 ↔ (n : G) ∈ Subgroup.centralizer Delta
  constructor
  · intro hn
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have heq := congrArg (fun e : Equiv.Perm Delta => ((e ⟨x, hx⟩ : Delta) : G)) hn
    change (n : G) * x * (n : G)⁻¹ = x at heq
    have hmul := congrArg (fun y : G => y * (n : G)) heq
    have hmul' : (n : G) * x = x * (n : G) := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
    exact hmul'.symm
  · intro hn
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (n : G) * (x : G) * (n : G)⁻¹ = (x : G)
    rw [← Subgroup.mem_centralizer_iff.mp hn (x : G) x.property]
    exact mul_inv_cancel_right (x : G) (n : G)

theorem cosetNormalizerPerm_ker_eq_closure_conjugation_ker (Delta : Set G) :
    (cosetNormalizerPerm Delta).ker = (cosetClosureConjugation Delta).ker := by
  rw [cosetNormalizerPerm_ker_eq_entire_centralizer,
    cosetClosureConjugation_ker_eq_entire_centralizer]

theorem cosetNormalizerPerm_ker_map_eq_entire_centralizer (Delta : Set G) :
    (cosetNormalizerPerm Delta).ker.map (Subgroup.normalizer Delta).subtype =
      Subgroup.centralizer Delta := by
  rw [cosetNormalizerPerm_ker_eq_entire_centralizer]
  exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer Delta)

@[expose] instance cosetNormalizerCentralizerNormal (Delta : Set G) :
    ((Subgroup.centralizer Delta).subgroupOf (Subgroup.normalizer Delta)).Normal := by
  rw [← cosetNormalizerPerm_ker_eq_entire_centralizer]
  infer_instance

@[expose] def cosetNormalizerQuotientEquivPermRange (Delta : Set G) :
    Subgroup.normalizer Delta ⧸
        (Subgroup.centralizer Delta).subgroupOf (Subgroup.normalizer Delta) ≃*
      (cosetNormalizerPerm Delta).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (cosetNormalizerPerm_ker_eq_entire_centralizer Delta).symm).trans
      (QuotientGroup.quotientKerEquivRange (cosetNormalizerPerm Delta))

theorem cosetNormalizer_centralizer_index_eq_perm_range_card (Delta : Set G) :
    (Subgroup.centralizer Delta).relIndex (Subgroup.normalizer Delta) =
      Nat.card (cosetNormalizerPerm Delta).range := by
  change ((Subgroup.centralizer Delta).subgroupOf (Subgroup.normalizer Delta)).index = _
  rw [← cosetNormalizerPerm_ker_eq_entire_centralizer, Subgroup.index_ker]

theorem cosetNormalizerAction_stabilizer (Delta : Set G) (x : Delta) :
    letI := cosetNormalizerAction Delta
    MulAction.stabilizer (Subgroup.normalizer Delta) x =
      (Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf (Subgroup.normalizer Delta) := by
  let := cosetNormalizerAction Delta
  ext n
  change n • x = x ↔ (n : G) ∈ Subgroup.centralizer ({(x : G)} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hn
    have heq := congrArg (fun y : Delta => (y : G)) hn
    change (n : G) * (x : G) * (n : G)⁻¹ = (x : G) at heq
    have hmul := congrArg (fun y : G => y * (n : G)) heq
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  · intro hn
    apply Subtype.ext
    change (n : G) * (x : G) * (n : G)⁻¹ = (x : G)
    rw [hn]
    exact mul_inv_cancel_right (x : G) (n : G)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
