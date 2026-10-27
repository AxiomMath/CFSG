module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalGraphFusion
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

theorem cosetNormalizerAction_isPretransitive (Delta : Set G)
    (htrans : ∀ s : G, s ∈ Delta → ∀ t : G, t ∈ Delta →
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem s (n : G) = t) :
    letI := cosetNormalizerAction Delta
    MulAction.IsPretransitive (Subgroup.normalizer Delta) Delta := by
  let := cosetNormalizerAction Delta
  constructor
  intro x y
  obtain ⟨n, hn⟩ := htrans x x.property y y.property
  refine ⟨n⁻¹, ?_⟩
  apply Subtype.ext
  change (n : G)⁻¹ * (x : G) * ((n : G)⁻¹)⁻¹ = (y : G)
  simpa only [rightConjugateElem, inv_inv] using hn

theorem cosetNormalizerAction_isTwoPretransitive (Delta : Set G) (u : G)
    (hu : u ∈ Delta)
    (htrans : ∀ s : G, s ∈ Delta → ∀ t : G, t ∈ Delta →
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem s (n : G) = t)
    (hstab : ∀ s : G, s ∈ Delta → s ≠ u → ∀ t : G, t ∈ Delta → t ≠ u →
      ∃ a : (Subgroup.normalizer Delta ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G),
        rightConjugateElem s (a : G) = t) :
    letI := cosetNormalizerAction Delta
    MulAction.IsMultiplyPretransitive (Subgroup.normalizer Delta) Delta 2 := by
  let := cosetNormalizerAction Delta
  let N := Subgroup.normalizer Delta
  let base : Delta := ⟨u, hu⟩
  have : MulAction.IsPretransitive N Delta :=
    cosetNormalizerAction_isPretransitive Delta htrans
  have hoff : MulAction.IsPretransitive (MulAction.stabilizer N base)
      (SubMulAction.ofStabilizer N base) := by
    constructor
    intro x y
    have hxu : ((x : Delta) : G) ≠ u := by
      intro heq
      exact x.property (Set.mem_singleton_iff.mpr (Subtype.ext heq))
    have hyu : ((y : Delta) : G) ≠ u := by
      intro heq
      exact y.property (Set.mem_singleton_iff.mpr (Subtype.ext heq))
    obtain ⟨a, ha⟩ := hstab ((x : Delta) : G) (x : Delta).property hxu
      ((y : Delta) : G) (y : Delta).property hyu
    let n : N := ⟨(a : G), a.property.1⟩
    have hn : n⁻¹ ∈ MulAction.stabilizer N base := by
      rw [cosetNormalizerAction_stabilizer]
      change (a : G)⁻¹ ∈ Subgroup.centralizer ({u} : Set G)
      exact (Subgroup.centralizer ({u} : Set G)).inv_mem a.property.2
    refine ⟨⟨n⁻¹, hn⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (a : G)⁻¹ * ((x : Delta) : G) * ((a : G)⁻¹)⁻¹ = ((y : Delta) : G)
    simpa only [rightConjugateElem, inv_inv] using ha
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := N) (α := Delta) (n := 1) (a := base)).mpr
      (MulAction.is_one_pretransitive_iff.mpr hoff)

theorem cosetNormalizer_every_centralizer_index (Delta : Set G)
    (htrans : ∀ s : G, s ∈ Delta → ∀ t : G, t ∈ Delta →
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem s (n : G) = t)
    (x : Delta) :
    (Subgroup.centralizer ({(x : G)} : Set G)).relIndex (Subgroup.normalizer Delta) =
      Nat.card Delta := by
  let := cosetNormalizerAction Delta
  have := cosetNormalizerAction_isPretransitive Delta htrans
  change ((Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf
    (Subgroup.normalizer Delta)).index = _
  rw [← cosetNormalizerAction_stabilizer]
  exact MulAction.index_stabilizer_of_transitive (Subgroup.normalizer Delta) x

theorem cosetNormalizerPerm_range_isPretransitive (Delta : Set G)
    (htrans : ∀ s : G, s ∈ Delta → ∀ t : G, t ∈ Delta →
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem s (n : G) = t) :
    MulAction.IsPretransitive (cosetNormalizerPerm Delta).range Delta := by
  let := cosetNormalizerAction Delta
  have h := cosetNormalizerAction_isPretransitive Delta htrans
  constructor
  intro x y
  obtain ⟨n, hn⟩ := h.exists_smul_eq x y
  refine ⟨⟨cosetNormalizerPerm Delta n, n, rfl⟩, ?_⟩
  exact hn

theorem cosetNormalizerPerm_range_isTwoPretransitive (Delta : Set G) (u : G)
    (hu : u ∈ Delta)
    (htrans : ∀ s : G, s ∈ Delta → ∀ t : G, t ∈ Delta →
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem s (n : G) = t)
    (hstab : ∀ s : G, s ∈ Delta → s ≠ u → ∀ t : G, t ∈ Delta → t ≠ u →
      ∃ a : (Subgroup.normalizer Delta ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G),
        rightConjugateElem s (a : G) = t) :
    MulAction.IsMultiplyPretransitive (cosetNormalizerPerm Delta).range Delta 2 := by
  let := cosetNormalizerAction Delta
  have h := cosetNormalizerAction_isTwoPretransitive Delta u hu htrans hstab
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨n, hn, hn'⟩ := MulAction.is_two_pretransitive_iff.mp h hab hcd
  exact ⟨⟨cosetNormalizerPerm Delta n, n, rfl⟩, hn, hn'⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
