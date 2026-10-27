module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.NormSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore
  CFSG.EvenSporadicStandard.HNRecog.HaradaLA

section Cert

variable
  (ι : Multiplicative V6 →* ↥P1408) (hι : ∀ v : V6, ι (Multiplicative.ofAdd v) = iotaFun v)

include hι

theorem fuse_normGens (v w : V6) (hv0 : v ≠ 0) (hvt : v ≠ tv) (hw0 : w ≠ 0) (hwt : w ≠ tv)
    (hl : lam v = lam w) (hq : qm v = qm w) :
    ∃ n ∈ wordSubgroupP normGens,
      n * ι (Multiplicative.ofAdd v) * n⁻¹ = ι (Multiplicative.ofAdd w) := by
  have hkv : codeOfVec v < 64 := codeOfVec_lt v
  have hkw : codeOfVec w < 64 := codeOfVec_lt w
  have hv0' : codeOfVec v ≠ 0 := fun h =>
    hv0 (codeOfVec_injective (by rw [h, codeOfVec_zero]))
  have hvt' : codeOfVec v ≠ 16 := fun h =>
    hvt (codeOfVec_injective (by rw [h, codeOfVec_tv]))
  have hw0' : codeOfVec w ≠ 0 := fun h =>
    hw0 (codeOfVec_injective (by rw [h, codeOfVec_zero]))
  have hwt' : codeOfVec w ≠ 16 := fun h =>
    hwt (codeOfVec_injective (by rw [h, codeOfVec_tv]))
  have htype' : typeIdx (codeOfVec v) = typeIdx (codeOfVec w) :=
    (typeIdx_codeOfVec_eq_iff v w).2 ⟨hl, hq⟩
  obtain ⟨n, hnH, hn_eq⟩ := aFacts.fuse _ hkv _ hkw hv0' hvt' hw0' hwt' htype'
  refine ⟨⟨n, wordSubgroup_le normGens hnH⟩, ?_, ?_⟩
  · rw [mem_wordSubgroupP]; exact hnH
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hι v, hι w]
    simp only [vecOfCode_codeOfVec] at hn_eq
    exact hn_eq

theorem fuse_A (v w : V6) (hv0 : v ≠ 0) (hvt : v ≠ tv) (hw0 : w ≠ 0) (hwt : w ≠ tv)
    (hl : lam v = lam w) (hq : qm v = qm w) :
    ∃ n ∈ normalizer (ι.range : Set ↥P1408),
      n * ι (Multiplicative.ofAdd v) * n⁻¹ = ι (Multiplicative.ofAdd w) := by
  obtain ⟨n, hn, heq⟩ := fuse_normGens ι hι v w hv0 hvt hw0 hwt hl hq
  exact ⟨n, wordSubgroupP_normGens_le_normalizer ι hι hn, heq⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
