module

public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

variable {G : Type*} [Group G]

theorem normal_two_extension_quotient (N B : Subgroup G) [N.Normal]
    (hcover : N ⊔ B = ⊤) (hB : IsPGroup 2 B) : IsPGroup 2 (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hsurj : Function.Surjective (q.comp B.subtype) := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x
    have hmem : g ∈ N ⊔ B := hcover ▸ Subgroup.mem_top g
    obtain ⟨n, hn, b, hb, heq⟩ :=
      NormalizedProduct.coordinates N B Subgroup.le_normalizer_of_normal g hmem
    refine ⟨⟨b, hb⟩, ?_⟩
    change q b = x
    have hnq : q n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    calc
      q b = q (n * b) := by
        rw [map_mul, hnq, one_mul]
      _ = x := by rw [heq]; exact hg
  exact hB.of_surjective (q.comp B.subtype) hsurj

variable [Finite G]

end CFSG.ComponentClassification.AschbacherComponentInvolution
