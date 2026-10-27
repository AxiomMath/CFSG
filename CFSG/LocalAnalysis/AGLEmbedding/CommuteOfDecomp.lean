module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

theorem commute_of_mem_of_decomp {G : Type*} [Group G] {R T : Subgroup G} {z : G}
    (hT : IsMulCommutative T) (hTR : T ≤ R) (hRz : ∀ r ∈ R, r * z = z * r)
    (hdec : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i) {a b : G} (ha : a ∈ R) (hb : b ∈ R) :
    a * b = b * a := by
  obtain ⟨s, hs, i, rfl⟩ := hdec a ha
  obtain ⟨t, ht, j, rfl⟩ := hdec b hb
  have hst : s * t = t * s := by
    have := hT.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩
    exact congrArg Subtype.val this
  calc s * z ^ i * (t * z ^ j) = s * (z ^ i * t) * z ^ j := by group
    _ = s * (t * z ^ i) * z ^ j := by rw [(Commute.pow_left (hRz t (hTR ht)).symm i).eq]
    _ = (s * t) * (z ^ i * z ^ j) := by group
    _ = (t * s) * (z ^ j * z ^ i) := by rw [hst, ← pow_add, ← pow_add, add_comm]
    _ = t * (s * z ^ j) * z ^ i := by group
    _ = t * (z ^ j * s) * z ^ i := by rw [(Commute.pow_left (hRz s (hTR hs)).symm j).eq]
    _ = t * z ^ j * (s * z ^ i) := by group

end CFSG.AGLEmbedding
