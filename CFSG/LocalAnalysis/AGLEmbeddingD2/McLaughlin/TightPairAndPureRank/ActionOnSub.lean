module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type*} [Group G]

@[expose] def actHom (N Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (N : Set G)) :
    ↥Y →* MulAut ↥N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion hY)

theorem actHom_apply_coe (N Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (y : ↥Y) (n : ↥N) : ((actHom N Y hY y n : ↥N) : G) = (y : G) * n * (y : G)⁻¹ := rfl

theorem actHom_eq_one_iff (N Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (y : ↥Y) : actHom N Y hY y = 1 ↔ (y : G) ∈ Subgroup.centralizer (N : Set G) := by
  constructor
  · intro h n hn
    have := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : G)) h
    simp only [actHom_apply_coe] at this
    have h2 : (y : G) * n * (y : G)⁻¹ = n := this
    calc n * (y : G) = (y : G) * n * (y : G)⁻¹ * (y : G) := by rw [h2]
      _ = (y : G) * n := by group
  · intro h
    ext n
    rw [actHom_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp h n n.2
    calc (y : G) * n * (y : G)⁻¹ = (n * (y : G)) * (y : G)⁻¹ := by rw [← this]
      _ = n := by group

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
