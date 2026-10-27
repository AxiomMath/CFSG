module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG

theorem exists_simple_subgroup_le_fixed_of_injective {X Y : Type*} [Group X] [Group Y]
    [IsSimpleGroup Y] {p k : ℕ} (ι : Y →* X) (hι : Function.Injective ι) (θ : MulAut X)
    (hfix : ∀ y, θ (ι y) = ι y) (hrank : k ≤ pRank p Y) :
    ∃ S : Subgroup X, S ≤ Open.signalizerFixedSubgroup θ ∧ IsSimpleGroup S ∧
      k ≤ pRank p S := by
  let e : Y ≃* ι.range := MonoidHom.ofInjective hι
  refine ⟨ι.range, ?_, e.symm.isSimpleGroup, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hfix y
  · rw [← pRank_congr_of_mulEquiv e p]
    exact hrank

end CFSG
