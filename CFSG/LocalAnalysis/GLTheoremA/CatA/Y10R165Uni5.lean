module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni4

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open CFSG.LocalAnalysis.ComponentInitial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ℓ f p : ℕ} {h : UnitaryFieldData ℓ f K}
variable {B : V →ₛₗ[h.bar] V →ₗ[K] K}

theorem separatingLeft_domRestrict_orthogonalBilin {U : Submodule K V}
    (hrefl : B.IsRefl) (hBn : B.SeparatingLeft)
    (hc : IsCompl U (Submodule.orthogonalBilin B U)) :
    (B.domRestrict₁₂ (Submodule.orthogonalBilin B U)
      (Submodule.orthogonalBilin B U)).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_linear_nontrivial]
  rintro ⟨y, hyW⟩ hy
  have hy0 : (y : V) = 0 := by
    rw [LinearMap.separatingLeft_iff_linear_nontrivial] at hBn
    refine hBn y (LinearMap.ext fun v => ?_)
    obtain ⟨u, w, rfl⟩ := exists_coe_add_of_isCompl hc v
    have h1 : B y (w : V) = 0 := by
      have h := congrFun (congrArg DFunLike.coe hy) w
      simpa only [LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply] using h
    have h2 : B y (u : V) = 0 :=
      hrefl.eq_zero ((Submodule.mem_orthogonalBilin.mp hyW) u u.2)
    rw [map_add, h2, h1, add_zero]
    rfl
  exact Subtype.ext hy0

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
